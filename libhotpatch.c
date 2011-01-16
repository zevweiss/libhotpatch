/*
 * (C) Zev Weiss 2011
 *
 * libhotpatch is licensed under the GPLv2.
 */

#define _GNU_SOURCE
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <dlfcn.h>
#include <limits.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>

#include <libelf.h>
#include <gelf.h>

#include "udis86/install/include/udis86.h"

static void libhotpatch_init(void) __attribute__((constructor));
static void libhotpatch_fini(void) __attribute__((destructor));

static FILE* pllog = NULL;

#define BREAK() __asm__ __volatile__("int3")

static void* memdup(void* orig, size_t len)
{
	void* new = malloc(len);
	assert(new);
	memcpy(new,orig,len);
	return new;
}

/* check if any of instruction's operands are RIP-relative memory operands */
static inline int inst_opnd_rip_rel(ud_t* ud)
{
	int i;
	for (i = 0; i < 3; i++) {
		if (ud->operand[i].type == UD_OP_MEM
		    && ud->operand[i].base == UD_R_RIP)
			return 1;
	}
	return 0;
}

/* determine if the most recently disassembled instruction is relocatable */
static int udinst_relocatable(ud_t* ud)
{
	switch (ud->mnemonic) {

	case UD_Iret:
	case UD_Ileave:
	case UD_Inop:
	case UD_Icdqe:
		return 1;

	case UD_Itest:
	case UD_Icmp:
	case UD_Ilea:
	case UD_Imov:
	case UD_Imovsxd:
	case UD_Iand:
	case UD_Idec:
	case UD_Iadd:
	case UD_Isub:
	case UD_Ixor:
	case UD_Ior:
	case UD_Ixchg:
	case UD_Icmpxchg:
	case UD_Ineg:
	case UD_Ipop:
	case UD_Isar:
	case UD_Ipush:
		return !inst_opnd_rip_rel(ud);

	case UD_Ijmp:
	case UD_Icall:
		if (ud->operand[0].type == UD_OP_JIMM)
			return 0;
		else
			abort();

	case UD_Ijz:
	case UD_Ijnz:
	case UD_Ijo:
	case UD_Ijp:
	case UD_Ijs:
	case UD_Ija:
	case UD_Ijae:
	case UD_Ijb:
	case UD_Ijbe:
	case UD_Ijg:
	case UD_Ijge:
	case UD_Ijl:
	case UD_Ijle:
	case UD_Ijno:
	case UD_Ijnp:
	case UD_Ijns:
		return 0;

	default:
		fprintf(pllog,"NYI: relocatability of %s (%i bytes @ pc=%lx)\n",
		        ud_insn_asm(ud),ud_insn_len(ud),ud->pc-ud_insn_len(ud));
		abort();
	}
}

struct inst {
	void* pc;
	uint8_t* bytes;
	uint8_t len;
};

static void init_udinst_pc(ud_t* ud, void* start, size_t len, uintptr_t pc)
{
	ud_init(ud);
	ud_set_input_buffer(ud,start,len);
	ud_set_mode(ud,64);
	ud_set_syntax(ud,UD_SYN_ATT);
	ud_set_pc(ud,pc);
}

static void init_udinst(ud_t* ud, void* start, size_t len)
{
	init_udinst_pc(ud,start,len,(uintptr_t)start);
}

static void inst_to_ud(const struct inst* inst, ud_t* ud)
{
	init_udinst_pc(ud,inst->bytes,inst->len,(uintptr_t)inst->pc);
	ud_disassemble(ud);
}

static int inst_relocatable(const struct inst* inst)
{
	ud_t ud;
	inst_to_ud(inst,&ud);
	return udinst_relocatable(&ud);
}

static void dup_ud_inst(ud_t* ud, struct inst* inst)
{
	inst->len = ud_insn_len(ud);
	inst->bytes = malloc(inst->len);
	assert(inst->bytes);
	memcpy(inst->bytes,ud_insn_ptr(ud),inst->len);
	inst->pc = (void*)((uintptr_t)ud->pc - (uintptr_t)inst->len);
}

/*
 * An mmap area used for hotpatch trampolines.
 */
struct trampmap {
	/* trampoline map base address */
	void* base;

	/* size of the trampoline map and how much of it we've
	 * currently used */
	size_t size,used;

	/* which original (program text) map the trampolines in this
	 * region bounce to/from */
	unsigned int mapnum;
};

/* Initial size we'll aim at for trampoline maps */
#define TRAMPMAP_MIN_SIZE (64*1024)
#define MIN_TRAMP_SIZE 64

static struct trampmap* trampmaps = NULL;
static unsigned int ntrampmaps = 0;

/*
 * int3 used as a filler byte in trampoline areas so we'll trap in case
 * anything goes unexpectedly out of bounds.
 */
#define X86OP_INT3 0xcc
#define X86OP_JMP_REL32 0xe9
#define X86OP_JMP_REL8 0xeb
#define X86OP_CALL_REL32 0xe8
#define X86OP_JCC_REL32 0x0f80
#define X86OP_JCC_REL8 0x70
#define X86OP_NOP 0x90

#define X86_MAX_INST_LEN 15

#define JMP_REL32_NBYTES 5
#define JMP_REL8_NBYTES 2
#define JCC_REL32_NBYTES 6
#define JCC_REL8_NBYTES 2
#define SYSCALL_NBYTES 2

/* generate a jmp-rel8 at org to dst */
static void genjmprel8(void* org, const void* dst)
{
	int64_t ofst = dst - (org+JMP_REL8_NBYTES);
	assert(ofst <= INT8_MAX && ofst >= INT8_MIN);
	*(uint8_t*)org = X86OP_JMP_REL8;
	*(int8_t*)(org+1) = (int8_t)ofst;
}

/* generate a jmp-rel32 at org to dst */
static void genjmprel32(void* org, const void* dst)
{
	int64_t ofst = dst - (org+JMP_REL32_NBYTES);
	assert(ofst <= INT32_MAX && ofst >= INT32_MIN);
	*(uint8_t*)org = X86OP_JMP_REL32;
	*(int32_t*)(org+1) = (int32_t)ofst;
}

/*
 * "Translate" an instruction for relocation from orig->pc to new->pc
 * (which must be filled in by the caller, new's other fields will be
 * filled in by translate_inst()).
 */
static void translate_inst(const struct inst* orig, struct inst* new)
{
	ud_t oud;
	int64_t origofst,newofst;
	uintptr_t targ;
	uint16_t jccop;
	int ofstbyte;
	int jmp_is_call;

	inst_to_ud(orig,&oud);
	if (udinst_relocatable(&oud)) {
		new->bytes = memdup(orig->bytes,orig->len);
		new->len = orig->len;
		return;
	}
	switch (oud.mnemonic) {
	case UD_Ijz:
	case UD_Ijnz:
	case UD_Ijo:
	case UD_Ijp:
	case UD_Ijs:
	case UD_Ija:
	case UD_Ijae:
	case UD_Ijb:
	case UD_Ijbe:
	case UD_Ijg:
	case UD_Ijge:
	case UD_Ijl:
	case UD_Ijle:
	case UD_Ijno:
	case UD_Ijnp:
	case UD_Ijns:
		assert(oud.operand[0].type == UD_OP_JIMM);
		switch (oud.operand[0].size) {
		case 8:
			origofst = oud.operand[0].lval.sbyte;
			if ((orig->bytes[0] & 0xf0) == 0xe0) {
				assert(orig->bytes[0] == 0xe3);
				fprintf(pllog,"stupid-ass x86 jcx NYI\n");
				abort();
			}
			assert((orig->bytes[0] & 0xf0) == 0x70);
			jccop = X86OP_JCC_REL32 | (orig->bytes[0] & 0x0f);
			break;
		case 32:
			origofst = oud.operand[0].lval.sdword;
			jccop = (orig->bytes[0] << 8) | orig->bytes[1];
			break;
		default:
			fprintf(pllog,"unknown jcc operand size (%i)\n",
			        oud.operand[0].size);
			abort();
		}

		targ = (uintptr_t)orig->pc + orig->len + origofst;
		newofst = (int64_t)targ - ((int64_t)new->pc + JCC_REL32_NBYTES);
		if (newofst > INT32_MAX || newofst < INT32_MIN) {
			fprintf(pllog,"jcc-rel32 can't reach target\n");
			abort();
		}

		new->len = JCC_REL32_NBYTES;
		new->bytes = malloc(JCC_REL32_NBYTES);
		assert(new->bytes);
		new->bytes[0] = (uint8_t)(jccop >> 8);
		new->bytes[1] = (uint8_t)(jccop & 0xff);
		*(int32_t*)(&new->bytes[2]) = newofst;

		return;

	case UD_Icall:
	case UD_Ijmp:
		jmp_is_call = oud.mnemonic == UD_Icall;
		if (oud.operand[0].type != UD_OP_JIMM) {
			fprintf(pllog,"translation NYI for %s\n",ud_insn_asm(&oud));
			abort();
		}
		switch (oud.operand[0].size) {
		case 8:
			origofst = oud.operand[0].lval.sbyte;
			break;
		case 32:
			origofst = oud.operand[0].lval.sdword;
			break;
		default:
			fprintf(pllog,"unknown jmp operand size (%i)\n",
			        oud.operand[0].size);
			abort();
		}
		targ = (uintptr_t)orig->pc + orig->len + origofst;
		newofst = (int64_t)targ - ((int64_t)new->pc + JMP_REL32_NBYTES);
		if (newofst > INT32_MAX || newofst < INT32_MIN) {
			fprintf(pllog,"jmp-rel32 can't reach target\n");
			abort();
		}

		new->len = JMP_REL32_NBYTES;
		new->bytes = malloc(JMP_REL32_NBYTES);
		assert(new->bytes);
		new->bytes[0] = jmp_is_call ? X86OP_CALL_REL32 : X86OP_JMP_REL32;
		*(int32_t*)(&new->bytes[1]) = (int32_t)newofst;

		return;

	case UD_Imov:
		if (oud.operand[0].type == UD_OP_REG) {
			assert(oud.operand[1].type == UD_OP_MEM);
			assert(oud.operand[1].base == UD_R_RIP);
			assert(oud.operand[1].offset == 32);
			assert(oud.operand[1].scale == 0);
			assert(oud.operand[1].index == UD_NONE);
			/* just copy & overwrite the offset */
			new->bytes = memdup(orig->bytes,orig->len);
			new->len = orig->len;
			targ = (uintptr_t)orig->pc + orig->len + oud.operand[1].lval.sdword;
			newofst = (int64_t)targ - ((int64_t)new->pc + new->len);
			if (newofst > INT32_MAX || newofst < INT32_MIN) {
				fprintf(pllog,"rip-relative mov can't reach target\n");
				abort();
			}

			*(int32_t*)(&new->bytes[3]) = (int32_t)newofst;
		} else {
			assert(oud.operand[0].type == UD_OP_MEM);
			assert(oud.operand[0].base == UD_R_RIP);
			assert(oud.operand[0].offset == 32);
			assert(oud.operand[0].scale == 0);
			assert(oud.operand[0].index == UD_NONE);

			/* again, just copying and overwriting, but
			 * the offsets are in differing places */
			new->bytes = memdup(orig->bytes,orig->len);
			new->len = orig->len;
			targ = (uintptr_t)orig->pc + orig->len + oud.operand[0].lval.sdword;
			newofst = (int64_t)targ - ((int64_t)new->pc + new->len);
			if (newofst > INT32_MAX || newofst < INT32_MIN) {
				fprintf(pllog,"rip-relative mov can't reach target\n");
				abort();
			}

			if (oud.operand[1].type == UD_OP_IMM) {
				assert(oud.operand[1].size == 32
				       || oud.operand[1].size == 8);
				ofstbyte = 2;
			} else if (oud.operand[1].type == UD_OP_REG) {
				assert(oud.operand[1].size == 64);
				ofstbyte = 3;
			} else {
				fprintf(pllog,"unhandled mov type: %s\t%s\n",
				        ud_insn_hex(&oud),ud_insn_asm(&oud));
				abort();
			}

			*(int32_t*)(&new->bytes[ofstbyte]) = (int32_t)newofst;
		}
		return;

	case UD_Ilea:
		/* copy & overwrite offset */
		assert(oud.operand[0].type == UD_OP_REG);
		assert(oud.operand[0].size == 64);
		assert(oud.operand[1].type == UD_OP_MEM);
		assert(oud.operand[1].base == UD_R_RIP);
		assert(oud.operand[1].offset == 32);
		assert(oud.operand[1].scale == 0);

		new->bytes = memdup(orig->bytes,orig->len);
		new->len = orig->len;
		targ = (uintptr_t)orig->pc + orig->len + oud.operand[1].lval.sdword;
		newofst = (int64_t)targ - ((int64_t)new->pc + new->len);
		if (newofst > INT32_MAX || newofst < INT32_MIN) {
			fprintf(pllog,"rip-relative lea can't reach target\n");
			abort();
		}
		*(int32_t*)(&new->bytes[3]) = (int32_t)newofst;
		return;

	default:
		fprintf(pllog,"new translation required: %s\n",ud_insn_asm(&oud));
		abort();
	}
}

/*
 * Relocate 'numinsts' instructions to address 'to', using no more
 * than 'maxlen' bytes.
 */
static size_t translate_insts(const struct inst* src, int numinsts,
                              void* to, size_t maxlen)
{
	int i;
	struct inst trans;
	size_t len = 0;
	uint8_t* iptr = to;

	for (i = 0; i < numinsts; i++) {
		trans.pc = iptr;
		translate_inst(src+i,&trans);
		if (len + trans.len > maxlen) {
			fprintf(pllog,"code overflow from %p\n",to);
			abort();
		}
		iptr = mempcpy(iptr,trans.bytes,trans.len);
		len += trans.len;
	}

	return len;
}

#define TRAMPFUNC_ALIGN 8

/*
 * Generate a trampoline function, return its address
 */
static void* gentramp(const struct inst* orig, const struct inst* succs,
                      int nsuccs, struct trampmap* tm, void* retaddr)
{
	uint8_t* iptr;
	void* funcaddr;
	size_t added;

	/* starting address of the trampoline */
	funcaddr = iptr = tm->base + tm->used;

	assert((uintptr_t)iptr % TRAMPFUNC_ALIGN == 0);

	/* for starters we'll just do a no-op trampoline */
	if (tm->used + orig->len > tm->size) {
		fprintf(pllog,"trampoline area overflow\n");
		abort();
	}
	iptr = mempcpy(iptr,orig->bytes,orig->len);
	tm->used += orig->len;

	/* relocate instructions to the trampoline */
	added = translate_insts(succs,nsuccs,iptr,tm->size - tm->used);
	iptr += added;
	tm->used += added;

	/* and add the return jump */
	genjmprel32(iptr,retaddr);
	tm->used += JMP_REL32_NBYTES;
	iptr += JMP_REL32_NBYTES;

	/* pad out to an aligned boundary */
	while ((uintptr_t)iptr % TRAMPFUNC_ALIGN) {
		*iptr++ = X86OP_INT3;
		tm->used++;
	}

	return funcaddr;
}

struct scratchbuf {
	void* start;
	size_t len;
	uint8_t fallthrough;
};

static struct scratchbuf* nopbufs = NULL;
static unsigned int nnopbufs = 0;
static unsigned int allocnopbufs = 0;

static void** syscalls = NULL;
static unsigned int nsyscalls = 0;

struct clobberpatch {
	void* start;
	uint8_t bytes;
};

static struct clobberpatch* clobberpatches = NULL;
static unsigned int nclobberpatches = 0;

/* static struct scratchbuf* int3bufs = NULL; */
/* static unsigned int nint3bufs = 0; */

static void new_nopbuf(void* start, size_t len, uint8_t fallthrough)
{
	if (nnopbufs == allocnopbufs) {
		allocnopbufs += 1024;
		nopbufs = realloc(nopbufs,sizeof(*nopbufs)*allocnopbufs);
		assert(nopbufs);
	}
	nopbufs[nnopbufs] = (struct scratchbuf) {
		.start = start,
		.len = len,
		.fallthrough = fallthrough,
	};
	nnopbufs++;
}

static void new_syscall(void* addr)
{
	syscalls = realloc(syscalls,sizeof(void*)*++nsyscalls);
	assert(syscalls);
	syscalls[nsyscalls-1] = addr;
}

static  void new_clobberpatch(void* start, uint8_t bytes)
{
	clobberpatches = realloc(clobberpatches,sizeof(*clobberpatches)*++nclobberpatches);
	assert(clobberpatches);
	clobberpatches[nclobberpatches-1] = (struct clobberpatch) {
		start = start,
		bytes = bytes,
	};
}

/*
 * Predicate: whether a jmp-rel8 at start can reach dest
 */
static inline int within_rel8(const void* start, const void* dest)
{
	const void* relpt = start + JMP_REL8_NBYTES;
	int64_t ofst = dest - relpt;
	return ofst <= INT8_MAX && ofst >= INT8_MIN;
}

/* where in the buffer we'll jump to, accounting for patch-branch at
 * the start of fallthrough bufs */
static inline void* scratchbuf_dest(const struct scratchbuf* sb)
{
	if (sb->fallthrough)
		return sb->start + JMP_REL8_NBYTES;
	else
		return sb->start;
}

/*
 * For use with bsearch().
 * FIXME: could check for bufs we can reach the end of, but not the beginning.
 */
static int bufsearch_compar(const void* startpt, const void* scratchbuf)
{
	const struct scratchbuf* buf = scratchbuf;
	const void* dst = scratchbuf_dest(buf);

	if (!within_rel8(startpt,dst)) {
		if (startpt < dst)
			return -1;
		else if (startpt > dst)
			return 1;
		else
			abort();
	} else
		return 0;
}

/* For use with qsort when we add nopbufs post-scanpass */
static int scratchbuf_cmp(const void* va, const void* vb)
{
	const struct scratchbuf* a = va;
	const struct scratchbuf* b = vb;

	if (a->start < b->start) {
		assert(a->start + a->len < b->start);
		return -1;
	} else if (b->start < a->start) {
		assert(b->start + b->len < a->start);
		return 1;
	}

	/* I believe we should never have two overlapping nopbufs */
	abort();
}

static inline int scratchbuf_fits_jmprel32(struct scratchbuf* sb)
{
	if (sb->fallthrough)
		/* jmp-rel32 to go where we want and a jmp-rel8 to
		 * jump over the inserted jmp-rel32 */
		return sb->len >= (JMP_REL32_NBYTES + JMP_REL8_NBYTES);
	else
		/* if no fallthrough, don't need to jump-over jmp */
		return sb->len >= JMP_REL32_NBYTES;
}

static inline int scratchbuf_usable(const struct scratchbuf* sb)
{
	if (!sb->fallthrough)
		return sb->len >= JMP_REL8_NBYTES;
	else
		return sb->len >= (JMP_REL8_NBYTES + JMP_REL8_NBYTES);
}

static inline int can_link(const struct scratchbuf* from, const struct scratchbuf* to)
{
	if (!scratchbuf_usable(from))
		return 0;
	return within_rel8(scratchbuf_dest(from),scratchbuf_dest(to));
}

static inline struct scratchbuf* next_scratchbuf(struct scratchbuf* sb)
{
	struct scratchbuf* i;
	for (i = sb+1; i < nopbufs+nnopbufs; i++) {
		if (scratchbuf_usable(i))
			return i;
	}
	return NULL;
}

static inline struct scratchbuf* prev_scratchbuf(struct scratchbuf* sb)
{
	struct scratchbuf* i;
	for (i = sb-1; i >= nopbufs; i--) {
		if (scratchbuf_usable(i))
			return i;
	}
	return NULL;
}

/*
 * See if there's a path through any scratchbufs we've found to one
 * that's big enough to fit a jmp-rel32.
 *
 * If found, returns the address of the first one in the chain, else
 * NULL.  Caller can scan in that direction until it finds a
 * sufficiently large scratchbuf.
 */
static struct scratchbuf* find_scratchpath(void* startpt)
{
	struct scratchbuf* firstfound;
	struct scratchbuf* iter;
	struct scratchbuf* next;
	struct scratchbuf* firststep;

	firstfound = bsearch(startpt,nopbufs,nnopbufs,
	                     sizeof(*nopbufs),bufsearch_compar);

	/* check if any were reachable */
	if (!firstfound)
		return NULL;

	/* first try to go forward */
	iter = firstfound;
	/* skipping over any unusable ones */
	while (!scratchbuf_usable(iter))
		iter = next_scratchbuf(iter);
	if (within_rel8(startpt,scratchbuf_dest(iter))) {
		firststep = iter;
		for (;;) {
			next = next_scratchbuf(iter);
			/* if we've reached a usable one, cool */
			if (scratchbuf_fits_jmprel32(iter)) {
				if (within_rel8(startpt,scratchbuf_dest(iter)))
					return iter;
				if (((iter->start < firststep->start)
				     && (firststep->start < startpt))
				    || ((iter->start > firststep->start)
				        && (firststep->start > startpt)))
					return firststep;
				/* I think that should cover it? If not, blow up. */
				abort();
			}

			/* give up if we've reached the end of the scratchbuf
			 * array or we can't reach the next one */
			if (!next
			    || (!can_link(iter,next)
			        && !within_rel8(startpt,scratchbuf_dest(next))))
				break;

			/* otherwise we'll move on to the next one, but first
			 * check if we're about to cross startpt -- if so,
			 * adjust firststep accordingly */
			if (next->start > startpt && iter->start < startpt)
				firststep = next;

			iter = next;
		}
	}

	/* if we get here, we didn't find anything going forward.  reinitialize. */
	iter = firstfound;
	/* again, skipping over unused ones */
	while (!scratchbuf_usable(iter))
		iter = prev_scratchbuf(iter);
	if (within_rel8(startpt,scratchbuf_dest(iter))) {
		firststep = iter;
		/* similar to above, but searching backward */
		for (;;) {
			next = prev_scratchbuf(iter);
			/* if we've reach a usable one, cool */
			if (scratchbuf_fits_jmprel32(iter)) {
				if (within_rel8(startpt,scratchbuf_dest(iter)))
					return iter;
				if (((iter->start < firststep->start)
				     && (firststep->start < startpt))
				    || ((iter->start > firststep->start)
				        && (firststep->start > startpt)))
					return firststep;
				/* I think that should cover it?  If not, blow up. */
				abort();
			}

			/* give up if we've reach the end of the scratchbuf
			 * array or we can't reach the next one. */
			if (!next
			    || (!can_link(iter,next)
			        && !within_rel8(startpt,scratchbuf_dest(next))))
				break;

			/* otherwise we'll move on to the next one, but first
			 * check to see if we're about to cross startpt -- if
			 * so, adjust firststep accordingly */
			if (next->start < startpt && iter->start > startpt)
				firststep = next;

			iter = next;
		}
	}

	/* if we get here, couldn't find anything */
	return NULL;
}

static void patch_jmpchain(void* origin, struct scratchbuf* firstlink, void* dest)
{
	ud_t ud;
	uint8_t orig_bytes[16];
	void* org;
	struct scratchbuf* link;
	struct scratchbuf* prevlink;
	struct scratchbuf* (*nextbuf)(struct scratchbuf*);
	struct inst originst = {
		.bytes = orig_bytes,
		.len = sizeof(orig_bytes),
		.pc = origin,
	};

	memcpy(orig_bytes,origin,sizeof(orig_bytes));
	inst_to_ud(&originst,&ud);

	if (firstlink->start > origin)
		nextbuf = next_scratchbuf;
	else
		nextbuf = prev_scratchbuf;

	prevlink = NULL;
	link = firstlink;
	org = origin;
	for (;;) {
		/* check if we can use this as the final link */
		if (link->len >= JMP_REL32_NBYTES + JMP_REL8_NBYTES
		    || (!link->fallthrough && link->len >= JMP_REL32_NBYTES)) {
			if (link->fallthrough) {
				/* short jmp over the rest of the buffer */
				genjmprel8(link->start,
				           link->start+link->len);
				/* after that insertion, fallthrough bufs no longer are */
				link->fallthrough = 0;
				link->start += JMP_REL8_NBYTES;
				link->len -= JMP_REL8_NBYTES;
			}
			genjmprel8(org,link->start);
			if (prevlink) {
				prevlink->start += JMP_REL8_NBYTES;
				prevlink->len -= JMP_REL8_NBYTES;
			}

			genjmprel32(link->start,dest);
			link->start += JMP_REL32_NBYTES;
			link->len -= JMP_REL32_NBYTES;
			assert(link->len >= 0);

			/* make sure we don't leave any partial-nops lying around */
			memset(link->start,X86OP_NOP,link->len);
			break;
		} else {
			if (link->fallthrough) {
				/* short jmp over the rest of the buffer */
				genjmprel8(link->start,
				           link->start+link->len);
				/* after that insertion, fallthrough bufs no longer are */
				link->fallthrough = 0;
				link->start += JMP_REL8_NBYTES;
				link->len -= JMP_REL8_NBYTES;
			}

			assert(link->len >= JMP_REL8_NBYTES);

			/* don't leave any partial-nops lying around */
			memset(link->start,X86OP_NOP,link->len);

			genjmprel8(org,link->start);
			if (prevlink) {
				prevlink->start += JMP_REL8_NBYTES;
				prevlink->len -= JMP_REL8_NBYTES;
			}

			org = link->start;
			prevlink = link;
			link = nextbuf(link);
		}
	}
}

/* For use with bsearch */
static int jmpcheck_clobberpatch_bscmp(const void* k, const void* vcp)
{
	const struct clobberpatch* cp = vcp;

	/* It's ok for jmp dest to be at the syscall */
	if (k <= cp->start)
		return -1;

	if (k >= cp->start + cp->bytes)
		return 1;

	return 0;
}

/* Get the offset (into the instruction) at which a jump's displacement is found */
static uint8_t get_jmpdisp_ofst(ud_t* ud)
{
	/* first check if this is something we're prepared to handle */
	assert(ud->operand[0].type == UD_OP_JIMM);
	assert(ud->operand[0].size == 8 || ud->operand[0].size == 32);

	switch (ud->mnemonic) {
	case UD_Ijmp:
		if (ud->operand[0].size == 8) {
			BREAK(); /* FIXME: why is this here? */
			return 1;
		} else {
			return 1;
		}
	case UD_Ijo:
	case UD_Ijno:
	case UD_Ijb:
	case UD_Ijae:
	case UD_Ijz:
	case UD_Ijnz:
	case UD_Ijbe:
	case UD_Ija:
	case UD_Ijs:
	case UD_Ijns:
	case UD_Ijp:
	case UD_Ijnp:
	case UD_Ijl:
	case UD_Ijge:
	case UD_Ijle:
	case UD_Ijg:
	case UD_Ijcxz:
	case UD_Ijecxz:
	case UD_Ijrcxz:
		if (ud->operand[0].size == 8) {
			BREAK(); /* FIXME: why is this here? */
			return 2;
		} else {
			return 2;
		}
	default:
		abort();
	}
}

static void* get_jmptarg(ud_t* ud)
{
	int64_t ofst;
	assert(ud->operand[0].type == UD_OP_JIMM);
	switch (ud->operand[0].size) {
	case 8:
		ofst = ud->operand[0].lval.sbyte;
		break;
	case 32:
		ofst = ud->operand[0].lval.sdword;
		break;
	default:
		abort();
	}

	return (void*)ud->pc + ofst;
}

#define CLOBBER_SHADOW_BUFLEN 16

/*
 * Figures out which instructions in a clobber-patch shadow will have
 * to be duplicated (and potentially translated) in its trampoline.
 */
static void* find_clobber_succs(void* victim, int bytes_needed,
                                struct inst* succs, int* nsuccs, int* succbytes)
{
	ud_t ud;
	int shadow,i,bytes;

	init_udinst(&ud,victim,X86_MAX_INST_LEN+CLOBBER_SHADOW_BUFLEN);

	ud_disassemble(&ud);
	assert(ud_insn_len(&ud) < bytes_needed);
	shadow = bytes_needed - ud_insn_len(&ud);
	for (i = 0, bytes = 0; i < shadow && bytes < shadow; i++) {
		ud_disassemble(&ud);
		dup_ud_inst(&ud,&succs[i]);
		bytes += succs[i].len;
	}
	assert(bytes >= shadow);

	*nsuccs = i;
	*succbytes = bytes;
	return (void*)ud.pc;
}

static size_t retarget_branch(void* loc, void* targ)
{
	int64_t disp;
	ud_t ud;
	uint8_t cond;
	uint16_t opcode;
	int fits_rel8,is_rel32;
	size_t len;

	init_udinst(&ud,loc,X86_MAX_INST_LEN);
	ud_disassemble(&ud);

	fits_rel8 = within_rel8(loc,targ);
	is_rel32 = ud.operand[0].size == 32;

	switch (ud.mnemonic) {
	case UD_Ijo:
	case UD_Ijno:
	case UD_Ijb:
	case UD_Ijae:
	case UD_Ijz:
	case UD_Ijnz:
	case UD_Ijbe:
	case UD_Ija:
	case UD_Ijs:
	case UD_Ijns:
	case UD_Ijp:
	case UD_Ijnp:
	case UD_Ijl:
	case UD_Ijge:
	case UD_Ijle:
	case UD_Ijg:
		/* jcc */
		disp = targ - loc - (fits_rel8 ? JCC_REL8_NBYTES : JCC_REL32_NBYTES);
		cond = ((uint8_t*)loc)[is_rel32 ? 1 : 0] & 0x0F;
		if (fits_rel8) {
			*((uint8_t*)loc) = (uint8_t)(X86OP_JCC_REL8 | cond);
			assert(disp <= INT8_MAX && disp >= INT8_MIN);
			*((int8_t*)loc + 1) = (int8_t)disp;
			len = JCC_REL8_NBYTES;
		} else {
			opcode = (X86OP_JCC_REL32 | cond);
			((uint8_t*)loc)[0] = opcode >> 8;
			((uint8_t*)loc)[1] = opcode & 0xff;
			assert(disp <= INT32_MAX && disp >= INT32_MIN);
			*((int32_t*)((uint8_t*)loc + 2)) = (int32_t)disp;
			len = JCC_REL32_NBYTES;
		}
		break;

	case UD_Ijmp:
		/* unconditional */
		(fits_rel8 ? genjmprel8 : genjmprel32)(loc,targ);
		len = fits_rel8 ? JMP_REL8_NBYTES : JMP_REL32_NBYTES;
		break;

	case UD_Ijcxz:
	case UD_Ijecxz:
	case UD_Ijrcxz:
		fprintf(pllog,"stupid-ass x86 jcx NYI\n");
		abort();

	default:
		fprintf(pllog,"unexpected instruction in retarget_branch: %s\n",ud_insn_asm(&ud));
		abort();
	}

	return len;
}

static void invasive_jmppatch(void* origin, void* dest, struct trampmap* tm)
{
	int nsuccs,succbytes;
	struct inst srcinst, succs[JCC_REL32_NBYTES];
	void* retaddr;
	void* tfaddr;
	uint8_t* iptr;
	ud_t srcud;
	size_t added,int3len;

	init_udinst(&srcud,origin,X86_MAX_INST_LEN);
	ud_disassemble(&srcud);

	dup_ud_inst(&srcud,&srcinst);

	/* FIXME: ensure this patch doesn't overlap another */
	retaddr = find_clobber_succs(origin,JMP_REL32_NBYTES,succs,
	                             &nsuccs,&succbytes);

	tfaddr = iptr = tm->base + tm->used;
	assert((uintptr_t)iptr % TRAMPFUNC_ALIGN == 0);

	/* jump to the trampoline area */
	genjmprel32(origin,tfaddr);

	/* fill with int3s to next instruction */
	int3len = succbytes + srcinst.len - JMP_REL32_NBYTES;
	memset(origin+JMP_REL32_NBYTES,X86OP_INT3,int3len);

	/* move the original instruction to the trampoline */
	if (tm->used + srcinst.len > tm->size) {
		fprintf(pllog,"trampoline area overflow\n");
		abort();
	}
	memcpy(iptr,srcinst.bytes,srcinst.len);

	/* point the branch at its new target */
	added = retarget_branch(iptr,dest);
	iptr += added;
	tm->used += added;

	/* move any other instructions we need */
	added = translate_insts(succs,nsuccs,iptr,tm->size - tm->used);
	iptr += added;
	tm->used += added;

	/* add the return branch */
	genjmprel32(iptr,retaddr);
	iptr += JMP_REL32_NBYTES;
	tm->used += JMP_REL32_NBYTES;

	/* pad out to an aligned boundary */
	while ((uintptr_t)iptr % TRAMPFUNC_ALIGN) {
		*iptr++ = X86OP_INT3;
		tm->used++;
	}
}

static void check_jump(ud_t* ud, struct trampmap* tm)
{
	void* targ;
	void* newtarg;
	void* trampaddr;
	void* instaddr;
	struct clobberpatch* collision;
	struct inst trampjmp_inst;
	struct scratchbuf* scratchlink;
	ud_t trampjmp;
	int64_t disp;

	switch (ud->operand[0].type) {

	case UD_OP_REG:
	case UD_OP_MEM:
		/* we'll assume these are safe. */
		return;

	case UD_OP_JIMM:
		targ = get_jmptarg(ud);
		break;

	default:
		abort();
	}

	/* this is very inefficient (doing a fresh search for every
	 * jump) */
	collision = bsearch(targ,clobberpatches,nclobberpatches,sizeof(*clobberpatches),
	                    jmpcheck_clobberpatch_bscmp);
	if (!collision)
		return;

	trampjmp_inst = (struct inst) {
		.pc = collision->start,
		.bytes = collision->start,
		.len = JMP_REL32_NBYTES,
	};
	inst_to_ud(&trampjmp_inst,&trampjmp);
	trampaddr = get_jmptarg(&trampjmp);

	/* FIXME: this will need fixing when trampolines aren't no-ops */
	newtarg = trampaddr + (targ - collision->start);

	instaddr = (void*)ud->pc - ud_insn_len(ud);

	if (ud->operand[0].size == 32) {
		/* we can just patch the existing instruction */
		disp = newtarg - (void*)ud->pc;
		assert(disp <= INT32_MAX && disp >= INT32_MIN);
		*(int32_t*)(instaddr+get_jmpdisp_ofst(ud)) = disp;
	} else {
		/* things get uglier. */
		scratchlink = find_scratchpath(instaddr);
		if (scratchlink) {
			patch_jmpchain(instaddr,scratchlink,newtarg);
		} else {
			invasive_jmppatch(instaddr,newtarg,tm);
		}
	}
}

static void jmpchkpass(void* buf, size_t len, struct trampmap* tm)
{
	ud_t ud;

	init_udinst(&ud,buf,len);

	while (ud_disassemble(&ud)) {
		switch (ud.mnemonic) {
		case UD_Ijmp:
		case UD_Ijo:
		case UD_Ijno:
		case UD_Ijb:
		case UD_Ijae:
		case UD_Ijz:
		case UD_Ijnz:
		case UD_Ijbe:
		case UD_Ija:
		case UD_Ijs:
		case UD_Ijns:
		case UD_Ijp:
		case UD_Ijnp:
		case UD_Ijl:
		case UD_Ijge:
		case UD_Ijle:
		case UD_Ijg:
		case UD_Ijcxz:
		case UD_Ijecxz:
		case UD_Ijrcxz:
			check_jump(&ud,tm);
			break;
		default:
			break;
		}
	}
}

static void syspatchpass(struct trampmap* tm)
{
	int i;
	struct scratchbuf* scratchlink;
	struct inst scinst,succs[3];
	int nsuccs,succbytes,int3len;
	void* tfaddr;
	void* retaddr;

	for (i = 0; i < nsyscalls; i++) {
		scinst = (struct inst) {
			.bytes = syscalls[i],
			.len = SYSCALL_NBYTES,
			.pc = syscalls[i],
		};
		scratchlink = find_scratchpath(syscalls[i]);
		if (scratchlink) {
			tfaddr = gentramp(&scinst,NULL,0,tm,
			                  syscalls[i]+JMP_REL8_NBYTES);
			patch_jmpchain(syscalls[i],scratchlink,tfaddr);
		} else {
			retaddr = find_clobber_succs(syscalls[i],JMP_REL32_NBYTES,
			                             succs,&nsuccs,&succbytes);
			tfaddr = gentramp(&scinst,succs,nsuccs,tm,retaddr);
			genjmprel32(syscalls[i],tfaddr);

			new_clobberpatch(syscalls[i],succbytes+SYSCALL_NBYTES);

			int3len = succbytes + SYSCALL_NBYTES - JMP_REL32_NBYTES;
			memset(syscalls[i]+JMP_REL32_NBYTES,X86OP_INT3,int3len);

			/* if the int3 hole is big enough to be potentially
			 * useful in the future, keep track of it. */
			if (int3len > JMP_REL8_NBYTES)
				new_nopbuf(syscalls[i]+JMP_REL32_NBYTES,int3len,0);
		}
	}

	/* we may have added scratchbufs onto the end of the nopbufs
	 * array, so re-sort it */
	qsort(nopbufs,nnopbufs,sizeof(*nopbufs),scratchbuf_cmp);
}

/*
 * Finds and record usefully-sized nop buffers and locations of
 * syscall instructions.
 */
static void scanpass(void* buf, size_t len)
{
	ud_t ud;
	unsigned int nopbytes = 0;
	int fallthrough = 1,holdoff = 0;

	init_udinst(&ud,buf,len);

	while (ud_disassemble(&ud)) {
		switch (ud.mnemonic) {

		case UD_Ifnop:
		case UD_Inop:
			if (!holdoff)
				nopbytes += ud_insn_len(&ud);
			break;

		default:
			/* if we could fallthrough into the nopbuf,
			 * we'll need space for *two* jmp_rel8s (one
			 * to the next link, and one at the top to
			 * skip over our modifications); */
			if ((fallthrough && nopbytes >= 2*JMP_REL8_NBYTES)
			    || (!fallthrough && nopbytes >= JMP_REL8_NBYTES)) {
				new_nopbuf((void*)ud.pc - ud_insn_len(&ud) - nopbytes,
				           nopbytes,fallthrough);
			}
			/* ASSUMPTION: a jmp/call won't be pointed at
			 * a nop in the next few bytes */
			fallthrough = (ud.mnemonic != UD_Iret
			               && ud.mnemonic != UD_Ijmp);
			nopbytes = 0;

			if (ud.mnemonic == UD_Isyscall
			    || ud.mnemonic == UD_Isysenter
			    || (ud.mnemonic == UD_Iint
			        && ud.operand[0].lval.ubyte == 0x80)) {
				new_syscall((void*)ud.pc - ud_insn_len(&ud));
				/* don't count nops that might fall in
				 * this syscall's "shadow", so we don't
				 * end up with patch collisions */
				holdoff = JMP_REL32_NBYTES;
			}

			break;
		}

		holdoff -= ud_insn_len(&ud);
		if (holdoff < 0)
			holdoff = 0;
	}
}

static void patch_sys_entries(void* buf, size_t len, struct trampmap* tm)
{
	scanpass(buf,len); /* populates 'syscalls' and 'nopbufs' arrays */
	syspatchpass(tm); /* populates 'clobberpatches' array */
	jmpchkpass(buf,len,tm); /* checks for jumps with a destination in a clobberpatch */

	if (syscalls) {
		free(syscalls);
		syscalls = NULL;
		nsyscalls = 0;
	}

	if (clobberpatches) {
		free(clobberpatches);
		clobberpatches = NULL;
		nclobberpatches = 0;
	}

	if (nopbufs) {
		free(nopbufs);
		nopbufs = NULL;
		nnopbufs = 0;
		allocnopbufs = 0;
	}
}

struct map {
	void* start;
	void* end;
	int prot;
	off_t ofst;
	uint8_t majdev,mindev;
	ino_t inode;
	char* path;
	int tmnum;
};

struct codeseg {
	void* start;
	size_t len;
	int mapnum;
	char* secname;
	char* filename;
};

static struct map* maps = NULL;
static unsigned int nmaps = 0;

static struct codeseg* codesegs = NULL;
static unsigned int ncodesegs = 0;

static int perms_to_prot(char str[4])
{
	int flags = PROT_NONE;
	flags |= str[0] == 'r' ? PROT_READ : 0;
	flags |= str[1] == 'w' ? PROT_WRITE : 0;
	flags |= str[2] == 'x' ? PROT_EXEC : 0;
	return flags;
}

/* comparison function for two maps' address spaces */
static int mapcmp(const void* a, const void* b)
{
	const struct map* ma = a;
	const struct map* mb = b;
	if (ma->start < mb->start)
		return -1;
	if (ma->start == mb->start)
		return 0;
	if (ma->start > mb->start)
		return 1;
	abort();
}

/* snapshot the proc's memory maps before we start messing with things */
static void read_maps(void)
{
	FILE* procmaps;
	void* start;
	void* end;
	char perms[4];
	off_t ofst;
	uint8_t majdev,mindev;
	int inode;
	char path[PATH_MAX];
	char space;
	int nscanned;

	procmaps = fopen("/proc/self/maps","r");
	assert(procmaps);
	while (1) {
		nscanned = fscanf(procmaps,"%p-%p %s %lx %hhx:%hhx %i%c",
		                  &start,&end,perms,&ofst,&majdev,&mindev,&inode,&space);
		if (feof(procmaps))
			break;
		assert(nscanned == 8);
		assert(space == ' ');
		if (fgetc(procmaps) == '\n')
			path[0] = '\0';
		else
			fscanf(procmaps," %s\n",path);

		maps = realloc(maps,sizeof(*maps)*++nmaps);
		assert(maps);
		maps[nmaps-1].start = start;
		maps[nmaps-1].end = end;
		maps[nmaps-1].prot = perms_to_prot(perms);
		maps[nmaps-1].ofst = ofst;
		maps[nmaps-1].majdev = majdev;
		maps[nmaps-1].mindev = mindev;
		maps[nmaps-1].inode = inode;
		maps[nmaps-1].path = strdup(path);
		maps[nmaps-1].tmnum = -1;
	}
	fclose(procmaps);

	/* it appears the kernel does this anyway, but later
	 * assumptions (in get_trampmap) depend on our maps being in
	 * order of increasing addresses, so make sure they really
	 * are. */
	qsort(maps,nmaps,sizeof(*maps),mapcmp);
}

static int new_trampmap(void* base, int origmap)
{
	void* tmbase;
	assert((uintptr_t)base % sysconf(_SC_PAGESIZE) == 0);

	tmbase = mmap(base,TRAMPMAP_MIN_SIZE,
	              PROT_READ|PROT_WRITE|PROT_EXEC,
	              MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED,-1,0);
	if (tmbase == MAP_FAILED) {
		fprintf(pllog,"trampoline area mmap failed for map %i (%s) at %p: %s\n",
		        origmap,maps[origmap].path,base,strerror(errno));
		base = (void*)((uintptr_t)base - (uintptr_t)(1ULL<<32));
		tmbase = mmap(base,TRAMPMAP_MIN_SIZE,
		              PROT_READ|PROT_WRITE|PROT_EXEC,
		              MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED,-1,0);
		if (tmbase == MAP_FAILED) {
			fprintf(pllog,"and failed again at %p\n",base);
			return -1;
		} else
			fprintf(pllog,"but worked on retry at %p\n",base);
	}
	assert(tmbase == base);
	trampmaps = realloc(trampmaps,
	                    sizeof(*trampmaps)*++ntrampmaps);
	assert(trampmaps);
	trampmaps[ntrampmaps-1].base = tmbase;
	trampmaps[ntrampmaps-1].size = TRAMPMAP_MIN_SIZE;
	trampmaps[ntrampmaps-1].used = 0;
	trampmaps[ntrampmaps-1].mapnum = origmap;

	return ntrampmaps - 1;
}

/* find space for and create the trampoline area used for patching
 * maps[origmap], adding and entry to trampmaps and returning its
 * index. */
static int get_trampmap(unsigned int origmap)
{
	int mi;
	struct map* m;
	void* lbound;

	assert(maps[origmap].tmnum == -1);

	/* because of the order in which we're doing things, the first
	 * possible place we could put it is just past the last
	 * trampmap */
	if (ntrampmaps)
		lbound = trampmaps[ntrampmaps-1].base + trampmaps[ntrampmaps-1].size;
	else
		lbound = 0;

	for (mi = origmap+1, m = maps+origmap+1; mi < nmaps; m++, mi++) {
		if (lbound < (m-1)->end)
			lbound = (m-1)->end;

		if (m->start - lbound >= TRAMPMAP_MIN_SIZE)
			return new_trampmap(lbound,origmap);
	}

	if (mi == nmaps) {
		mi = nmaps - 1;
		m = &maps[mi];
		if (lbound < m->end)
			lbound = m->end;
		if (UINTPTR_MAX - (uintptr_t)lbound >= TRAMPMAP_MIN_SIZE - 1)
			return new_trampmap(lbound,origmap);
	}

	fprintf(pllog,"failed to find trampoline area for map %i (%s)\n",
	        origmap,maps[origmap].path);
	abort();
}

static void print_maps(void)
{
	int i,p;

	fprintf(pllog,"initial maps:\n");

	for (i = 0; i < nmaps; i++) {
		p = maps[i].prot;
		fprintf(pllog,"%p-%p %c%c%c %s\n",maps[i].start,maps[i].end,
		        p & PROT_READ ? 'r' : '-', p & PROT_WRITE ? 'w' : '-',
		        p & PROT_EXEC ? 'x' : '-', maps[i].path);
	}
}

static int map_path(const char* path, void** base, size_t* len)
{
	int fd;
	struct stat st;

	if ((fd = open(path,O_RDONLY)) == -1) {
		fprintf(pllog,"failed to open '%s': %s\n",path,strerror(errno));
		return -1;
	}

	if ((fstat(fd,&st)) == -1) {
		fprintf(pllog,"failed to stat(2) '%s': %s\n",path,strerror(errno));
		close(fd);
		return -1;
	}

	*base = mmap(NULL,st.st_size,PROT_READ,MAP_PRIVATE,fd,0);
	if (*base == MAP_FAILED) {
		fprintf(pllog,"failed to mmap '%s': %s\n",path,strerror(errno));
		*base = NULL;
		close(fd);
		return -1;
	}

	*len = st.st_size;

	close(fd);

	return 0;
}

static void read_codesegs(int mapnum)
{
	void* base;
	size_t len;
	unsigned int elfversion;
	char* path;
	char* secname;
	Elf* elf;
	Elf_Scn* esec;
	GElf_Shdr shdr;
	size_t shstrndx;

	path = maps[mapnum].path;
	elfversion = elf_version(EV_CURRENT);
	assert(elfversion != EV_NONE);

	if (map_path(path,&base,&len)) {
		fprintf(pllog,"failed to mmap '%s': %s\n",path,strerror(errno));
		abort();
	}

	if (!(elf = elf_memory(base,len))) {
		fprintf(pllog,"libelf elf_memory() failed: %s\n",elf_errmsg(-1));
		abort();
	}

	if (elf_kind(elf) != ELF_K_ELF) {
		fprintf(pllog,"%s not an ELF??\n",path);
		abort();
	}

	if (elf_getshdrstrndx(elf,&shstrndx)) {
		fprintf(pllog,"elf_getshstrndx() failed: %s\n",elf_errmsg(-1));
		abort();
	}

	esec = NULL;
	while ((esec = elf_nextscn(elf,esec))) {
		if (gelf_getshdr(esec,&shdr) != &shdr) {
			fprintf(pllog,"gelf_getshdr failed\n");
			abort();
		}

		if ((shdr.sh_type != SHT_PROGBITS)
		    || !(shdr.sh_flags & SHF_ALLOC)
		    || !(shdr.sh_flags & SHF_EXECINSTR))
			continue;

		if (!(secname = elf_strptr(elf,shstrndx,shdr.sh_name))) {
			fprintf(pllog,"elf_strptr() failed: %s\n",elf_errmsg(-1));
			abort();
		}

		if (shdr.sh_addr < (uintptr_t)maps[mapnum].start
		    || (shdr.sh_addr + shdr.sh_size) > (uintptr_t)maps[mapnum].end) {
			fprintf(pllog,"%s:.%s section not contained in map %i\n",
			        path,secname,mapnum);
			abort();
		}

		codesegs = realloc(codesegs,sizeof(*codesegs)*++ncodesegs);
		assert(codesegs);
		codesegs[ncodesegs-1] = (struct codeseg) {
			.start = (void*)shdr.sh_addr,
			.len = shdr.sh_size,
			.mapnum = mapnum,
			.secname = strdup(secname),
			.filename = strdup(path),
		};
	}

	elf_end(elf);
	munmap(base,len);
}

static void scan_and_patch(void)
{
	char* basename;
	int i,tmnum;
	struct map* m;
	struct codeseg* cs;

	for (m = maps, i = 0; i < nmaps; m++, i++) {
		if (m->prot & PROT_EXEC) {

			/* don't scan/patch our own code */
			if ((basename = strrchr(m->path,'/'))
			    && (!strcmp(basename+1,"libhotpatch.so")
			        || !strncmp(basename+1,"libelf.so",
			                    strlen("libelf.so"))))
				continue;

			if (!strcmp(m->path,"[vdso]")
			    || !strcmp(m->path,"[vsyscall]"))
				continue;

			if (mprotect(m->start,m->end-m->start,m->prot|PROT_WRITE)) {
				fprintf(pllog,"mprotect failed on map %i (%s): %s\n",
				        i,m->path,strerror(errno));
				abort();
			}

			tmnum = get_trampmap(i);

			if (tmnum == -1) {
				fprintf(pllog,"mmap failed for %s trampoline area",
				        maps[i].path);
				if (!strcmp(maps[i].path,"[vdso]")
				    || !strcmp(maps[i].path,"[vsyscall]"))
					fprintf(pllog,", ignoring...\n");
				else {
					fprintf(pllog,", aborting!\n");
					abort();
				}
			} else {
				m->tmnum = tmnum;
				read_codesegs(i);
			}
		}
	}

	for (cs = codesegs, i = 0; i < ncodesegs; cs++, i++) {
		patch_sys_entries(cs->start,cs->len,
		                  &trampmaps[maps[cs->mapnum].tmnum]);
	}
}

static void printargv(void)
{
	int c;
	FILE* argfile;

	argfile = fopen("/proc/self/cmdline","r");
	assert(argfile);

	fprintf(pllog,"%i: ",getpid());
	while ((c =fgetc(argfile)) != EOF)
		fputc(c ? c : ' ',pllog); /* args in /proc/pid/cmdline are NUL-delimited */
	fputc('\n',pllog);

	fflush(pllog);
	fclose(argfile);
}

static void print_loghdr(void)
{
	printargv();
}

static void libhotpatch_init(void)
{
	const char* hotpatch;
	const char* logpath;

	logpath = getenv("LIBHOTPATCH_LOGPATH");
	if (!logpath || !strlen(logpath))
		logpath = "./hplog";

	pllog = fopen(logpath,"w");
	assert(pllog);
	print_loghdr();

	hotpatch = getenv("LIBHOTPATCH_ENABLE");
	if (hotpatch && strlen(hotpatch) > 0) {
		read_maps();
		scan_and_patch();
	}
}

static void libhotpatch_fini(void)
{
	fclose(pllog);
}
