#define _GNU_SOURCE
#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/mman.h>
#include <unistd.h>
#include <assert.h>
#include <dlfcn.h>
#include <signal.h>
#include <limits.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>

#include <udis86.h>

static void lib752_init(void) __attribute__((constructor));
static void lib752_fini(void) __attribute__((destructor));

static void usr_handler(int signo);

#define CALLWRAP(name,rettype,parmlist,callargs,extra)	  \
	rettype name parmlist \
	{ \
		static typeof(&name) real_##name = NULL; \
		if (!real_##name) { \
			real_##name = dlsym(RTLD_NEXT,#name); \
		} \
		extra; \
		return real_##name callargs; \
	}

#define CALLWRAP0(name,rettype,extra) \
	CALLWRAP(name,rettype,(void),(),extra)
#define CALLWRAP1(name,rettype,t1,p1,extra) \
	CALLWRAP(name,rettype,(t1 p1),(p1),extra)
#define CALLWRAP2(name,rettype,t1,p1,t2,p2,extra) \
	CALLWRAP(name,rettype,(t1 p1, t2 p2),(p1,p2),extra)
#define CALLWRAP3(name,rettype,t1,p1,t2,p2,t3,p3,extra) \
	CALLWRAP(name,rettype,(t1 p1, t2 p2, t3 p3),(p1,p2,p3),extra)
#define CALLWRAP4(name,rettype,t1,p1,t2,p2,t3,p3,t4,p4,extra) \
	CALLWRAP(name,rettype,(t1 p1, t2 p2, t3 p3, t4 p4),(p1,p2,p3,p4),extra)
#define CALLWRAP5(name,rettype,t1,p1,t2,p2,t3,p3,t4,p4,t5,p5,extra) \
	CALLWRAP(name,rettype,(t1 p1, t2 p2, t3 p3, t4 p4, t5 p5), \
	         (p1,p2,p3,p4,p5),extra)
#define CALLWRAP6(name,rettype,t1,p1,t2,p2,t3,p3,t4,p4,t5,p5,t6,p6,extra) \
	CALLWRAP(name,rettype,(t1 p1, t2 p2, t3 p3, t4 p4, t5 p5, t6 p6), \
	         (p1,p2,p3,p4,p5,p6),extra)

#define NO_EXTRA

CALLWRAP0(fork,pid_t,NO_EXTRA);

CALLWRAP3(read,ssize_t,int,fd,void*,buf,size_t,count,NO_EXTRA);
CALLWRAP3(write,ssize_t,int,fd,const void*,buf,size_t,count,NO_EXTRA);

CALLWRAP6(mmap,void*,void*,addr,size_t,length,
          int,prot,int,flags,int,fd,off_t,offset,NO_EXTRA);
CALLWRAP6(mmap2,void*,void*,addr,size_t,length,
          int,prot,int,flags,int,fd,off_t,offset,NO_EXTRA);

static FILE* pllog;

#define ZERO_RUSAGE { \
	.ru_utime = { .tv_sec = 0, .tv_usec = 0, }, \
	.ru_stime = { .tv_sec = 0, .tv_usec = 0, }, \
	.ru_majflt = 0, \
	.ru_nswap = 0, \
	.ru_nvcsw = 0, \
	.ru_nivcsw = 0, \
}

static struct rusage tot_self_rusage = ZERO_RUSAGE, tot_children_rusage = ZERO_RUSAGE;

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

static void rusage_hdr(void)
{
	fprintf(pllog,"%15s %12s %12s %10s %10s %8s %10s %10s\n","",
	        "User CPU","System CPU","majflt", "minflt","Swaps",
	        "VCSW","ICSW");
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
	case UD_Iand:
	case UD_Iadd:
	case UD_Ixor:
	case UD_Ixchg:
	case UD_Ineg:
	case UD_Ipop:
	case UD_Ipush:
		if (inst_opnd_rip_rel(ud)) {
			fprintf(pllog,"warning: must relocate %s [%s]\n",
			        ud_insn_asm(ud),ud_insn_hex(ud));
			return 0;
		} else
			return 1;

	case UD_Ijmp:
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

static void inst_to_ud(const struct inst* inst, ud_t* ud)
{
	ud_init(ud);
	ud_set_input_buffer(ud,inst->bytes,inst->len);
	ud_set_mode(ud,64);
	ud_set_syntax(ud,UD_SYN_ATT);
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
 * Used as a filler byte in trampoline areas so we'll trap in case
 * anything goes unexpectedly out of bounds.
 */
#define X86OP_INT3 0xcc
#define X86OP_JMP_REL32 0xe9

#define JMP_REL32_NBYTES 5
#define JCC_REL32_NBYTES 6
#define JCC_REL8_NBYTES 2
	

/*
 * "Translate" an instruction for relocation from orig->pc to new->pc
 * (which must be filled in by the caller, new's other fields will be
 * filled in by translate_inst()).
 */
static void translate_inst(const struct inst* orig, struct inst* new)
{
	ud_t oud;
	int64_t origofst,newofst;
	uintptr_t jcctarg;
	uint16_t jccop;

	inst_to_ud(orig,&oud);
	if (udinst_relocatable(&oud)) {
		*new = *orig;
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
			jccop = 0x0f80 | (orig->bytes[0] & 0x0f);
			break;
		case 32:
			origofst = oud.operand[0].lval.sdword;
			jccop = (orig->bytes[0] << 8) | orig->bytes[1];
			break;
		default:
			fprintf(pllog,"unknown jcc operand size (%i)\n",
			        oud.operand[0].size);
		}

		jcctarg = (uintptr_t)orig->pc + orig->len + origofst;
		newofst = (int64_t)jcctarg - ((int64_t)new->pc + JCC_REL32_NBYTES);
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
	default:
		fprintf(pllog,"warning: not translating %s\n",ud_insn_asm(&oud));
		*new = *orig;
	}
}

/*
 * Trampoline functions will start on 8-byte aligned addresses.
 */
static void gentramp(const struct inst* orig, const struct inst* succs,
                     int nsuccs, struct trampmap* tm, void* retaddr)
{
	uint8_t* iptr;
	int i;
	struct inst trans;
	int64_t retofst;

	iptr = tm->base + tm->used;

	assert((uintptr_t)iptr % 8 == 0);

	/* for starters we'll just do a no-op trampoline */
	if (tm->used + orig->len > tm->size) {
		fprintf(pllog,"trampoline area overflow\n");
		abort();
	}
	iptr = mempcpy(iptr,orig->bytes,orig->len);
	tm->used += orig->len;

	for (i = 0; i < nsuccs; i++) {
		trans.pc = iptr;
		translate_inst(&succs[i],&trans);
		if (tm->used + trans.len > tm->size) {
			fprintf(pllog,"trampoline area overflow\n");
			abort();
		}
		iptr = mempcpy(iptr,trans.bytes,trans.len);
		tm->used += trans.len;
	}

	retofst = (int64_t)retaddr - ((int64_t)iptr + JMP_REL32_NBYTES);
	if (retofst > INT32_MAX || retofst < INT32_MIN) {
		fprintf(pllog,"return branch beyond rel32 range\n");
		abort();
	}

	/* and generate the return jmp */
	*iptr++ = X86OP_JMP_REL32;
	tm->used++;
	*(int32_t*)iptr = (int32_t)retofst;
	iptr += sizeof(int32_t);
	tm->used += sizeof(int32_t);

	while ((uintptr_t)iptr % 8) {
		*iptr++ = X86OP_INT3;
		tm->used++;
	}
	return;
}

static unsigned int patch_sys_entries(void* buf, size_t len, struct trampmap* tm)
{
	ud_t ud;
	struct inst orig;
	struct inst succs[3];	/* successor instructions */
	unsigned int found = 0;
	unsigned int i,succbytes;

	ud_init(&ud);
	ud_set_input_buffer(&ud,buf,len);
	ud_set_syntax(&ud,UD_SYN_ATT);
	ud_set_mode(&ud,64);
	ud_set_pc(&ud,(uint64_t)buf);

	while (ud_disassemble(&ud)) {
		switch (ud.mnemonic) {
		case UD_Iint:
			assert(ud.operand[0].type == UD_OP_IMM);
			if (ud.operand[0].lval.ubyte != 0x80)
				break;
			/* otherwise fall through */
		case UD_Isyscall:
		case UD_Isysenter:
			++found;
			assert(ud_insn_len(&ud) == 2);
			dup_ud_inst(&ud,&orig);
			for (i = 0, succbytes = 0; i < 3 && succbytes < 3; i++) {
				ud_disassemble(&ud);
				dup_ud_inst(&ud,&succs[i]);
				succbytes += succs[i].len;
			}
			gentramp(&orig,succs,i,tm,(void*)ud.pc);
			break;
		default:
			break;
		}
	}
	return found;
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

static struct map* maps = NULL;
static unsigned int nmaps = 0;

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
void read_maps(void)
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
	assert((uintptr_t)base % getpagesize() == 0);

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

static void find_text(void)
{
	char* basename;
	int i,nfound = 0,tmnum;
	struct map* m;

	read_maps();

	for (m = maps, i = 0; i < nmaps; m++, i++) {
		if (m->prot & PROT_EXEC) {
			if ((basename = strrchr(m->path,'/'))
			    && !strcmp(basename+1,"lib752.so"))
				continue;
//			fprintf(pllog,"found executable map from '%s'\n",m->path);
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
				nfound = patch_sys_entries(m->start,m->end - m->start,
				                           &trampmaps[tmnum]);
//				fprintf(pllog,"  %i sysentry points found\n",nfound);
			}
		}
	}
}

static void lib752_init(void)
{
	sighandler_t ret;

	ret = signal(SIGUSR1,usr_handler);
	assert(ret != SIG_ERR);
	ret = signal(SIGUSR2,usr_handler);
	assert(ret != SIG_ERR);

	pllog = fopen("./log","a");
	assert(pllog);
	printargv();
	find_text();

	rusage_hdr();

//	unsetenv("LD_PRELOAD");
}

static void printrusage(struct rusage* r, const char* pfx)
{
	fprintf(pllog,"%-15s %5li.%06li %5li.%06li",pfx,
	        r->ru_utime.tv_sec,r->ru_utime.tv_usec,
	        r->ru_stime.tv_sec,r->ru_stime.tv_usec);

	fprintf(pllog," %10li %10li %8li %10li %10li\n",
	        r->ru_majflt,r->ru_minflt,r->ru_nswap,r->ru_nvcsw,r->ru_nivcsw);

	fflush(pllog);
}

static void rusage_sub(const struct rusage* a, const struct rusage* b,
                       struct rusage* res)
{
	timersub(&a->ru_utime,&b->ru_utime,&res->ru_utime);
	timersub(&a->ru_stime,&b->ru_stime,&res->ru_stime);
#define SUBRUMEMB(m) res->ru_##m = a->ru_##m - b->ru_##m
	SUBRUMEMB(maxrss);
	SUBRUMEMB(ixrss);
	SUBRUMEMB(idrss);
	SUBRUMEMB(isrss);
	SUBRUMEMB(minflt);
	SUBRUMEMB(majflt);
	SUBRUMEMB(nswap);
	SUBRUMEMB(inblock);
	SUBRUMEMB(oublock);
	SUBRUMEMB(msgsnd);
	SUBRUMEMB(msgrcv);
	SUBRUMEMB(nsignals);
	SUBRUMEMB(nvcsw);
	SUBRUMEMB(nivcsw);
#undef SUBRUMEMB
}

static void rusage_add(const struct rusage* a, const struct rusage* b,
                       struct rusage* res)
{
	timeradd(&a->ru_utime,&b->ru_utime,&res->ru_utime);
	timeradd(&a->ru_stime,&b->ru_stime,&res->ru_stime);
#define ADDRUMEMB(m) res->ru_##m = a->ru_##m + b->ru_##m
	ADDRUMEMB(maxrss);
	ADDRUMEMB(ixrss);
	ADDRUMEMB(idrss);
	ADDRUMEMB(isrss);
	ADDRUMEMB(minflt);
	ADDRUMEMB(majflt);
	ADDRUMEMB(nswap);
	ADDRUMEMB(inblock);
	ADDRUMEMB(oublock);
	ADDRUMEMB(msgsnd);
	ADDRUMEMB(msgrcv);
	ADDRUMEMB(nsignals);
	ADDRUMEMB(nvcsw);
	ADDRUMEMB(nivcsw);
#undef ADDRUMEMB
}

static void showstats(int abs)
{
	struct rusage newself, newchildren, deltaself, deltachildren;
	struct rusage* sprint;
	struct rusage* cprint;
	char pfxbuf[64]; // HACK

	getrusage(RUSAGE_SELF,&newself);
	getrusage(RUSAGE_CHILDREN,&newchildren);

	rusage_sub(&newself,&tot_self_rusage,&deltaself);
	rusage_sub(&newchildren,&tot_children_rusage,&deltachildren);

	memcpy(&tot_self_rusage,&newself,sizeof(struct rusage));
	memcpy(&tot_children_rusage,&newchildren,sizeof(struct rusage));

	sprint = abs ? &newself : &deltaself;
	cprint = abs ? &newchildren : &deltachildren;

	snprintf(pfxbuf,sizeof(pfxbuf),"%i",getpid());
	printrusage(sprint,pfxbuf);

	if (cprint->ru_utime.tv_sec || cprint->ru_utime.tv_usec
	    || cprint->ru_stime.tv_sec || cprint->ru_stime.tv_usec
            || cprint->ru_majflt || cprint->ru_nswap
	    || cprint->ru_nvcsw || cprint->ru_nivcsw) {
		snprintf(pfxbuf,sizeof(pfxbuf),"%i-children",getpid());
		printrusage(cprint,pfxbuf);
	}
}

static void usr_handler(int signo)
{
	showstats(signo == SIGUSR1);
}

static void lib752_fini(void)
{
	signal(SIGUSR1,SIG_DFL);

	showstats(1);
	fclose(pllog);
}
