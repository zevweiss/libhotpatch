#define _GNU_SOURCE
#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <assert.h>
#include <dlfcn.h>
#include <signal.h>
#include <limits.h>
#include <string.h>
#include <stdint.h>

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
static int inst_relocatable(ud_t* ud)
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
			fprintf(pllog,"warning: must relocate %s\n",ud_insn_asm(ud));
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
	char* bytes;
	uint8_t len;
};

static void dup_ud_inst(ud_t* ud, struct inst* inst)
{
	inst->len = ud_insn_len(ud);
	inst->bytes = malloc(inst->len);
	assert(inst->bytes);
	memcpy(inst->bytes,ud_insn_ptr(ud),inst->len);
}

static unsigned int patch_sys_entries(void* buf, size_t len)
{
	ud_t ud;
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
			for (i = 0, succbytes = 0; i < 3 && succbytes < 3; i++) {
				ud_disassemble(&ud);
				if (!inst_relocatable(&ud)) {
/* 					fprintf(pllog,"uh-oh, non-relocatable inst: %s\n", */
/* 					        ud_insn_asm(&ud)); */
/* 					abort(); */
				}
				dup_ud_inst(&ud,&succs[i]);
				succbytes += succs[i].len;
			}
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
	char perms[4];
	off_t ofst;
	uint8_t majdev,mindev;
	int inode;
	char* path;
};

struct map* maps = NULL;
unsigned int nmaps = 0;

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

		maps = realloc(maps,sizeof(struct map)*++nmaps);
		maps[nmaps-1].start = start;
		maps[nmaps-1].end = end;
		memcpy(maps[nmaps-1].perms,perms,sizeof(perms));
		maps[nmaps-1].ofst = ofst;
		maps[nmaps-1].majdev = majdev;
		maps[nmaps-1].mindev = mindev;
		maps[nmaps-1].inode = inode;
		maps[nmaps-1].path = strdup(path);
	}
	fclose(procmaps);
}

static void find_text(void)
{
	char* basename;
	int i;
	struct map* m;

	read_maps();

	for (m = maps, i = 0; i < nmaps; m++, i++) {
		if (m->perms[2] == 'x') {
			if ((basename = strrchr(m->path,'/'))
			    && !strcmp(basename+1,"lib752.so"))
				continue;
			fprintf(pllog,"found executable map from '%s'\n",m->path);
			patch_sys_entries(m->start,m->end - m->start);
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
	// need to ensure *one* of main code or signal handler can access FILE*s at any given point
	signal(SIGUSR1,SIG_IGN);

	showstats(1);
	fclose(pllog);
}
