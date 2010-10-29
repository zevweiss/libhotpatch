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

static unsigned int patch_sys_entries(void* buf, size_t len)
{
	ud_t ud;
	unsigned int bytes;
	unsigned int found = 0;

	ud_init(&ud);
	ud_set_input_buffer(&ud,buf,len);
	ud_set_mode(&ud,64);

	while ((bytes = ud_disassemble(&ud))) {
		switch (ud.mnemonic) {
		case UD_Isyscall:
		case UD_Isysenter:
			++found;
			break;
		case UD_Iint:
			assert(ud.operand[0].type == UD_OP_IMM);
			if (ud.operand[0].lval.ubyte == 0x80)
				++found;
			break;
		default:
			break;
		}
	}
	return found;
}

static void find_text(void)
{
	FILE* maps;
	char path[PATH_MAX];
	char perms[4];
	void* start;
	void* end;
	off_t ofst;
	char majdev,mindev,space;
	int inode;
	int nscanned;
	char* basename;
	int patches;

	maps = fopen("/proc/self/maps","r");
	assert(maps);
	while (1) {
		nscanned = fscanf(maps,"%p-%p %s %lx %hhx:%hhx %i%c",
		                  &start,&end,perms,&ofst,&majdev,&mindev,&inode,&space);
		if (feof(maps))
			break;
		assert(nscanned == 8);
		assert(space == ' ');
		if (fgetc(maps) == '\n')
			path[0] = '\0';
		else
			fscanf(maps," %s\n",path);

		if (perms[2] == 'x') {
			if ((basename = strrchr(path,'/'))
			    && !strcmp(basename+1,"lib752.so"))
				continue;
			patches = patch_sys_entries(start,end-start);
			fprintf(pllog,"found executable map from '%s' with %i system entries\n",path,patches);
		}
	}

	fclose(maps);
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
