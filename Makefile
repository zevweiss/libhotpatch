CC = gcc
CWARN = -Wall -Wextra -Wno-sign-compare
CDEBUG = -ggdb3
COPT = -O0
CFLAGS = $(CWARN) $(CDEBUG) $(COPT) -fPIC -fvisibility=hidden

DLIBS = dl elf

# TODO: build libudis86 automatically...preferably without redoing the
# whole autogen/configure/make process every time.
LIBUDIS86 = udis86/install/lib/libudis86.a
LDDLIBS = $(addprefix -l,$(DLIBS))

LDFLAGS = -shared -Wl,-Bstatic $(LIBUDIS86) -Wl,-Bdynamic $(LDDLIBS)

default: libhotpatch.so

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

libhotpatch.so: libhotpatch.o
	$(CC) $(CFLAGS) -Wl,-soname,$@ -o $@ $^ $(LDFLAGS)

.PHONY: clean
clean:
	rm -f *.o libhotpatch.so
