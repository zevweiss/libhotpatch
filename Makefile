CC = gcc
CWARN = -Wall
CDEBUG = -ggdb3
COPT = -O0
CFLAGS = $(CWARN) $(CDEBUG) $(COPT) -fPIC

SLIBS = udis86
DLIBS = dl elf

LDSLIBS = $(addprefix -l,$(SLIBS))
LDDLIBS = $(addprefix -l,$(DLIBS))

LDFLAGS = -shared -Wl,-Bstatic $(LDSLIBS) -Wl,-Bdynamic $(LDDLIBS)

default: libhotpatch.so

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

libhotpatch.so: libhotpatch.o
	$(CC) $(CFLAGS) -Wl,-soname,$@ -o $@ $^ $(LDFLAGS)

.PHONY: clean
clean:
	rm -f *.o libhotpatch.so
