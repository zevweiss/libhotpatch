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

default: lib752.so

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

lib752.so: lib752.o
	$(CC) $(CFLAGS) -Wl,-soname,$@ -o $@ $^ $(LDFLAGS)

.PHONY: clean
clean:
	rm -f *.o lib752.so
