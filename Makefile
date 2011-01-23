
# TODO: build libudis86 automatically...preferably without redoing the
# whole autogen/configure/make process every time.
UDIS86DIR = udis86/install
LIBUDIS86 = $(UDIS86DIR)/lib/libudis86.a
UDIS86INC = $(UDIS86DIR)/include

CC = gcc
CWARN = -Wall -Wextra -Wno-sign-compare
CDEBUG = -ggdb3
COPT = -O0
CINCLUDE = -I$(UDIS86INC)
CFLAGS = $(CWARN) $(CDEBUG) $(COPT) $(CINCLUDE) -fPIC -fvisibility=hidden

DLIBS = dl elf
LDDLIBS = $(addprefix -l,$(DLIBS))
LDFLAGS = -shared $(LDDLIBS)

default: libhotpatch.so

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

libhotpatch.so: libhotpatch.o
	$(CC) $(CFLAGS) -Wl,-soname,$@ -o $@ $^ $(LIBUDIS86) $(LDFLAGS)

.PHONY: clean
clean:
	rm -f *.o libhotpatch.so
