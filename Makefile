CC = gcc
CWARN = -Wall
CDEBUG = -ggdb3
COPT = -O0
CFLAGS = $(CWARN) $(CDEBUG) $(COPT) -fPIC

default: lib752.so

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

lib752.so: lib752.o
	$(CC) $(CFLAGS) -shared -Wl,-soname,$@ -o $@ $^ -ldl -Wl,-Bstatic -ludis86 -Wl,-Bdynamic

.PHONY: clean
clean:
	rm *.o lib752.so
