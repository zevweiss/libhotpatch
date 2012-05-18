libhotpatch
===========

libhotpatch implements hot-patching (as its name implies) of code at
program load time.  It is a shared library intended for use via
`LD_PRELOAD` (actually linking against it won't do you much good).
Currently it patches `syscall` instructions, replacing them with
branches to dynamically-generated trampolines from which the
instruction is actually executed, and which then branch back to the
patch-point.


## How it Works

Its mechanism for achieving this is a bit...unusual, I suppose.  It
exploits (and depends on) gcc's tendency to create binaries with
little pads of no-ops scattered throughout them (a result of gcc's
`-falign-*` flags).  Since a `syscall` instruction is only two bytes and
we need a 5-byte branch to reach the trampolines, it attempts to
string together sequences of two-bytes jumps until it reaches a no-op
pad large enough to accommodate a 5-byte `jmp`, threading a chain of
"stepping stones" through the spaces left by the compiler.  Early
results indicate (somewhat surprisingly, to me) that this actually
works most of the time, allowing most patching to be done in a
minimally-invasive manner.

For the cases where it can't quite pull this off, a "clobber-patch" is
used: it simply writes a 5-byte instruction over a 2-byte one, and
relocates the clobbered instructions into the trampoline, translating
them as necessary if they are position-dependent.  This also
introduces further complications if any clobbered instruction is the
target of a branch somewhere else in the code -- that branch must then
be retargeted to point to the relocated instruction, which in turn can
introduce another round of clobbering...so the patching process
iterates until there are no "outstanding" clobbers.

## Usage Notes

To use libhotpatch, put the absolute path to libhotpatch.so in the
environment variable `LD_PRELOAD` of the program to patch.  If you're
using bash, you can do this by simply prefixing your command with
`LD_PRELOAD=/path/to/libhotpatch.so`, but if your shell doesn't
support this syntax, `env` is an easy alternative.  You could of
course just `export LD_PRELOAD=/path/to/libhotpatch.so`, but then it
would be used on *everything* that inherits that environment, which
might not be what you want.

A few other environment variables also affect the behavior of
libhotpatch:

- `LIBHOTPATCH_LOGPATH`: the path to a file to which libhotpatch will
  print any output of its own.  This defaults to `/proc/self/fd/2`,
  a.k.a. stderr; set it to `/dev/null` to shut it up.

- `LIBHOTPATCH_SKIP`: a list of patterns to skip when scanning and
  patching DSOs.  These are matched against the absolute paths of the
  DSOs in the address space of the process via `fnmatch(3)`, so you
  can use shell glob patterns to specify e.g. `/usr/lib/*`.  Note
  though that slashes *are* matched by `*`, unlike a shell glob.  If
  the first character of `LIBHOTPATCH_SKIP` is `!`, matching of all
  patterns is inverted and only DSOs *not* matching any of the
  patterns specified in the rest of the variable will be skipped.
  Patterns may be separated by spaces, tabs, newlines, or colons.

## Plans for future development

- Provide more useful information to tracing function (e.g. a pointer
  to a modifiable struct describing machine state, which would be
  restored before resumption of the patched code).

- Allow a user-supplied predicate function to determine which
  instructions to patch.

- Implement lazy patching: at initialization, just mark code sections
  no-execute; then catch the SIGSEGV when execution hits them, patch
  that page, and re-enable execution on it.  I think this may be
  slightly more complicated than it would appear at first glance.

Hopefully I'll remember to update this as it progresses.


## Support

libhotpatch has been developed and tested exclusively on x86-64 Linux.
Any functionality on other platforms is purely coincidental (and
highly unlikely).


## Build

First acquire libudis86: run `git submodule update --init` in the
top-level directory of the libhotpatch git tree.

Then build libudis86: `cd` to the `udis86` directory and run the
following commands:

    $ ./autogen.sh
    $ ./configure --prefix=$PWD/installroot/ --disable-shared CFLAGS='-fPIC -fvisibility=hidden'
    $ make
    $ make install

Finally, just run `make` in the top-level directory.


## Acknowledgments

libhotpatch makes extensive use of Vivek Thampi's udis86 library for
x86-64 disassembly.


## Author

Zev Weiss  
<zevweiss@gmail.com>


## License

libhotpatch is released under the terms of the GPL, version 2.
