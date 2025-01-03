This directory contains the SAC front end.

The parser recognizes pieces of programs, in somewhat inconsistent
granularities, and build the whole syntax tree on the fly. This enables
incremental or interactive use of the front end.

To build, enter 'mkdir build && cd build && cmake .. && make -j4 test'. The
program is read from stdin.
