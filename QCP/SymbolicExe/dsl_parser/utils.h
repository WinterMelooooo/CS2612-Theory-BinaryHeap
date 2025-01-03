#ifndef UTILS_H
#define UTILS_H

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define PREAKPOINT() {fprintf(stderr,"!!!\n");fflush(stderr);}

extern void *__current_scanner;
int llget_lineno ();
int llget_column ();

#define failwith(...)                                                   \
  {                                                                     \
    fprintf(stderr, "\e[1;31mfatal error:\e[0m " __VA_ARGS__);          \
    if (__current_scanner != NULL)                                      \
      fprintf(stderr, " around line %d, column %d.",                    \
              llget_lineno(),                          \
              llget_column());                         \
    exit(1);                                                            \
  }

#ifdef DEBUG
#define assert(e) { if (!(e)) failwith("compiler internal error at file %s, line %d", __FILE__, __LINE__); }
#else
#define assert(e) { exit(1); }
#endif

#endif