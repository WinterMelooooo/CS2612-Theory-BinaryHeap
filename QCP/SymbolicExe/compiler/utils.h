#ifndef UTILS_H
#define UTILS_H

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define PREAKPOINT() {fprintf(stderr,"!!!\n");fflush(stderr);}

extern void *__current_scanner;
extern char *__current_file;
int yyget_lineno (void * yyscanner);
int yyget_column  ( void * yyscanner );

#define failwith(...)                                                   \
  {                                                                     \
    fprintf(stderr, "\e[1;31mfatal error: \e[0m" __VA_ARGS__);           \
    fprintf(stderr, " ");                                               \
    if (__current_file != NULL)                                         \
      fprintf(stderr, "in %s:", __current_file);                        \
    if (__current_scanner != NULL)                                      \
      fprintf(stderr, "%d:%d",                                          \
              yyget_lineno(__current_scanner),                          \
              yyget_column(__current_scanner));                         \
    exit(1);                                                            \
  }

#ifdef DEBUG
#define assert(e) { if (!(e)) failwith("compiler internal error at file %s, line %d", __FILE__, __LINE__);  }
#else
#define assert(e) { }
#endif

unsigned long long build_nat(char *c, int len);
unsigned long long build_hex(char *c, int len);
char *new_str(char *str, int len);
char *new_identifier(char *str, int len);
char *clone_str(char *str);
char *embed_str(char *fmt, char *str);
char *embed_int(char *fmt, int n);
void print_escaped_str(char *str);
void print_escaped_str_File(FILE *f, char *str);

int roundup(int x, int gran);
void print_subscript(unsigned int x);

int cast_void(void *x);
void *cast_int(int x);

char *find_file_in_same_dir(char *file, char *relative);
char *find_file_in_search_path(char *file, char *relative);

#endif
