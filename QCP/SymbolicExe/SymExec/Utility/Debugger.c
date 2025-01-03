// #include <execinfo.h>
#include <stdio.h>
#include <stdlib.h>
#include "Debugger.h"

// to make a "address points to the zero page" and -fsanitize=address will show the stacktrace :)
void print_stacktrace() {
   int * x = NULL;
   *x = 1;
   // int size = 16;
   // void * array[16];
   // int stack_num = backtrace(array, size);
   // char ** stacktrace = backtrace_symbols(array, stack_num);
   // fprintf(stderr, "\n");
   // for (int i = 0; i < stack_num; ++i) {
   //    fprintf(stderr, "%s\n", stacktrace[i]);
   // }
   // free(stacktrace);
}
