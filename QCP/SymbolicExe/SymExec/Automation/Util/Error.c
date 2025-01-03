#include "Error.h"

void ERROR(const char * msg) {
    fprintf(stderr, "%s\n", msg);
    // int * p;
    // *p = 0;
    exit(1);
}