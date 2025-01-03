#include "Util.h"

char * createString(const char * str) {
    char * newStr = (char *)malloc(sizeof(char) * (strlen(str) + 1));
    strcpy(newStr, str);
    return newStr;
}