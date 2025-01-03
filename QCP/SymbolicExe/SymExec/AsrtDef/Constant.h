#ifndef CONSTANT_INCLUDED
#define CONSTANT_INCLUDED

#include <stdio.h>
#include <stdlib.h>
#include "string.h"
struct Constant {
  int pos; // positive : 1 , negative : 0
  int * val;
  int size;
};

unsigned long long abs_number_of_Constant(struct Constant *c);

struct Constant * Constant_number(unsigned long long number);

struct Constant * Constant_neg(struct Constant * c);

struct Constant * Constant_not(struct Constant * c);

struct Constant * Constant_nint(struct Constant * c);

struct Constant * Constant_add(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_sub(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_mul(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_div(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_mod(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_and(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_or(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_xor(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_shl(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_shr(struct Constant * c1, struct Constant * c2);

struct Constant * Constant_ZPOW(struct Constant *c1, struct Constant *c2);

struct Constant * Constant_LNB(struct Constant *c1, struct Constant *c2);

struct Constant *Constant_ULNB(struct Constant *c1, struct Constant *c2);

int ConstantAbsCompare(struct Constant *c1, struct Constant *c2);

void ConstantPrint(struct Constant * c);

void ConstantFree(struct Constant *c);

struct Constant *ConstantDeepCopy(struct Constant *c);

#endif