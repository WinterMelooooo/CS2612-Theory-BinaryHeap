#include "verification_stdlib.h"
#include "verification_list.h"
#include "fieldtest_def.h"


int f(int *x, int *y)
/*@ With (p : IntPair)
    Require IntPairSep(x, y, p) && (p.a)(1) == 1 && (p.b)(1) == 2
    Ensure  __return == (p.a)(1) + (p.b)(1) && IntPairSep(x, y, p)*/
{
  while (*x > 2) {
    *x = 2;
    while (1) {
      break;
    }
  }
  return *x + *y;
}


int g(int *x)
/*@ With (p : IntPair)
    Require IntPairSep2(x, p) && (p.a)(1) == 1 && (p.b)(1) == 2
    Ensure  __return == (p.a)(1) + (p.b)(1) && IntPairSep2(x, p)*/
{
  while (*x > 2) {
    *x = 2;
    while (1) {
      break;
    }
  }
  return *x + z;
}

int g2(int *x)
/*@ With {A} (p : Pair A) (a0 b0 : A)
    Require IntPairSep3(x, p, a0, b0) && (p.a1)(a0) == 1 && (p.b1)(b0) == 2
    Ensure  __return == (p.a1)(a0) + (p.b1)(b0) && IntPairSep3(x, p, a0, b0)*/
{
  while (*x > 2) {
    *x = 2;
    while (1) {
      break;
    }
  }
  return *x + z;
}

int g3(int *x)
/*@ With (p : Pair0)
    Require IntPairSep4(x, p) && p.a2 == 1 && p.b2 == 2
    Ensure  __return == p.a2 + p.b2 && IntPairSep4(x, p)*/
{
  while (*x > 2) {
    *x = 2;
    while (1) {
      break;
    }
  }
  return *x + z;
}