#include "../verification_stdlib.h"

/*@ Extern Coq (Zgcd: Z -> Z -> Z)
               (Zabs: Z -> Z) */

int abs(int x)
  /*@ Require
        INT_MIN < x &&
        x <= INT_MAX && emp
      Ensure
        __return == Zabs(x) && emp
   */
;

int gcd(int x, int y)
  /*@ Require
        INT_MIN < x && x <= INT_MAX &&
        INT_MIN < y && y <= INT_MAX && emp
      Ensure
        __return == Zgcd(x,y) && emp
   */
{
  if (y == 0)
  {
    return abs(x);
  }
  else {
    return gcd(y, x % y);
  }
}
