#include "../verification_stdlib.h"

/*@ Extern Coq (factorial: Z -> Z) */

int fac(int n)
/*@ Require 1 <= n && n <= 10
    Ensure  __return == factorial(n)
*/
{
   int ans = 1;
   int i = 0;
   do {
      ++i;
      ans *= i;
   } /*@ Inv ans == factorial(i) && 1 <= i && i <= n && n == n@pre */ while (i != n);
   return ans;
}

*/