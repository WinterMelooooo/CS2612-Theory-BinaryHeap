#include "../verification_stdlib.h"


int local(unsigned int x, int y) 
/*@ Require emp 
    Ensure __return >= INT_MIN && __return <= INT_MAX
*/
{
  /*@ x >= 0 && y >= INT_MIN && y <= INT_MAX by local*/
  if (y >= 0 && x <= 100)
    return y - (int)x;
  return 0;
}


unsigned int local2(unsigned int x)
/*@ Require emp
    Ensure __return == unsigned_last_nbits(2 * x + 1, 32)
*/
{
  return 2 * x + 1;
}