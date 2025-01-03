/*@ Import Coq Import naive_C_Rules CRules */

/*@ Extern Coq (INT_MAX : Z)
               (INT_MIN : Z) */

int slow_add(int x, int y)
/*@ Require
      0 <= x && x <= 100 && 
      0 <= y && y <= 100 && emp
    Ensure
      __return == x + y && emp
  */
{
  return x == 0 ? y : 1 + slow_add(x - 1, y);
}

int max2(int x, int y)
/*@ Require
      INT_MIN <= x && x <= INT_MAX &&
      INT_MIN <= y && y <= INT_MAX && emp
    Ensure 
      __return >= x && __return >= y && emp
*/
{
  return x >= y ? x : y;
}

int max3_a(int x, int y, int z)
/*@ Require
      INT_MIN <= x && x <= INT_MAX &&
      INT_MIN <= y && y <= INT_MAX &&
      INT_MIN <= z && z <= INT_MAX && emp
    Ensure
      __return >= x &&
      __return >= y &&
      __return >= z && emp
  */
{
  return x < y ? (y < z ? z : y) : (x < z ? z : x);
}

int max3_b(int x, int y, int z)
/*@ Require
      INT_MIN <= x && x <= INT_MAX &&
      INT_MIN <= y && y <= INT_MAX &&
      INT_MIN <= z && z <= INT_MAX && emp
    Ensure
      __return >= x &&
      __return >= y &&
      __return >= z && emp
  */
{
  return x < y ? max2(y, z) : max2(x, z);
}