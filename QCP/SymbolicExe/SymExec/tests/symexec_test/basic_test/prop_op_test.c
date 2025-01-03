/*@ Let binop_test(x, y) = 
      ((x == y + y) && emp) ||
      (exists t, (x < t && y == t * 2 && x != t) && emp) ||
      ((x < y && x <= y && x == y && y > x && y >= x) && emp)
 */

int test_func(int x, int y)
/*@ Require ((x == y + y) && emp) ||
      (exists t, (x < t && y == t * 2 && x != t) && emp) ||
      ((x < y && x <= y && x == y && y > x && y >= x) && emp)
    Ensure __return == 0 && emp
 */   
{
   //@ binop_test(x, y) && emp
   return 0;
}