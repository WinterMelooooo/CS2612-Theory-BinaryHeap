int test(int x) 
/*@ With v
    Require 1 < v && v < 10 && x == v && emp
    Ensure  __return == v + 1 && emp
*/
{
  x = x + 1;
  return x;
}