unsigned int square(unsigned int x)
/*@ 
  Require emp
  Ensure emp
*/
{
  /*@ x == 1 && x > 0 && x >= 1 && x < 2 && x <= 2 && x != 0 && emp */
  x = x + (unsigned int)1;
  return x * x;
  while (1) {
    break;
  }
}

int f() {}
