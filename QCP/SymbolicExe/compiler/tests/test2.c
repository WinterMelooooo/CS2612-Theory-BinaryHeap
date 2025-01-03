/*@ Let is_pow(x, n, y) =
  n == 0 && y == 1 ||
  exists z,
    is_pow(x, n - 1, z) && x * z == y
*/

unsigned int square(unsigned int x)
/*@
  Require emp
  Ensure __return == x * x
*/
{
  return x * x;
}

unsigned int pow(unsigned int x, unsigned int n)
/*@
  Require emp
  Ensure is_pow(x, n, __return)
*/
{
  if (n == (unsigned int)0)
    return (unsigned int)1;
  if (n % (unsigned int)2 == (unsigned int)0)
    return square(pow(x, n / (unsigned int)2));
  return x * pow(x, n - (unsigned int)1);
}
