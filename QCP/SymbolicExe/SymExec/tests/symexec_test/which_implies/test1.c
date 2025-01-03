void test(int *x, int *y)
/*@ With a b 
    Require data_at(x, a) * data_at(y, b)
    Ensure  data_at(x, a) * data_at(y, b)
*/
{
   /*@ (exists t, data_at(x, t)) || (exists r, data_at(y, r))
       which implies 
       (x != 0 && data_at(x, t)) || (y != 0 && data_at(y, r)) */
}