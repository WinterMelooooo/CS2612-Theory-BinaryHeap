//@ Export Coq Goal "swap.v"
//@ Export Coq Proof "swap.v"

void swap(int *x, int *y) 
/*@ With a b
    Require data_at(x, a) * data_at(y, b)
    Ensure  data_at(x, b) * data_at(y, a)
*/
{
   int t;
   t = *x;
   *x = *y;
   *y = t;
}
