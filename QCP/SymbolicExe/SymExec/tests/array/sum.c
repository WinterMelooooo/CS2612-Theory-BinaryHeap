/*@ Extern Coq (INT_MAX : Z)
               (sum : list Z -> Z) 
               (sublist : list Z -> Z -> Z -> list Z)
               (store_int_array : Z -> list Z -> Assertion)
*/

int arr_sum(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && store_int_array(a, n, l) && forall i, 0 <= l[i] && l[i] < 100
    Ensure  __return == sum(l) && store_int_array(a, n, l)
*/
{
  int i;
  i = 0;
  int ret;
  ret = 0;
  /*@ Inv
      0 <= i && i <= n && ret == sum(sublist(l, 0, i - 1))
  */
  while (i < n) {
    ret += a[i];
    ++i;
  }
  return ret;
}
