void ptr_add(int *p)
/*@ With vp
    Require 0 <= vp && vp <= 100 && ((*{int}p) == vp)
    Ensure ((*{int}p) == vp + 1)
*/
{
   (*p)++;
}