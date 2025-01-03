//@ Extern Coq (T U V :: *) (L M N :: * => *)
//@ Extern Coq (t1 t2 t3 : T) (mt1 mt2 mt3 : M T)

/*@ Let f({A, B, C :: *}; a : A, b : B, c : C) = emp */

int g()
/*@ With {A B C :: *} {D E F :: * => *}
         (a aa aaa : A) (x xx xxx : D A)
    Require exists (n m p : A), n == m && m == p
    Ensure sizeof(int) == 4
 */
{
  int n = 0;
  int m = 1;
  /*@ n == 0 ... */
  /*@ n == 0 && m == 1 */
  /*@ Inv n == 0 ... */
  while (1) {
    m++;
  }
  /*@ Inv n == 0 && m == m */
  while (1) {
    m--;
  }
  return 0;
}

