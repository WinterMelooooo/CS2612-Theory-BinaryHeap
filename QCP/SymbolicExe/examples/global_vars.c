#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "sll_def.h"

int x;

void add(int t)
/*@ Require 0 < x && x < 200 && 0 < t && t < 100 && emp
    Ensure  x == x@pre + t && emp
*/
{
   x = x + t;
}

void add_call()
/*@ Require 0 < x && x < 100 && emp
    Ensure  x == x@pre + 6 && emp
*/
{
   add(1);
   add(2);
   add(3);
}

void add_rec(int n)
/*@ Require 0 <= x && 0 <= n && x + n <= 100 && emp
    Ensure  x == x@pre + n && emp
*/
{
   if (n == 0) return;
   x = x + 1;
   add_rec(n - 1);
}

int n, *a;

int array_sum()
/*@ With l
    Require 0 < n && n < 100 && store_int_array(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && store_int_array(a, n, l)
*/
{
   int i;
   i = 0;
   int ret;
   ret = 0;
   /*@ Inv
         0 <= i && i <= n && n == n@pre && ret == sum(sublist(0, i, l))
   */
   while (i < n) {
      ret += a[i];
      ++i;
   }
   return ret;
}

int array_sum_call()
/*@ With l
    Require 0 < n && n < 100 && store_int_array(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && store_int_array(a, n, l)
*/
{
   return array_sum();
}

struct list *p;

struct list *reverse()
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure  undef_data_at(&p) * sll(__return, rev(l))
*/
{
   struct list * w = (void *) 0, * v = p;
   /*@ Inv exists l1 l2,
            l == app(rev(l1), l2) &&
            sll(w, l1) * sll(v, l2)
      */
   while (v) {
      /*@ exists l2, v != 0 && sll(v, l2)
          which implies
          exists l2_new, l2 == cons(v -> data, l2_new) && sll(v -> next, l2_new)
      */
      struct list * t = v -> next;
      v -> next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *reverse_call()
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure  undef_data_at(&p) && sll(__return, l)
*/
{
   p = reverse();
   p = reverse();
   return p;
}
