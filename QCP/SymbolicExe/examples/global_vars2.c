#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "sll_def.h"

/*@ include strategies "global_vars.strategies" */

struct array_box{
   int n;
   int *a;
};

struct array_box arr;

int array_box_sum()
/*@ With n l
    Require store_array_box(&arr, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && store_array_box(&arr, n, l)
*/
{
   int i;
   i = 0;
   int ret;
   ret = 0;
   /*@ Inv
         0 <= i && i <= n && ret == sum(sublist(0, i, l))
   */
   while (i < arr.n) {
      ret += arr.a[i];
      ++i;
   }
   return ret;
}

int a[100];

int global_array_sum()
/*@ With (l : list Z)
    Require store_int_array(a, 100, l) && (forall (i: Z), (0 <= i && i < 100) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && store_int_array(a, 100, l)
*/
{
   int i;
   i = 0;
   int ret;
   ret = 0;
   /*@ Inv
         0 <= i && i <= 100 && ret == sum(sublist(0, i, l))
   */
   while (i < 100) {
      ret += a[i];
      ++i;
   }
   return ret;
}

struct array_box_array {
   int a[100];
};

struct array_box_array arr_box;

int array_box_array_sum()
/*@ With (l : list Z)
    Require store_array_box_array(&arr_box, l) && (forall (i: Z), (0 <= i && i < 100) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && store_array_box_array(&arr_box, l)
*/
{
   int i;
   i = 0;
   int ret;
   ret = 0;
   /*@ Inv
         0 <= i && i <= 100 && ret == sum(sublist(0, i, l))
   */
   while (i < 100) {
      ret += arr_box.a[i];
      ++i;
   }
   return ret;
}

// struct array_box boxes[100];

// int array_box_sum2(struct array_box *box)
// /*@ With n l
//     Require store_array_box(box, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
//     Ensure  __return == sum(l) && store_array_box(box, n, l)
// */;

// int array_array_box_sum()
// /*@ 
// */