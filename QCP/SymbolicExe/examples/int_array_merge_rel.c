#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "safeexec_def.h"


/*@ Import Coq Require Import int_array_merge_rel_lib */
/*@ Extern Coq 
               (maketuple: list Z -> list Z ->  ((list Z) * (list Z)))
               (merge_rel: list Z -> list Z -> program unit (list Z))
               (merge_from_mid_rel: list Z -> list Z -> list Z -> program unit (list Z))
               (gmergesortrec: list Z -> program unit (list Z))
               (gmergesortrec_loc0: ((list Z) * (list Z)) -> program unit (list Z))
               (gmergesortrec_loc1: list Z -> list Z -> program unit (list Z))
                */


void merge(int *arr, int p, int q, int r, int *ret) 
/*@ With s1 s2 l0 X
  Require safeExec(ATrue, merge_rel(s1, s2), X) && 
          0 <= p && p <= q && 
          q < r && r + 1 <= INT_MAX &&
          store_int_array_rec(arr, p, q + 1, s1) * 
          store_int_array_rec(arr, q + 1, r + 1, s2) * 
          store_int_array_rec(ret, p, r + 1, l0) 
  Ensure exists s3 l1, safeExec(ATrue, return(s3), X) && 
          store_int_array_rec(arr, p, r + 1, l1) * 
          store_int_array_rec(ret, p, r + 1, s3)
*/
{

  int i = p;
  int j = q + 1;
  int k = p;

  /*@ Inv 
      exists l1 l2 l3 l4 l5 l6,
        safeExec(ATrue, merge_from_mid_rel(l1, l2, l3), X) && 
        p == p@pre && q == q@pre && r == r@pre &&
        arr == arr@pre && ret == ret@pre && 
        p <= i &&
        q + 1 <= j &&       
        k == p + (i - p) + (j - (q + 1)) &&
        store_int_array_rec(arr, p, i, l4) * 
        store_int_array_rec(arr, i, q + 1, l1) * 
        store_int_array_rec(arr, q + 1, j, l5) * 
        store_int_array_rec(arr, j, r + 1, l2) * 
        store_int_array_rec(ret, p, k, l3) *
        store_int_array_rec(ret, k, r + 1, l6) 
  */
  while (i < q + 1 && j < r + 1) {
    if (arr[i] <= arr[j]) {
      ret[k] = arr[i];
      i++;
    } else {
      ret[k] = arr[j];
      j++;
    }
    k++;
  }


  /*@ Assert Inv 
        exists l1 l2 l3 l4 l5 l6,
          safeExec(ATrue, merge_from_mid_rel(l1, l2, l3), X) && 
          p == p@pre && q == q@pre && r == r@pre &&
          arr == arr@pre && ret == ret@pre && 
          0 <= p && p <= q && 
          q < r  && r + 1 <= INT_MAX &&
          p <= i &&
          q + 1 <= j &&
          k == p + (i - p) + (j - (q + 1)) && 
          (i == q + 1 || j == r + 1) &&
          store_int_array_rec(arr, p, i, l4) * 
          store_int_array_rec(arr, i, q + 1, l1) * 
          store_int_array_rec(arr, q + 1, j, l5) * 
          store_int_array_rec(arr, j, r + 1, l2) * 
          store_int_array_rec(ret, p, k, l3) *
          store_int_array_rec(ret, k, r + 1, l6) 
  */
  while (i < q + 1) {
    ret[k] = arr[i];
    i++;
    k++;
  }

  /*@ Assert Inv 
        exists l2 l3 l4 l5 l6,
          safeExec(ATrue, merge_from_mid_rel(nil, l2, l3), X) && 
          p == p@pre && q == q@pre && r == r@pre &&
          arr == arr@pre && ret == ret@pre && 
          0 <= p && p <= q && 
          q < r && r + 1 <= INT_MAX &&
          p <= i &&
          q + 1 <= j &&
          k == p + (i - p) + (j - (q + 1)) && 
          i == q + 1 && 
          store_int_array_rec(arr, p, i, l4) * 
          store_int_array_rec(arr, q + 1, j, l5) * 
          store_int_array_rec(arr, j, r + 1, l2) * 
          store_int_array_rec(ret, p, k, l3) *
          store_int_array_rec(ret, k, r + 1, l6) 
  */
  while (j < r + 1) {
    ret[k] = arr[j];
    j++;
    k++;
  }


}

void  mergeSort(int *arr, int l, int r, int *ret) 
  /*@ low_level_spec_aux <= low_level_spec
      With {B} l0 (c: list Z -> program unit B) X
      Require safeExec(ATrue, bind(gmergesortrec(l0), c), X) &&
              0 <= l && l <= r && r + 1 <= INT_MAX &&
              store_int_array_rec(arr, l, r + 1, l0) *
              store_int_array_rec(ret, l, r + 1, l0)
      Ensure exists l1 l2,
              safeExec(ATrue, applyf(c, l1), X) && 
              store_int_array_rec(arr, l, r + 1, l2) *
              store_int_array_rec(ret, l, r + 1, l1)
   */
;


void mergeSort(int *arr, int l, int r, int *ret) 
/*@ low_level_spec
      With s1 X
      Require safeExec(ATrue, gmergesortrec(s1), X) && 
              0 <= l && l <= r && r + 1 <= INT_MAX &&
              store_int_array_rec(arr, l, r + 1, s1) *
              store_int_array_rec(ret, l, r + 1, s1)
      Ensure exists s2 s3,
              safeExec(ATrue, return(s2), X) &&
              store_int_array_rec(arr, l, r + 1, s3) *
              store_int_array_rec(ret, l, r + 1, s2) 
*/
{
  if (l < r) {
    int m = l + (r - l) / 2;

    /*@ Assert
        exists l1 l2, safeExec(ATrue, bind(gmergesortrec(l1), gmergesortrec_loc1(l2)), X) && 
                      arr == arr@pre && ret == ret@pre && l == l@pre && r == r@pre &&
                      0 <= l && l <= r && r + 1 <= INT_MAX &&
                      l < r &&
                      l <= m  && m < r && 
                      store_int_array_rec(arr, l, m + 1, l1)  *
                      store_int_array_rec(arr, m + 1, r + 1, l2) *
                      store_int_array_rec(ret, l, m + 1, l1)  *
                      store_int_array_rec(ret, m + 1, r + 1, l2)     */
    mergeSort(ret, l, m, arr) /*@ where(low_level_spec_aux) X = X  ; B = (list Z) */;

     /*@ exists l1 l2 l3, safeExec(ATrue, bind(gmergesortrec(l2), mergesortrec_loc2(l1)), X) && 
                      store_int_array_rec(arr, l, m + 1, l1)  *
                      store_int_array_rec(arr, m + 1, r + 1, l2) *
                      store_int_array_rec(ret, l, m + 1, l3)  *
                      store_int_array_rec(ret, m + 1, r + 1, l2)   */
    mergeSort(ret, m + 1, r, arr) /*@ where(low_level_spec_aux) X = X ; B = (list Z) */;

     /*@ exists s1 s2 l0, safeExec(ATrue, merge_rel(s1, s2), X) && 
                      store_int_array_rec(arr, l, m + 1, s1) * 
                      store_int_array_rec(arr, m + 1, r + 1, s2) * 
                      store_int_array_rec(ret, l, r + 1, l0)    */
    merge(arr, l, m, r, ret) /*@ where X = X  */;



  }
}