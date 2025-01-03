#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"
#include "safeexec_def.h"
#include "nested_critical_def.h"

/*@ Extern Coq (atomic_rev: program (list Z -> Prop) unit)
               (LastSeen: list Z -> (list Z -> Prop) -> Prop)
 */

struct list * * p;

int int_save()
/*@ spec1
    With (l: list Z)
    Require Critical(nil, l)
    Ensure exists l0, RTrans(l, l0) && Critical(cons(__return, nil), l0) * os_inv(l0)
*/
;

int int_save()
/*@ spec2
    With (r: list Z) (l: list Z)
    Require Critical(r, l)
    Ensure Critical(cons(__return, r), l)
*/
;

void int_restore(int x)
/*@ spec1
    With (l1: list Z) (l2: list Z)
    Require GTrans(l1, l2) && Critical(cons(x, nil), l1) * os_inv(l2)
    Ensure Critical(nil, l2)
*/
;

void int_restore(int x)
/*@ spec2
    With (r: list Z) (l1: list Z)
    Require Critical(cons(x, r), l1)
    Ensure Critical(r, l1)
*/
;

struct list *reverse(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
;

void atomic_rev1()
/*@ With (l1: list Z)
    Require Critical(nil, l1)
    Ensure exists l2, Critical(nil, l2)
*/
{
  int x = int_save() /*@ where (spec1) */;
  /*@ exists l, os_inv(l) 
      which implies
      sll(* p, l) */
  * p = reverse(* p);
  /*@ exists rev_l, sll(* p, rev_l)
      which implies
      os_inv(rev_l) */
  int_restore(x) /*@ where (spec1) */;
}

void atomic_rev2()
/*@ With l1 X
    Require safeExec(LastSeen(l1), atomic_rev, X) && Critical(nil, l1)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && Critical(nil, l2)
*/
{
  int x = int_save() /*@ where (spec1) */;
  int y = int_save() /*@ where (spec2) */;
  /*@ exists l, os_inv(l) 
      which implies
      sll(* p, l) */
  * p = reverse(* p);
  /*@ exists rev_l, sll(* p, rev_l)
      which implies
      os_inv(rev_l) */
  int_restore(y) /*@ where (spec2) r = cons(x, nil) */;
  int_restore(x) /*@ where (spec1) */;
}
