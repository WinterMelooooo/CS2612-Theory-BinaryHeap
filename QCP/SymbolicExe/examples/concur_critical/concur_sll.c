#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"
#include "safeexec_def.h"
#include "critical_def.h"

/*@ Extern Coq (atomic_rev: program (list Z -> Prop) unit)
               (LastSeen: list Z -> (list Z -> Prop) -> Prop)
 */

struct list * * p;

void enter_critical()
/*@ With (l: list Z)
    Require OutsideCritical(l)
    Ensure exists l0, RTrans(l,l0) && InsideCritical(l0) * os_inv(l0)
*/
;

void exit_critical()
/*@ With (l1: list Z) (l2: list Z)
    Require GTrans(l1, l2) && InsideCritical(l1) * os_inv(l2)
    Ensure OutsideCritical(l2)
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
    Require OutsideCritical(l1)
    Ensure exists l2, OutsideCritical(l2)
*/
{
  enter_critical();
  /*@ exists l, os_inv(l) 
      which implies
      sll(* p, l) */
  * p = reverse(* p);
  /*@ exists rev_l, sll(* p, rev_l)
      which implies
      os_inv(rev_l) */
  exit_critical();
}

void atomic_rev2()
/*@ With l1 X
    Require safeExec(LastSeen(l1), atomic_rev, X) && OutsideCritical(l1)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && OutsideCritical(l2)
*/
{
  enter_critical();
  /*@ exists l, os_inv(l) 
      which implies
      sll(* p, l) */
  * p = reverse(* p);
  /*@ exists rev_l, sll(* p, rev_l)
      which implies
      os_inv(rev_l) */
  exit_critical();
}
