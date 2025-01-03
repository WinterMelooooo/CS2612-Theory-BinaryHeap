#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"
#include "safeexec_def.h"
#include "guarded_critical_def.h"

/*@ Extern Coq (atomic_rev_twice: program (list Z -> Prop) unit)
               (LastSeen: list Z -> (list Z -> Prop) -> Prop)
 */

struct list * * p;

void enter_critical()
/*@ With (q: Z) (l: list Z)
    Require OutsideCritical(q, l)
    Ensure exists q0 l0,
             RTrans_C(q, l, q0, l0) &&
             InsideCritical(q0, l0) * os_inv(q0, l0)
*/
;

void exit_critical()
/*@ With (q1: Z) (l1: list Z) (q2: Z) (l2: list Z)
    Require GTrans_C(q1, l1, q2, l2) &&
            InsideCritical(q1, l1) * os_inv(q2, l2)
    Ensure OutsideCritical(q2, l2)
*/
;

struct list *reverse(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
;

void atomic_rev_twice1()
/*@ With (q: Z) (l1: list Z)
    Require p == q && OutsideCritical(q, l1)
    Ensure exists l2, p == q && OutsideCritical(q, l2)
*/
{
    enter_critical();
    /*@ exists l, os_inv(q, l) 
      which implies
      sll(* (struct list *) q, l) */
    * p = reverse(* p);
     /*@ exists rev_l, sll(* (struct list *) q, rev_l)
      which implies
      os_inv(q, rev_l) */
    exit_critical();
    enter_critical();
    /*@ exists l, os_inv(q, l) 
      which implies
      sll(* (struct list *) q, l) */
    * p = reverse(* p);
    /*@ exists rev_l2, sll(* (struct list *) q, rev_l2)
      which implies
      os_inv(q, rev_l2) */
    exit_critical();
}

void atomic_rev_twice2()
/*@ With (q: Z) (l1: list Z) X
    Require safeExec(LastSeen(l1), atomic_rev_twice, X) && p == q && OutsideCritical(q, l1)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && p == q && OutsideCritical(q, l2)
*/
{
    enter_critical();
    /*@ exists l, os_inv(q, l) 
      which implies
      sll(* (struct list *) q, l) */
    * p = reverse(* p);
    /*@ exists rev_l, sll(* (struct list *) q, rev_l)
      which implies
      os_inv(q, rev_l) */
    exit_critical();
    enter_critical();
    /*@ exists l, os_inv(q, l) 
      which implies
      sll(* (struct list *) q, l) */
    * p = reverse(* p);
    /*@ exists rev_l2, sll(* (struct list *) q, rev_l2)
      which implies
      os_inv(q, rev_l2) */
    exit_critical();
}