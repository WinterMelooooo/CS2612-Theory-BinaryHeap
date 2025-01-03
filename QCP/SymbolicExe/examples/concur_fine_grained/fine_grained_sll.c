#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"
#include "safeexec_def.h"
#include "critical_def.h"

/*@ Extern Coq (atomic_rev: program (list Z -> Prop) unit)
               (atomic_push: Z -> program (list Z -> Prop) unit)
               (atomic_pop: program (list Z -> Prop) (option Z))
               (pop_add_push: program (list Z -> Prop) unit)
               (pop_add_push_loc0: option Z -> program (list Z -> Prop) unit)
 */

struct list * * p;
int flag;

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

struct list *push(struct list *p, int x) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, cons(x,l))
*/
;

int pop(struct list * * p, int * x) 
/*@ With (l: list Z)
    Require sll(* p, l) * undef_data_at(x)
    Ensure __return == 0 && l == nil && sll(* p, l) * undef_data_at(x) ||
           exists l0, __return == 1 && l == cons(*x, l0) && sll(* p, l0)
*/
;

void atomic_rev_C()
/*@ With l1 X
    Require safeExec(LastSeen(l1), atomic_rev, X) && OutsideCritical(l1)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && OutsideCritical(l2)
*/
{
  enter_critical();
  /*@ exists l, os_inv(l) 
      which implies
      conditionally_store_sll(flag, l) */
  if (flag) {
    flag = 0;
    /*@ exists l, flag == 0 && conditionally_store_sll(1, l) 
        which implies
        os_inv(rev(l)) */
  }
  else {
    flag = 1;
    /*@ exists l, flag == 1 && conditionally_store_sll(0, l) 
        which implies
        os_inv(rev(l)) */
  }
  exit_critical();
}


void atomic_push_C(int x)
/*@ With l1 X
    Require safeExec(LastSeen(l1), atomic_push(x), X) && OutsideCritical(l1)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && OutsideCritical(l2)
*/
{
  enter_critical();
  /*@ exists l, os_inv(l) 
      which implies
      conditionally_store_sll(flag, l) */
  if (flag) {
    /*@ exists l, conditionally_store_sll(1, l) 
        which implies
        sll(* p, rev(l)) */
    * p = reverse(* p);
    flag = 0;
  }
  /*@ Assert
        exists l2,
          safeExec(LastSeen(l1), atomic_push(x), X) &&
          RTrans(l1, l2) &&
          flag == 0 &&
          InsideCritical(l2) *
          sll(* p, l2) */
  * p = push(* p, x);
  /*@ exists l, flag == 0 && sll(* p, l) 
      which implies
      os_inv(l) */
  exit_critical();
}

int atomic_pop_C(int * x)
/*@ aux_spec <= normal_spec
    With {B} l1 (c: option Z -> program (list Z -> Prop) B) X
    Require safeExec(LastSeen(l1), bind(atomic_pop, c), X) && OutsideCritical(l1) * undef_data_at(x)
    Ensure (exists l2, __return == 0 && safeExec(LastSeen(l2), c(None), X) && OutsideCritical(l2) * undef_data_at(x)) ||
           (exists l2, __return == 1 && safeExec(LastSeen(l2), c(Some( * x)), X) && OutsideCritical(l2))
*/
;

int atomic_pop_C(int * x)
/*@ normal_spec
    With l1 X
    Require safeExec(LastSeen(l1), atomic_pop(), X) && OutsideCritical(l1) * undef_data_at(x)
    Ensure (exists l2, __return == 0 && safeExec(LastSeen(l2), return(None), X) && OutsideCritical(l2) * undef_data_at(x)) ||
           (exists l2, __return == 1 && safeExec(LastSeen(l2), return(Some( * x)), X) && OutsideCritical(l2))
*/
{
  enter_critical();
  /*@ exists l, os_inv(l) 
      which implies
      conditionally_store_sll(flag, l) */
  if (flag) {
    /*@ exists l, conditionally_store_sll(1, l) 
        which implies
        sll(* p, rev(l)) */
    * p = reverse(* p);
    flag = 0;
  }
  /*@ Assert
        exists l2,
          safeExec(LastSeen(l1), atomic_pop(), X) &&
          RTrans(l1, l2) &&
          flag == 0 &&
          x == x@pre &&
          InsideCritical(l2) *
          sll(* p, l2) * undef_data_at(x) */
  int ret;
  ret = pop(p, x);
  /*@ exists l, flag == 0 && sll(* p, l) 
      which implies
      os_inv(l) */
  exit_critical();
  return ret;
}

void pop_add_push_C()
/*@ With l1 X
    Require safeExec(LastSeen(l1), pop_add_push(), X) && OutsideCritical(l1)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && OutsideCritical(l2)
*/
{
  int x;
  /*@ safeExec(LastSeen(l1), bind(atomic_pop, pop_add_push_loc0), X) && emp */
  if (atomic_pop_C(&x) /*@ where(aux_spec) c = pop_add_push_loc0, X = X; B = unit  */) {
    if (x >= 0) {
      x = x - 1;
      /*@ exists l2, safeExec(LastSeen(l2), atomic_push(x), X) && emp */
    }
    else {
      x = x + 1;
      /*@ exists l2, safeExec(LastSeen(l2), atomic_push(x), X) && emp */
    }
    atomic_push_C(x) /*@ where X = X */;
  }
}
