#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"
#include "safeexec_def.h"
#include "triple_critical_def.h"

/*@ Extern Coq (atomic_1_rev: program (list Z * list Z * list Z -> Prop) unit)
               (atomic_2_pop : program (list Z * list Z * list Z -> Prop) (option Z))
               (atomic_3_push : Z -> program (list Z * list Z * list Z -> Prop) unit)
               (atomic_3_push_loc0 : option Z -> program (list Z * list Z * list Z -> Prop) unit)
               (triple_work : program (list Z * list Z * list Z -> Prop) unit)
               (pop2_push3 : unit -> program (list Z * list Z * list Z -> Prop) unit)
              (LastSeen: list Z * list Z * list Z -> (list Z * list Z * list Z -> Prop) -> Prop)
 */

struct list * * p;
struct list * * q;
struct list * * r;

void enter_critical()
/*@ With (q: Z * Z * Z) (l: list Z * list Z * list Z)
    Require OutsideCritical(q, l)
    Ensure exists q0 l0,
             RTrans_C(q, l, q0, l0) &&
             InsideCritical(q0, l0) * os_inv(q0, l0)
*/
;

void exit_critical()
/*@ With (q1: Z * Z * Z) (l1: list Z * list Z * list Z) (q2: Z * Z * Z) (l2: list Z * list Z * list Z)
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

void atomic_rev1()
/*@ With (q: Z * Z * Z) (l1: list Z * list Z * list Z)
    Require p == fst(fst(q)) && OutsideCritical(q, l1)
    Ensure exists l2, p == fst(fst(q)) && OutsideCritical(q, l2)
*/
{
  enter_critical();
  /*@ exists l, os_inv(q, l) 
      which implies
      sll(* (struct list **) fst(fst(q)), fst(fst(l))) *
      sll(* (struct list **) snd(fst(q)), snd(fst(l))) * 
      sll(* (struct list **) snd(q), snd(l)) */
  * p = reverse(* p);
  /*@ exists l l0 rev_l, sll(* (struct list **) (fst (fst (q))), rev_l) *
      sll(* (struct list **) snd(fst(q)), l) * 
      sll(* (struct list **) snd(q), l0)
      which implies
      os_inv(q, prod3(rev_l, l, l0)) */
  exit_critical();
}

void atomic_rev1_2()
/*@ aux_rev_spec <= normal_rev_spec
    With {B} q0 l1 (c: unit -> program (list Z * list Z * list Z -> Prop) B) X
    Require safeExec(LastSeen(l1), bind(atomic_1_rev, c), X) && p == fst(fst(q0)) && OutsideCritical(q0, l1)
    Ensure exists l2, safeExec(LastSeen(l2), c(tt), X) && p == fst(fst(q0)) && OutsideCritical(q0, l2)
*/;

void atomic_rev1_2()
/*@ normal_rev_spec
    With (q0: Z * Z * Z) (l1: list Z * list Z * list Z) X
    Require safeExec(LastSeen(l1), atomic_1_rev, X) && p == fst(fst(q0)) && OutsideCritical(q0, l1)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && p == fst(fst(q0)) && OutsideCritical(q0, l2)
*/
{
    enter_critical();
    /*@ exists l, os_inv(q0, l) 
      which implies
      sll(* (struct list **) fst(fst(q0)), fst(fst(l))) *
      sll(* (struct list **) snd(fst(q0)), snd(fst(l))) * 
      sll(* (struct list **) snd(q0), snd(l)) */
    * p = reverse(* p);
    /*@ exists l l0 rev_l, sll(* (struct list **) (fst (fst (q0))), rev_l) *
      sll(* (struct list **) snd(fst(q0)), l) * 
      sll(* (struct list **) snd(q0), l0)
      which implies
      os_inv(q0, prod3(rev_l, l, l0)) */
    exit_critical();
}


int atomic_pop2_2(int * x)
/*@ aux_pop_spec <= normal_pop_spec
    With {B} q0 l1 (c: option Z -> program (list Z * list Z * list Z -> Prop) B) X
    Require safeExec(LastSeen(l1), bind(atomic_2_pop, c), X) && q == snd(fst(q0)) && OutsideCritical(q0, l1) * undef_data_at(x)
    Ensure (exists l2, __return == 0 && safeExec(LastSeen(l2), c(None), X) && q == snd(fst(q0)) && OutsideCritical(q0, l2) * undef_data_at(x)) ||
           (exists l2, __return == 1 && safeExec(LastSeen(l2), c(Some( * x)), X) && q == snd(fst(q0)) && OutsideCritical(q0, l2))
*/
;

int atomic_pop2_2(int * x)
/*@ normal_pop_spec
    With (q0: Z * Z * Z) (l1: list Z * list Z * list Z) X
    Require safeExec(LastSeen(l1), atomic_2_pop, X) && q == snd(fst(q0)) && OutsideCritical(q0, l1) * undef_data_at(x)
    Ensure (exists l2, __return == 0 && safeExec(LastSeen(l2), return(None), X) && q == snd(fst(q0)) && OutsideCritical(q0, l2) * undef_data_at(x)) ||
           (exists l2, __return == 1 && safeExec(LastSeen(l2), return(Some( * x)), X) && q == snd(fst(q0)) && OutsideCritical(q0, l2))
*/
{
    enter_critical();
    /*@ exists l, os_inv(q0, l) 
      which implies
      sll(* (struct list **) fst(fst(q0)), fst(fst(l))) *
      sll(* (struct list **) snd(fst(q0)), snd(fst(l))) * 
      sll(* (struct list **) snd(q0), snd(l)) */
    int ret = pop(q, x);
    /*@ exists l l0 l2 , sll(* (struct list **) (fst (fst (q0))), l) *
      sll(* (struct list **) snd(fst(q0)), l0) * 
      sll(* (struct list **) snd(q0), l2)
      which implies
      os_inv(q0, prod3(l, l0, l2)) */
    exit_critical();

    return ret;
}

void atomic_push2_3(int x)
/*@ aux_push_spec <= normal_push_spec 
    With {B} q0 l1 (c: unit -> program (list Z * list Z * list Z -> Prop) B) X
    Require safeExec(LastSeen(l1), bind(atomic_3_push(x), c), X) && r == snd(q0) && OutsideCritical(q0, l1)
    Ensure exists l2, safeExec(LastSeen(l2), c(tt), X) && r == snd(q0) && OutsideCritical(q0, l2)
*/;


void atomic_push2_3(int x)
/*@ normal_push_spec
    With (q0: Z * Z * Z) (l1: list Z * list Z * list Z) X
    Require safeExec(LastSeen(l1), atomic_3_push(x), X) && r == snd(q0) && OutsideCritical(q0, l1)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && r == snd(q0) && OutsideCritical(q0, l2)
*/
{
    enter_critical();
    /*@ exists l, os_inv(q0, l) 
      which implies
      sll(* (struct list **) fst(fst(q0)), fst(fst(l))) *
      sll(* (struct list **) snd(fst(q0)), snd(fst(l))) * 
      sll(* (struct list **) snd(q0), snd(l)) */
    * r = push(* r, x);
    /*@ exists l l0 l2 , sll(* (struct list **) (fst (fst (q0))), l) *
      sll(* (struct list **) snd(fst(q0)), l0) * 
      sll(* (struct list **) snd(q0), l2)
      which implies
      os_inv(q0, prod3(l, l0, l2)) */
    exit_critical();
}


void triple_work_C(int *x)
/*@ With (q0: Z * Z * Z) (l1: list Z * list Z * list Z) X
    Require safeExec(LastSeen(l1), triple_work(), X) && p == fst(fst(q0)) && q == snd(fst(q0)) && r == snd(q0) && OutsideCritical(q0, l1) * undef_data_at(x)
    Ensure exists l2, safeExec(LastSeen(l2), return(tt), X) && p == fst(fst(q0)) && q == snd(fst(q0)) && r == snd(q0) && OutsideCritical(q0, l2) * undef_data_at(x)
*/
{
    /*@ safeExec(LastSeen(l1), bind(atomic_1_rev, pop2_push3), X) && emp */
    atomic_rev1_2() /*@ where (aux_rev_spec) X = X ; B = unit*/;
    /*@ exists l1, safeExec(LastSeen(l1), bind(atomic_2_pop, atomic_3_push_loc0), X) && emp*/
    if (atomic_pop2_2(x) /*@ where (aux_pop_spec) c = atomic_3_push_loc0 , X = X ; B = unit*/)
    {
      /*@ exists l1, safeExec(LastSeen(l1), atomic_3_push(*x), X) && emp*/
      atomic_push2_3(*x) /*@ where (normal_push_spec) X = X ; B = unit*/;
    }
}