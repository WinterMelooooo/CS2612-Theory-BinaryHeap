/*@ Extern Coq (InsideCritical: Z -> list Z -> Assertion)
               (OutsideCritical: Z -> list Z -> Assertion)
               (RTrans_C: Z -> list Z -> Z -> list Z -> Prop)
               (GTrans_C: Z -> list Z -> Z -> list Z -> Prop)
               (RTrans_Abs: list Z -> list Z -> Prop)
               (GTrans_Abs: list Z -> list Z -> Prop)
               (os_inv: Z -> list Z -> Assertion) */

/*@ include strategies "guarded_critical.strategies" */

/*@ Import Coq Require Import guarded_critical_sll_lib */
/*@ Import Coq Require Import sequential_critical_sll_lib */
