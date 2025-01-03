/*@ Extern Coq (InsideCritical: list Z -> Assertion)
               (OutsideCritical: list Z -> Assertion)
               (RTrans: list Z -> list Z -> Prop)
               (GTrans: list Z -> list Z -> Prop)
               (os_inv: list Z -> Assertion) */

/*@ include strategies "critical.strategies" */

/*@ Import Coq Require Import critical_sll_lib */
