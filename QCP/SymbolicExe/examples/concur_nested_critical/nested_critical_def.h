/*@ Extern Coq (Critical: list Z -> list Z -> Assertion)
               (RTrans: list Z -> list Z -> Prop)
               (GTrans: list Z -> list Z -> Prop)
               (os_inv: list Z -> Assertion) */

/*@ include strategies "nested_critical.strategies" */

/*@ Import Coq Require Import nested_critical_sll_lib */
