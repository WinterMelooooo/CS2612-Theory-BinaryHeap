/*@ Extern Coq (InsideCritical: list Z -> Assertion)
               (OutsideCritical: list Z -> Assertion)
               (RTrans: list Z -> list Z -> Prop)
               (GTrans: list Z -> list Z -> Prop)
               (conditionally_store_sll: Z -> list Z -> Assertion)
               (os_inv: list Z -> Assertion) */

/*@ include strategies "critical.strategies" */

/*@ Import Coq Require Import fine_grained_sll_lib */
