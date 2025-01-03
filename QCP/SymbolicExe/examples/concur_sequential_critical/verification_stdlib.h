/*@ Extern Coq (should_be_equal: {A} -> A -> A -> Prop) */
/*@ Extern Coq (option :: * => *) */
/*@ Extern Coq (Some: {A} -> A -> option A)
               (None: {A} -> option A) */

/*@ Import Coq Require Import guarded_critical_sll_lib */
/*@ Import Coq Import sll_C_Rules */
/*@ include strategies "common.strategies" */