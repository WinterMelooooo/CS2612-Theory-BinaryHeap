/*@ Extern Coq (should_be_equal: {A} -> A -> A -> Prop) */
/*@ Extern Coq (dup_data_at_error : Z -> Assertion)*/
/*@ Extern Coq (dup_data_at_error_prop : Prop) */
/*@ Extern Coq (option :: * => *) */
/*@ Extern Coq (Some: {A} -> A -> option A)
               (None: {A} -> option A) */
/*@ Extern Coq (UINT_MAX : Z) */

/*@ Import Coq Require Import triple_critical_sll_lib */
/*@ Import Coq Import sll_TC_Rules */
/*@ include strategies "common.strategies" */