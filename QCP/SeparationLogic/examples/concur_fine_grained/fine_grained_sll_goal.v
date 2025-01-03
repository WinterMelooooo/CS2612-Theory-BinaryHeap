Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import fine_grained_sll_lib.
Import sll_C_Rules.
Require Import fine_grained_sll_lib.
Import sll_C_Rules.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import fine_grained_sll_lib.
Import sll_C_Rules.
Local Open Scope stmonad.
Require Import fine_grained_sll_lib.
Local Open Scope sac.
From SimpleC.EE.concur_fine_grained Require Import common_strategy_goal.
From SimpleC.EE.concur_fine_grained Require Import common_strategy_proof.
From SimpleC.EE.concur_fine_grained Require Import sll_strategy_goal.
From SimpleC.EE.concur_fine_grained Require Import sll_strategy_proof.
From SimpleC.EE.concur_fine_grained Require Import safeexec_strategy_goal.
From SimpleC.EE.concur_fine_grained Require Import safeexec_strategy_proof.
From SimpleC.EE.concur_fine_grained Require Import critical_strategy_goal.
From SimpleC.EE.concur_fine_grained Require Import critical_strategy_proof.

(*----- Function atomic_rev_C -----*)

Definition atomic_rev_C_safety_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atomic_rev_C_safety_wit_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition atomic_rev_C_return_wit_1_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (OutsideCritical (rev (l0)) )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  (OutsideCritical l2 )
.

Definition atomic_rev_C_return_wit_1_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (OutsideCritical (rev (l0)) )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  (OutsideCritical l2 )
.

Definition atomic_rev_C_partial_solve_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) ,
  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (OutsideCritical l1 )
|--
  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (OutsideCritical l1 )
.

Definition atomic_rev_C_partial_solve_wit_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (InsideCritical l0 )
  **  (os_inv l0 )
|--
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv l0 )
  **  (InsideCritical l0 )
.

Definition atomic_rev_C_partial_solve_wit_3_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> 0)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
|--
  [| (0 = 0) |] 
  &&  [| (flag = 1) |]
.

Definition atomic_rev_C_partial_solve_wit_3_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> 0)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
|--
  [| (0 = 0) |] 
  &&  [| (flag = 1) |] 
  &&  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> 0)
  **  (conditionally_store_sll 1 l0 )
  **  (InsideCritical l0 )
.

Definition atomic_rev_C_partial_solve_wit_3 := atomic_rev_C_partial_solve_wit_3_pure -> atomic_rev_C_partial_solve_wit_3_aux.

Definition atomic_rev_C_partial_solve_wit_4_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> 1)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
|--
  [| (1 = 1) |]
.

Definition atomic_rev_C_partial_solve_wit_4_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> 1)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
|--
  [| (1 = 1) |] 
  &&  [| (flag = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> 1)
  **  (conditionally_store_sll 0 l0 )
  **  (InsideCritical l0 )
.

Definition atomic_rev_C_partial_solve_wit_4 := atomic_rev_C_partial_solve_wit_4_pure -> atomic_rev_C_partial_solve_wit_4_aux.

Definition atomic_rev_C_partial_solve_wit_5_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv (rev (l0)) )
  **  (InsideCritical l0 )
|--
  [| (GTrans l0 (rev (l0)) ) |]
.

Definition atomic_rev_C_partial_solve_wit_5_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv (rev (l0)) )
  **  (InsideCritical l0 )
|--
  [| (GTrans l0 (rev (l0)) ) |] 
  &&  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (InsideCritical l0 )
  **  (os_inv (rev (l0)) )
.

Definition atomic_rev_C_partial_solve_wit_5 := atomic_rev_C_partial_solve_wit_5_pure -> atomic_rev_C_partial_solve_wit_5_aux.

Definition atomic_rev_C_partial_solve_wit_6_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv (rev (l0)) )
  **  (InsideCritical l0 )
|--
  [| (GTrans l0 (rev (l0)) ) |]
.

Definition atomic_rev_C_partial_solve_wit_6_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv (rev (l0)) )
  **  (InsideCritical l0 )
|--
  [| (GTrans l0 (rev (l0)) ) |] 
  &&  [| (flag = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (InsideCritical l0 )
  **  (os_inv (rev (l0)) )
.

Definition atomic_rev_C_partial_solve_wit_6 := atomic_rev_C_partial_solve_wit_6_pure -> atomic_rev_C_partial_solve_wit_6_aux.

Definition atomic_rev_C_which_implies_wit_1 := 
forall (l: (@list Z)) ,
  (os_inv l )
|--
  EX flag,
  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l )
.

Definition atomic_rev_C_which_implies_wit_2 := 
forall (l: (@list Z)) (flag: Z) ,
  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll 1 l )
|--
  (os_inv (rev (l)) )
.

Definition atomic_rev_C_which_implies_wit_3 := 
forall (l: (@list Z)) (flag: Z) ,
  [| (flag = 1) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll 0 l )
|--
  (os_inv (rev (l)) )
.

(*----- Function atomic_push_C -----*)

Definition atomic_push_C_safety_wit_1 := 
forall (x_pre: Z) (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) (p: Z) (retval: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  (sll retval (rev ((rev (l0)))) )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atomic_push_C_entail_wit_1_1 := 
forall (x_pre: Z) (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag_2: Z) (p_2: Z) (retval: Z) ,
  [| (flag_2 <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  (sll retval (rev ((rev (l0)))) )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((p_2) # Ptr  |-> retval)
  **  ((( &( "flag" ) )) # Int  |-> 0)
  **  (InsideCritical l0 )
|--
  EX p_v p flag l2,
  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l2 )
.

Definition atomic_push_C_entail_wit_1_2 := 
forall (x_pre: Z) (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag_2: Z) ,
  [| (flag_2 = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag_2)
  **  (conditionally_store_sll flag_2 l0 )
  **  (InsideCritical l0 )
|--
  EX p_v p flag l2,
  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l2 )
.

Definition atomic_push_C_return_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2_2: (@list Z)) (x: Z) (flag: Z) ,
  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2_2 ) |] 
  &&  [| (flag = 0) |]
  &&  (OutsideCritical (cons (x) (l2_2)) )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  (OutsideCritical l2 )
.

Definition atomic_push_C_partial_solve_wit_1 := 
forall (x_pre: Z) (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) ,
  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  (OutsideCritical l1 )
|--
  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  (OutsideCritical l1 )
.

Definition atomic_push_C_partial_solve_wit_2 := 
forall (x_pre: Z) (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  (InsideCritical l0 )
  **  (os_inv l0 )
|--
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  (os_inv l0 )
  **  (InsideCritical l0 )
.

Definition atomic_push_C_partial_solve_wit_3_pure := 
forall (x_pre: Z) (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (flag = 1) |]
.

Definition atomic_push_C_partial_solve_wit_3_aux := 
forall (x_pre: Z) (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
|--
  [| (flag = 1) |] 
  &&  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  (conditionally_store_sll 1 l0 )
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l0 )
.

Definition atomic_push_C_partial_solve_wit_3 := atomic_push_C_partial_solve_wit_3_pure -> atomic_push_C_partial_solve_wit_3_aux.

Definition atomic_push_C_partial_solve_wit_4 := 
forall (x_pre: Z) (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) (p_v: Z) (p: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v (rev (l0)) )
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l0 )
|--
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x_pre)) X ) |]
  &&  (sll p_v (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l0 )
.

Definition atomic_push_C_partial_solve_wit_5 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (flag: Z) (p: Z) (p_v: Z) ,
  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l2 )
|--
  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (sll p_v l2 )
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
.

Definition atomic_push_C_partial_solve_wit_6_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (flag: Z) (p: Z) (retval: Z) ,
  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (sll retval (cons (x) (l2)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval)
|--
  [| (0 = 0) |]
.

Definition atomic_push_C_partial_solve_wit_6_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (flag: Z) (p: Z) (retval: Z) ,
  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (sll retval (cons (x) (l2)) )
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval)
|--
  [| (0 = 0) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval)
  **  (sll retval (cons (x) (l2)) )
  **  (InsideCritical l2 )
.

Definition atomic_push_C_partial_solve_wit_6 := atomic_push_C_partial_solve_wit_6_pure -> atomic_push_C_partial_solve_wit_6_aux.

Definition atomic_push_C_partial_solve_wit_7_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (flag: Z) ,
  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (os_inv (cons (x) (l2)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (InsideCritical l2 )
|--
  [| (GTrans l2 (cons (x) (l2)) ) |]
.

Definition atomic_push_C_partial_solve_wit_7_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (flag: Z) ,
  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (os_inv (cons (x) (l2)) )
  **  (InsideCritical l2 )
|--
  [| (GTrans l2 (cons (x) (l2)) ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_push (x)) X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (InsideCritical l2 )
  **  (os_inv (cons (x) (l2)) )
.

Definition atomic_push_C_partial_solve_wit_7 := atomic_push_C_partial_solve_wit_7_pure -> atomic_push_C_partial_solve_wit_7_aux.

Definition atomic_push_C_which_implies_wit_1 := 
forall (l: (@list Z)) ,
  (os_inv l )
|--
  EX flag,
  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l )
.

Definition atomic_push_C_which_implies_wit_2 := 
forall (l: (@list Z)) ,
  (conditionally_store_sll 1 l )
|--
  EX p_v p,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v (rev (l)) )
.

Definition atomic_push_C_which_implies_wit_3 := 
forall (l: (@list Z)) (flag: Z) (p: Z) (p_v: Z) ,
  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l )
|--
  (os_inv l )
.

(*----- Function atomic_pop_C -----*)

Definition atomic_pop_C_safety_wit_1 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) (p: Z) (retval: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  (sll retval (rev ((rev (l0)))) )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l0 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atomic_pop_C_entail_wit_1_1 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag_2: Z) (p_2: Z) (retval: Z) ,
  [| (flag_2 <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  (sll retval (rev ((rev (l0)))) )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((p_2) # Ptr  |-> retval)
  **  ((( &( "flag" ) )) # Int  |-> 0)
  **  (InsideCritical l0 )
  **  ((x_pre) # Int  |->_)
|--
  EX p_v p flag l2,
  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l2 )
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop_C_entail_wit_1_2 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag_2: Z) ,
  [| (flag_2 = 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag_2)
  **  (conditionally_store_sll flag_2 l0 )
  **  (InsideCritical l0 )
  **  ((x_pre) # Int  |->_)
|--
  EX p_v p flag l2,
  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l2 )
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop_C_return_wit_1_1 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2_3: (@list Z)) (flag: Z) (x_pre_v_2: Z) (l0: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (l2_3 = (cons (x_pre_v_2) (l0))) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2_3 ) |] 
  &&  [| (flag = 0) |]
  &&  (OutsideCritical l0 )
  **  ((x_pre) # Int  |-> x_pre_v_2)
|--
  (EX l2,
  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (return (None)) X ) |]
  &&  (OutsideCritical l2 )
  **  ((x_pre) # Int  |->_))
  ||
  (EX l2_2 x_pre_v,
  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (return ((Some (x_pre_v)))) X ) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  (OutsideCritical l2_2 ))
.

Definition atomic_pop_C_return_wit_1_2 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2_3: (@list Z)) (flag: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (l2_3 = nil) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2_3 ) |] 
  &&  [| (flag = 0) |]
  &&  (OutsideCritical l2_3 )
  **  ((x_pre) # Int  |->_)
|--
  (EX l2,
  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (return (None)) X ) |]
  &&  (OutsideCritical l2 )
  **  ((x_pre) # Int  |->_))
  ||
  (EX l2_2 x_pre_v,
  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (return ((Some (x_pre_v)))) X ) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  (OutsideCritical l2_2 ))
.

Definition atomic_pop_C_partial_solve_wit_1 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) ,
  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  (OutsideCritical l1 )
  **  ((x_pre) # Int  |->_)
|--
  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  (OutsideCritical l1 )
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop_C_partial_solve_wit_2 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  (InsideCritical l0 )
  **  (os_inv l0 )
  **  ((x_pre) # Int  |->_)
|--
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  (os_inv l0 )
  **  (InsideCritical l0 )
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop_C_partial_solve_wit_3_pure := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Int  |->_)
|--
  [| (flag = 1) |]
.

Definition atomic_pop_C_partial_solve_wit_3_aux := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l0 )
  **  (InsideCritical l0 )
  **  ((x_pre) # Int  |->_)
|--
  [| (flag = 1) |] 
  &&  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  (conditionally_store_sll 1 l0 )
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l0 )
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop_C_partial_solve_wit_3 := atomic_pop_C_partial_solve_wit_3_pure -> atomic_pop_C_partial_solve_wit_3_aux.

Definition atomic_pop_C_partial_solve_wit_4 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (flag: Z) (p_v: Z) (p: Z) ,
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v (rev (l0)) )
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l0 )
  **  ((x_pre) # Int  |->_)
|--
  [| (flag <> 0) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |]
  &&  (sll p_v (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l0 )
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop_C_partial_solve_wit_5 := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (p: Z) (p_v: Z) ,
  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l2 )
  **  ((x_pre) # Int  |->_)
|--
  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((p) # Ptr  |-> p_v)
  **  (sll p_v l2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_pop_C_partial_solve_wit_6_pure := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (p: Z) (p_pre_v: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (l2 = nil) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((p) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "ret" ) )) # Int  |-> retval)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (0 = 0) |]
.

Definition atomic_pop_C_partial_solve_wit_6_aux := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (p: Z) (p_pre_v: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (l2 = nil) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((p) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (0 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l2 = nil) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l2 )
  **  ((x_pre) # Int  |->_)
  **  (InsideCritical l2 )
.

Definition atomic_pop_C_partial_solve_wit_6 := atomic_pop_C_partial_solve_wit_6_pure -> atomic_pop_C_partial_solve_wit_6_aux.

Definition atomic_pop_C_partial_solve_wit_7_pure := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (p: Z) (p_pre_v: Z) (x_pre_v: Z) (l0: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (l2 = (cons (x_pre_v) (l0))) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((p) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l0 )
  **  ((( &( "ret" ) )) # Int  |-> retval)
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (0 = 0) |]
.

Definition atomic_pop_C_partial_solve_wit_7_aux := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (p: Z) (p_pre_v: Z) (x_pre_v: Z) (l0: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (l2 = (cons (x_pre_v) (l0))) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((p) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l0 )
  **  ((( &( "flag" ) )) # Int  |-> flag)
  **  (InsideCritical l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (0 = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (l2 = (cons (x_pre_v) (l0))) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l0 )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  (InsideCritical l2 )
.

Definition atomic_pop_C_partial_solve_wit_7 := atomic_pop_C_partial_solve_wit_7_pure -> atomic_pop_C_partial_solve_wit_7_aux.

Definition atomic_pop_C_partial_solve_wit_8_pure := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (x_pre_v: Z) (l0: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (l2 = (cons (x_pre_v) (l0))) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (os_inv l0 )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "ret" ) )) # Int  |-> retval)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (InsideCritical l2 )
|--
  [| (GTrans l2 l0 ) |]
.

Definition atomic_pop_C_partial_solve_wit_8_aux := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (x_pre_v: Z) (l0: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (l2 = (cons (x_pre_v) (l0))) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (os_inv l0 )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  (InsideCritical l2 )
|--
  [| (GTrans l2 l0 ) |] 
  &&  [| (retval = 1) |] 
  &&  [| (l2 = (cons (x_pre_v) (l0))) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (InsideCritical l2 )
  **  (os_inv l0 )
  **  ((x_pre) # Int  |-> x_pre_v)
.

Definition atomic_pop_C_partial_solve_wit_8 := atomic_pop_C_partial_solve_wit_8_pure -> atomic_pop_C_partial_solve_wit_8_aux.

Definition atomic_pop_C_partial_solve_wit_9_pure := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (l2 = nil) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (os_inv l2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "ret" ) )) # Int  |-> retval)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (InsideCritical l2 )
|--
  [| (GTrans l2 l2 ) |]
.

Definition atomic_pop_C_partial_solve_wit_9_aux := 
forall (x_pre: Z) (X: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (flag: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (l2 = nil) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (os_inv l2 )
  **  ((x_pre) # Int  |->_)
  **  (InsideCritical l2 )
|--
  [| (GTrans l2 l2 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l2 = nil) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_pop X ) |] 
  &&  [| (RTrans l1 l2 ) |] 
  &&  [| (flag = 0) |]
  &&  (InsideCritical l2 )
  **  (os_inv l2 )
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop_C_partial_solve_wit_9 := atomic_pop_C_partial_solve_wit_9_pure -> atomic_pop_C_partial_solve_wit_9_aux.

Definition atomic_pop_C_which_implies_wit_1 := 
forall (l: (@list Z)) ,
  (os_inv l )
|--
  EX flag,
  ((( &( "flag" ) )) # Int  |-> flag)
  **  (conditionally_store_sll flag l )
.

Definition atomic_pop_C_which_implies_wit_2 := 
forall (l: (@list Z)) ,
  (conditionally_store_sll 1 l )
|--
  EX p_v p,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v (rev (l)) )
.

Definition atomic_pop_C_which_implies_wit_3 := 
forall (l: (@list Z)) (flag: Z) (p: Z) (p_v: Z) ,
  [| (flag = 0) |]
  &&  ((( &( "flag" ) )) # Int  |-> flag)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l )
|--
  (os_inv l )
.

(*----- Function pop_add_push_C -----*)

Definition pop_add_push_C_safety_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 (None)) X ) |]
  &&  (OutsideCritical l2 )
  **  ((( &( "x" ) )) # Int  |->_)
|--
  [| False |]
.

Definition pop_add_push_C_safety_wit_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre_v)
  **  (OutsideCritical l2 )
|--
  [| False |]
.

Definition pop_add_push_C_safety_wit_3 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre_v)
  **  (OutsideCritical l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pop_add_push_C_safety_wit_4 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) ,
  [| (x_pre_v >= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre_v)
  **  (OutsideCritical l2 )
|--
  [| ((x_pre_v - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre_v - 1 )) |]
.

Definition pop_add_push_C_safety_wit_5 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) ,
  [| (x_pre_v >= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre_v)
  **  (OutsideCritical l2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition pop_add_push_C_safety_wit_6 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) ,
  [| (x_pre_v < 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre_v)
  **  (OutsideCritical l2 )
|--
  [| ((x_pre_v + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre_v + 1 )) |]
.

Definition pop_add_push_C_safety_wit_7 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) ,
  [| (x_pre_v < 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre_v)
  **  (OutsideCritical l2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition pop_add_push_C_entail_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) ,
  [| (safeExec (LastSeen (l1)) pop_add_push X ) |]
  &&  (OutsideCritical l1 )
|--
  [| (safeExec (LastSeen (l1)) (bind (atomic_pop) (pop_add_push_loc0)) X ) |]
  &&  (OutsideCritical l1 )
.

Definition pop_add_push_C_entail_wit_2_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2_2: (@list Z)) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (pop_add_push_loc0 (None)) X ) |]
  &&  (OutsideCritical l2_2 )
  **  ((( &( "x" ) )) # Int  |->_)
|--
  EX l2 x_pre_v retval,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre_v)
  **  (OutsideCritical l2 )
.

Definition pop_add_push_C_entail_wit_2_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2_2: (@list Z)) (x_pre_v: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  (OutsideCritical l2_2 )
|--
  EX l2 retval,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  (OutsideCritical l2 )
.

Definition pop_add_push_C_entail_wit_3_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2_2: (@list Z)) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (pop_add_push_loc0 (None)) X ) |]
  &&  (OutsideCritical l2_2 )
|--
  EX l2 retval,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 (None)) X ) |]
  &&  (OutsideCritical l2 )
.

Definition pop_add_push_C_entail_wit_3_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2_2: (@list Z)) (x_pre_v: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre_v)
  **  (OutsideCritical l2_2 )
|--
  EX l2 retval,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (pop_add_push_loc0 (None)) X ) |]
  &&  (OutsideCritical l2 )
  **  ((( &( "x" ) )) # Int  |->_)
.

Definition pop_add_push_C_entail_wit_4 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2_2: (@list Z)) (x_pre_v: Z) (retval: Z) ,
  [| (x_pre_v >= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  (OutsideCritical l2_2 )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v - 1 ))) X ) |] 
  &&  [| (x_pre_v >= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  (OutsideCritical l2_2 )
.

Definition pop_add_push_C_entail_wit_5 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2_2: (@list Z)) (x_pre_v: Z) (retval: Z) ,
  [| (x_pre_v < 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (pop_add_push_loc0 ((Some (x_pre_v)))) X ) |]
  &&  (OutsideCritical l2_2 )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v + 1 ))) X ) |] 
  &&  [| (x_pre_v < 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  (OutsideCritical l2_2 )
.

Definition pop_add_push_C_return_wit_1_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2_2: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (pop_add_push_loc0 (None)) X ) |]
  &&  (OutsideCritical l2_2 )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  (OutsideCritical l2 )
.

Definition pop_add_push_C_return_wit_1_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (x_pre_v: Z) (retval: Z) (l2_2: (@list Z)) ,
  [| (safeExec (LastSeen (l2_2)) (return (tt)) X ) |] 
  &&  [| (x_pre_v >= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  (OutsideCritical l2_2 )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  (OutsideCritical l2 )
.

Definition pop_add_push_C_return_wit_1_3 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (x_pre_v: Z) (retval: Z) (l2_2: (@list Z)) ,
  [| (safeExec (LastSeen (l2_2)) (return (tt)) X ) |] 
  &&  [| (x_pre_v < 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  (OutsideCritical l2_2 )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  (OutsideCritical l2 )
.

Definition pop_add_push_C_partial_solve_wit_1_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) ,
  [| (safeExec (LastSeen (l1)) (bind (atomic_pop) (pop_add_push_loc0)) X ) |]
  &&  ((( &( "x" ) )) # Int  |->_)
  **  (OutsideCritical l1 )
|--
  [| (safeExec (LastSeen (l1)) (bind (atomic_pop) (pop_add_push_loc0)) X ) |]
.

Definition pop_add_push_C_partial_solve_wit_1_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) ,
  [| (safeExec (LastSeen (l1)) (bind (atomic_pop) (pop_add_push_loc0)) X ) |]
  &&  (OutsideCritical l1 )
|--
  [| (safeExec (LastSeen (l1)) (bind (atomic_pop) (pop_add_push_loc0)) X ) |]
  &&  (OutsideCritical l1 )
.

Definition pop_add_push_C_partial_solve_wit_1 := pop_add_push_C_partial_solve_wit_1_pure -> pop_add_push_C_partial_solve_wit_1_aux.

Definition pop_add_push_C_partial_solve_wit_2_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) (l2_2: (@list Z)) ,
  [| (safeExec (LastSeen (l2_2)) (atomic_push ((x_pre_v - 1 ))) X ) |] 
  &&  [| (x_pre_v >= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre_v - 1 ))
  **  (OutsideCritical l2 )
|--
  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v - 1 ))) X ) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v - 1 ))) X ) |]
.

Definition pop_add_push_C_partial_solve_wit_2_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) (l2_2: (@list Z)) ,
  [| (safeExec (LastSeen (l2_2)) (atomic_push ((x_pre_v - 1 ))) X ) |] 
  &&  [| (x_pre_v >= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  (OutsideCritical l2 )
|--
  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v - 1 ))) X ) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v - 1 ))) X ) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (atomic_push ((x_pre_v - 1 ))) X ) |] 
  &&  [| (x_pre_v >= 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  (OutsideCritical l2 )
.

Definition pop_add_push_C_partial_solve_wit_2 := pop_add_push_C_partial_solve_wit_2_pure -> pop_add_push_C_partial_solve_wit_2_aux.

Definition pop_add_push_C_partial_solve_wit_3_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) (l2_2: (@list Z)) ,
  [| (safeExec (LastSeen (l2_2)) (atomic_push ((x_pre_v + 1 ))) X ) |] 
  &&  [| (x_pre_v < 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre_v + 1 ))
  **  (OutsideCritical l2 )
|--
  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v + 1 ))) X ) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v + 1 ))) X ) |]
.

Definition pop_add_push_C_partial_solve_wit_3_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l2: (@list Z)) (x_pre_v: Z) (retval: Z) (l2_2: (@list Z)) ,
  [| (safeExec (LastSeen (l2_2)) (atomic_push ((x_pre_v + 1 ))) X ) |] 
  &&  [| (x_pre_v < 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  (OutsideCritical l2 )
|--
  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v + 1 ))) X ) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_push ((x_pre_v + 1 ))) X ) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (atomic_push ((x_pre_v + 1 ))) X ) |] 
  &&  [| (x_pre_v < 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |]
  &&  (OutsideCritical l2 )
.

Definition pop_add_push_C_partial_solve_wit_3 := pop_add_push_C_partial_solve_wit_3_pure -> pop_add_push_C_partial_solve_wit_3_aux.

Definition atomic_pop_C_derive_aux_spec_by_normal_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X: (B -> (((@list Z) -> Prop) -> Prop))) (c: ((@option Z) -> (@program ((@list Z) -> Prop) B))) (l1: (@list Z)) ,
  [| (safeExec (LastSeen (l1)) (bind (atomic_pop) (c)) X ) |]
  &&  (OutsideCritical l1 )
  **  ((x_pre) # Int  |->_)
|--
EX (l1_2: (@list Z)) (X_2: ((@option Z) -> (((@list Z) -> Prop) -> Prop))) ,
  ([| (safeExec (LastSeen (l1_2)) atomic_pop X_2 ) |]
  &&  (OutsideCritical l1_2 )
  **  ((x_pre) # Int  |->_))
  **
  (((EX l2_3 x_pre_v_2 retval_2,
  [| (retval_2 = 1) |] 
  &&  [| (safeExec (LastSeen (l2_3)) (return ((Some (x_pre_v_2)))) X_2 ) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  (OutsideCritical l2_3 ))
  ||
  (EX l2_4 retval_2,
  [| (retval_2 = 0) |] 
  &&  [| (safeExec (LastSeen (l2_4)) (return (None)) X_2 ) |]
  &&  (OutsideCritical l2_4 )
  **  ((x_pre) # Int  |->_)))
  -*
  ((EX l2 x_pre_v retval,
  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (c ((Some (x_pre_v)))) X ) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  (OutsideCritical l2 ))
  ||
  (EX l2_2 retval,
  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (c (None)) X ) |]
  &&  (OutsideCritical l2_2 )
  **  ((x_pre) # Int  |->_))))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.
Include critical_Strategy_Correct.

Axiom proof_of_atomic_rev_C_safety_wit_1 : atomic_rev_C_safety_wit_1.
Axiom proof_of_atomic_rev_C_safety_wit_2 : atomic_rev_C_safety_wit_2.
Axiom proof_of_atomic_rev_C_return_wit_1_1 : atomic_rev_C_return_wit_1_1.
Axiom proof_of_atomic_rev_C_return_wit_1_2 : atomic_rev_C_return_wit_1_2.
Axiom proof_of_atomic_rev_C_partial_solve_wit_1 : atomic_rev_C_partial_solve_wit_1.
Axiom proof_of_atomic_rev_C_partial_solve_wit_2 : atomic_rev_C_partial_solve_wit_2.
Axiom proof_of_atomic_rev_C_partial_solve_wit_3_pure : atomic_rev_C_partial_solve_wit_3_pure.
Axiom proof_of_atomic_rev_C_partial_solve_wit_3 : atomic_rev_C_partial_solve_wit_3.
Axiom proof_of_atomic_rev_C_partial_solve_wit_4_pure : atomic_rev_C_partial_solve_wit_4_pure.
Axiom proof_of_atomic_rev_C_partial_solve_wit_4 : atomic_rev_C_partial_solve_wit_4.
Axiom proof_of_atomic_rev_C_partial_solve_wit_5_pure : atomic_rev_C_partial_solve_wit_5_pure.
Axiom proof_of_atomic_rev_C_partial_solve_wit_5 : atomic_rev_C_partial_solve_wit_5.
Axiom proof_of_atomic_rev_C_partial_solve_wit_6_pure : atomic_rev_C_partial_solve_wit_6_pure.
Axiom proof_of_atomic_rev_C_partial_solve_wit_6 : atomic_rev_C_partial_solve_wit_6.
Axiom proof_of_atomic_rev_C_which_implies_wit_1 : atomic_rev_C_which_implies_wit_1.
Axiom proof_of_atomic_rev_C_which_implies_wit_2 : atomic_rev_C_which_implies_wit_2.
Axiom proof_of_atomic_rev_C_which_implies_wit_3 : atomic_rev_C_which_implies_wit_3.
Axiom proof_of_atomic_push_C_safety_wit_1 : atomic_push_C_safety_wit_1.
Axiom proof_of_atomic_push_C_entail_wit_1_1 : atomic_push_C_entail_wit_1_1.
Axiom proof_of_atomic_push_C_entail_wit_1_2 : atomic_push_C_entail_wit_1_2.
Axiom proof_of_atomic_push_C_return_wit_1 : atomic_push_C_return_wit_1.
Axiom proof_of_atomic_push_C_partial_solve_wit_1 : atomic_push_C_partial_solve_wit_1.
Axiom proof_of_atomic_push_C_partial_solve_wit_2 : atomic_push_C_partial_solve_wit_2.
Axiom proof_of_atomic_push_C_partial_solve_wit_3_pure : atomic_push_C_partial_solve_wit_3_pure.
Axiom proof_of_atomic_push_C_partial_solve_wit_3 : atomic_push_C_partial_solve_wit_3.
Axiom proof_of_atomic_push_C_partial_solve_wit_4 : atomic_push_C_partial_solve_wit_4.
Axiom proof_of_atomic_push_C_partial_solve_wit_5 : atomic_push_C_partial_solve_wit_5.
Axiom proof_of_atomic_push_C_partial_solve_wit_6_pure : atomic_push_C_partial_solve_wit_6_pure.
Axiom proof_of_atomic_push_C_partial_solve_wit_6 : atomic_push_C_partial_solve_wit_6.
Axiom proof_of_atomic_push_C_partial_solve_wit_7_pure : atomic_push_C_partial_solve_wit_7_pure.
Axiom proof_of_atomic_push_C_partial_solve_wit_7 : atomic_push_C_partial_solve_wit_7.
Axiom proof_of_atomic_push_C_which_implies_wit_1 : atomic_push_C_which_implies_wit_1.
Axiom proof_of_atomic_push_C_which_implies_wit_2 : atomic_push_C_which_implies_wit_2.
Axiom proof_of_atomic_push_C_which_implies_wit_3 : atomic_push_C_which_implies_wit_3.
Axiom proof_of_atomic_pop_C_safety_wit_1 : atomic_pop_C_safety_wit_1.
Axiom proof_of_atomic_pop_C_entail_wit_1_1 : atomic_pop_C_entail_wit_1_1.
Axiom proof_of_atomic_pop_C_entail_wit_1_2 : atomic_pop_C_entail_wit_1_2.
Axiom proof_of_atomic_pop_C_return_wit_1_1 : atomic_pop_C_return_wit_1_1.
Axiom proof_of_atomic_pop_C_return_wit_1_2 : atomic_pop_C_return_wit_1_2.
Axiom proof_of_atomic_pop_C_partial_solve_wit_1 : atomic_pop_C_partial_solve_wit_1.
Axiom proof_of_atomic_pop_C_partial_solve_wit_2 : atomic_pop_C_partial_solve_wit_2.
Axiom proof_of_atomic_pop_C_partial_solve_wit_3_pure : atomic_pop_C_partial_solve_wit_3_pure.
Axiom proof_of_atomic_pop_C_partial_solve_wit_3 : atomic_pop_C_partial_solve_wit_3.
Axiom proof_of_atomic_pop_C_partial_solve_wit_4 : atomic_pop_C_partial_solve_wit_4.
Axiom proof_of_atomic_pop_C_partial_solve_wit_5 : atomic_pop_C_partial_solve_wit_5.
Axiom proof_of_atomic_pop_C_partial_solve_wit_6_pure : atomic_pop_C_partial_solve_wit_6_pure.
Axiom proof_of_atomic_pop_C_partial_solve_wit_6 : atomic_pop_C_partial_solve_wit_6.
Axiom proof_of_atomic_pop_C_partial_solve_wit_7_pure : atomic_pop_C_partial_solve_wit_7_pure.
Axiom proof_of_atomic_pop_C_partial_solve_wit_7 : atomic_pop_C_partial_solve_wit_7.
Axiom proof_of_atomic_pop_C_partial_solve_wit_8_pure : atomic_pop_C_partial_solve_wit_8_pure.
Axiom proof_of_atomic_pop_C_partial_solve_wit_8 : atomic_pop_C_partial_solve_wit_8.
Axiom proof_of_atomic_pop_C_partial_solve_wit_9_pure : atomic_pop_C_partial_solve_wit_9_pure.
Axiom proof_of_atomic_pop_C_partial_solve_wit_9 : atomic_pop_C_partial_solve_wit_9.
Axiom proof_of_atomic_pop_C_which_implies_wit_1 : atomic_pop_C_which_implies_wit_1.
Axiom proof_of_atomic_pop_C_which_implies_wit_2 : atomic_pop_C_which_implies_wit_2.
Axiom proof_of_atomic_pop_C_which_implies_wit_3 : atomic_pop_C_which_implies_wit_3.
Axiom proof_of_pop_add_push_C_safety_wit_1 : pop_add_push_C_safety_wit_1.
Axiom proof_of_pop_add_push_C_safety_wit_2 : pop_add_push_C_safety_wit_2.
Axiom proof_of_pop_add_push_C_safety_wit_3 : pop_add_push_C_safety_wit_3.
Axiom proof_of_pop_add_push_C_safety_wit_4 : pop_add_push_C_safety_wit_4.
Axiom proof_of_pop_add_push_C_safety_wit_5 : pop_add_push_C_safety_wit_5.
Axiom proof_of_pop_add_push_C_safety_wit_6 : pop_add_push_C_safety_wit_6.
Axiom proof_of_pop_add_push_C_safety_wit_7 : pop_add_push_C_safety_wit_7.
Axiom proof_of_pop_add_push_C_entail_wit_1 : pop_add_push_C_entail_wit_1.
Axiom proof_of_pop_add_push_C_entail_wit_2_1 : pop_add_push_C_entail_wit_2_1.
Axiom proof_of_pop_add_push_C_entail_wit_2_2 : pop_add_push_C_entail_wit_2_2.
Axiom proof_of_pop_add_push_C_entail_wit_3_1 : pop_add_push_C_entail_wit_3_1.
Axiom proof_of_pop_add_push_C_entail_wit_3_2 : pop_add_push_C_entail_wit_3_2.
Axiom proof_of_pop_add_push_C_entail_wit_4 : pop_add_push_C_entail_wit_4.
Axiom proof_of_pop_add_push_C_entail_wit_5 : pop_add_push_C_entail_wit_5.
Axiom proof_of_pop_add_push_C_return_wit_1_1 : pop_add_push_C_return_wit_1_1.
Axiom proof_of_pop_add_push_C_return_wit_1_2 : pop_add_push_C_return_wit_1_2.
Axiom proof_of_pop_add_push_C_return_wit_1_3 : pop_add_push_C_return_wit_1_3.
Axiom proof_of_pop_add_push_C_partial_solve_wit_1_pure : pop_add_push_C_partial_solve_wit_1_pure.
Axiom proof_of_pop_add_push_C_partial_solve_wit_1 : pop_add_push_C_partial_solve_wit_1.
Axiom proof_of_pop_add_push_C_partial_solve_wit_2_pure : pop_add_push_C_partial_solve_wit_2_pure.
Axiom proof_of_pop_add_push_C_partial_solve_wit_2 : pop_add_push_C_partial_solve_wit_2.
Axiom proof_of_pop_add_push_C_partial_solve_wit_3_pure : pop_add_push_C_partial_solve_wit_3_pure.
Axiom proof_of_pop_add_push_C_partial_solve_wit_3 : pop_add_push_C_partial_solve_wit_3.
Axiom proof_of_atomic_pop_C_derive_aux_spec_by_normal_spec : atomic_pop_C_derive_aux_spec_by_normal_spec.

End VC_Correct.
