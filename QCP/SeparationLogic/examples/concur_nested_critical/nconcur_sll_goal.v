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
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
Local Open Scope stmonad.
Require Import nested_critical_sll_lib.
Local Open Scope sac.
From SimpleC.EE.concur_nested_critical Require Import common_strategy_goal.
From SimpleC.EE.concur_nested_critical Require Import common_strategy_proof.
From SimpleC.EE.concur_nested_critical Require Import sll_strategy_goal.
From SimpleC.EE.concur_nested_critical Require Import sll_strategy_proof.
From SimpleC.EE.concur_nested_critical Require Import safeexec_strategy_goal.
From SimpleC.EE.concur_nested_critical Require Import safeexec_strategy_proof.
From SimpleC.EE.concur_nested_critical Require Import nested_critical_strategy_goal.
From SimpleC.EE.concur_nested_critical Require Import nested_critical_strategy_proof.

(*----- Function atomic_rev1 -----*)

Definition atomic_rev1_return_wit_1 := 
forall (l1: (@list Z)) (l0: (@list Z)) ,
  [| (RTrans l1 l0 ) |]
  &&  (Critical nil (rev (l0)) )
|--
  EX l2,
  (Critical nil l2 )
.

Definition atomic_rev1_partial_solve_wit_1 := 
forall (l1: (@list Z)) ,
  (Critical nil l1 )
|--
  (Critical nil l1 )
.

Definition atomic_rev1_partial_solve_wit_2 := 
forall (l1: (@list Z)) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans l1 l0 ) |]
  &&  (Critical (cons (retval) (nil)) l0 )
  **  (os_inv l0 )
|--
  [| (RTrans l1 l0 ) |]
  &&  (os_inv l0 )
  **  (Critical (cons (retval) (nil)) l0 )
.

Definition atomic_rev1_partial_solve_wit_3 := 
forall (l1: (@list Z)) (l0: (@list Z)) (retval: Z) (p_v: Z) (p: Z) ,
  [| (RTrans l1 l0 ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l0 )
  **  (Critical (cons (retval) (nil)) l0 )
|--
  [| (RTrans l1 l0 ) |]
  &&  (sll p_v l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (Critical (cons (retval) (nil)) l0 )
.

Definition atomic_rev1_partial_solve_wit_4 := 
forall (l1: (@list Z)) (l0: (@list Z)) (retval: Z) (p: Z) (retval_2: Z) ,
  [| (RTrans l1 l0 ) |]
  &&  (sll retval_2 (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval_2)
  **  (Critical (cons (retval) (nil)) l0 )
|--
  [| (RTrans l1 l0 ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval_2)
  **  (sll retval_2 (rev (l0)) )
  **  (Critical (cons (retval) (nil)) l0 )
.

Definition atomic_rev1_partial_solve_wit_5_pure := 
forall (l1: (@list Z)) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans l1 l0 ) |]
  &&  (os_inv (rev (l0)) )
  **  (Critical (cons (retval) (nil)) l0 )
  **  ((( &( "x" ) )) # Int  |-> retval)
|--
  [| (GTrans l0 (rev (l0)) ) |]
.

Definition atomic_rev1_partial_solve_wit_5_aux := 
forall (l1: (@list Z)) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans l1 l0 ) |]
  &&  (os_inv (rev (l0)) )
  **  (Critical (cons (retval) (nil)) l0 )
|--
  [| (GTrans l0 (rev (l0)) ) |] 
  &&  [| (RTrans l1 l0 ) |]
  &&  (Critical (cons (retval) (nil)) l0 )
  **  (os_inv (rev (l0)) )
.

Definition atomic_rev1_partial_solve_wit_5 := atomic_rev1_partial_solve_wit_5_pure -> atomic_rev1_partial_solve_wit_5_aux.

Definition atomic_rev1_which_implies_wit_1 := 
forall (l: (@list Z)) ,
  (os_inv l )
|--
  EX p_v p,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l )
.

Definition atomic_rev1_which_implies_wit_2 := 
forall (rev_l: (@list Z)) (p: Z) (p_v: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v rev_l )
|--
  (os_inv rev_l )
.

(*----- Function atomic_rev2 -----*)

Definition atomic_rev2_return_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical nil (rev (l0)) )
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  (Critical nil l2 )
.

Definition atomic_rev2_partial_solve_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) ,
  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical nil l1 )
|--
  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical nil l1 )
.

Definition atomic_rev2_partial_solve_wit_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical (cons (retval) (nil)) l0 )
  **  (os_inv l0 )
|--
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical (cons (retval) (nil)) l0 )
  **  (os_inv l0 )
.

Definition atomic_rev2_partial_solve_wit_3 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical (cons (retval_2) ((cons (retval) (nil)))) l0 )
  **  (os_inv l0 )
|--
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv l0 )
  **  (Critical (cons (retval_2) ((cons (retval) (nil)))) l0 )
.

Definition atomic_rev2_partial_solve_wit_4 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (retval: Z) (retval_2: Z) (p_v: Z) (p: Z) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l0 )
  **  (Critical (cons (retval_2) ((cons (retval) (nil)))) l0 )
|--
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (sll p_v l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (Critical (cons (retval_2) ((cons (retval) (nil)))) l0 )
.

Definition atomic_rev2_partial_solve_wit_5 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (retval: Z) (retval_2: Z) (p: Z) (retval_3: Z) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (sll retval_3 (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval_3)
  **  (Critical (cons (retval_2) ((cons (retval) (nil)))) l0 )
|--
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> retval_3)
  **  (sll retval_3 (rev (l0)) )
  **  (Critical (cons (retval_2) ((cons (retval) (nil)))) l0 )
.

Definition atomic_rev2_partial_solve_wit_6 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv (rev (l0)) )
  **  (Critical (cons (retval_2) ((cons (retval) (nil)))) l0 )
|--
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical (cons (retval_2) ((cons (retval) (nil)))) l0 )
  **  (os_inv (rev (l0)) )
.

Definition atomic_rev2_partial_solve_wit_7_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical (cons (retval) (nil)) l0 )
  **  (os_inv (rev (l0)) )
  **  ((( &( "y" ) )) # Int  |-> retval_2)
  **  ((( &( "x" ) )) # Int  |-> retval)
|--
  [| (GTrans l0 (rev (l0)) ) |]
.

Definition atomic_rev2_partial_solve_wit_7_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical (cons (retval) (nil)) l0 )
  **  (os_inv (rev (l0)) )
|--
  [| (GTrans l0 (rev (l0)) ) |] 
  &&  [| (RTrans l1 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (Critical (cons (retval) (nil)) l0 )
  **  (os_inv (rev (l0)) )
.

Definition atomic_rev2_partial_solve_wit_7 := atomic_rev2_partial_solve_wit_7_pure -> atomic_rev2_partial_solve_wit_7_aux.

Definition atomic_rev2_which_implies_wit_1 := 
forall (l: (@list Z)) ,
  (os_inv l )
|--
  EX p_v p,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v l )
.

Definition atomic_rev2_which_implies_wit_2 := 
forall (rev_l: (@list Z)) (p: Z) (p_v: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v rev_l )
|--
  (os_inv rev_l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.
Include nested_critical_Strategy_Correct.

Axiom proof_of_atomic_rev1_return_wit_1 : atomic_rev1_return_wit_1.
Axiom proof_of_atomic_rev1_partial_solve_wit_1 : atomic_rev1_partial_solve_wit_1.
Axiom proof_of_atomic_rev1_partial_solve_wit_2 : atomic_rev1_partial_solve_wit_2.
Axiom proof_of_atomic_rev1_partial_solve_wit_3 : atomic_rev1_partial_solve_wit_3.
Axiom proof_of_atomic_rev1_partial_solve_wit_4 : atomic_rev1_partial_solve_wit_4.
Axiom proof_of_atomic_rev1_partial_solve_wit_5_pure : atomic_rev1_partial_solve_wit_5_pure.
Axiom proof_of_atomic_rev1_partial_solve_wit_5 : atomic_rev1_partial_solve_wit_5.
Axiom proof_of_atomic_rev1_which_implies_wit_1 : atomic_rev1_which_implies_wit_1.
Axiom proof_of_atomic_rev1_which_implies_wit_2 : atomic_rev1_which_implies_wit_2.
Axiom proof_of_atomic_rev2_return_wit_1 : atomic_rev2_return_wit_1.
Axiom proof_of_atomic_rev2_partial_solve_wit_1 : atomic_rev2_partial_solve_wit_1.
Axiom proof_of_atomic_rev2_partial_solve_wit_2 : atomic_rev2_partial_solve_wit_2.
Axiom proof_of_atomic_rev2_partial_solve_wit_3 : atomic_rev2_partial_solve_wit_3.
Axiom proof_of_atomic_rev2_partial_solve_wit_4 : atomic_rev2_partial_solve_wit_4.
Axiom proof_of_atomic_rev2_partial_solve_wit_5 : atomic_rev2_partial_solve_wit_5.
Axiom proof_of_atomic_rev2_partial_solve_wit_6 : atomic_rev2_partial_solve_wit_6.
Axiom proof_of_atomic_rev2_partial_solve_wit_7_pure : atomic_rev2_partial_solve_wit_7_pure.
Axiom proof_of_atomic_rev2_partial_solve_wit_7 : atomic_rev2_partial_solve_wit_7.
Axiom proof_of_atomic_rev2_which_implies_wit_1 : atomic_rev2_which_implies_wit_1.
Axiom proof_of_atomic_rev2_which_implies_wit_2 : atomic_rev2_which_implies_wit_2.

End VC_Correct.
