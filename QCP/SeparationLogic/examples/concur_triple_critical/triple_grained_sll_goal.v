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
Require Import triple_critical_sll_lib.
Import sll_TC_Rules.
Require Import triple_critical_sll_lib.
Import sll_TC_Rules.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import triple_critical_sll_lib.
Import sll_TC_Rules.
Local Open Scope stmonad.
Require Import triple_critical_sll_lib.
Local Open Scope sac.
From SimpleC.EE.concur_triple_critical Require Import common_strategy_goal.
From SimpleC.EE.concur_triple_critical Require Import common_strategy_proof.
From SimpleC.EE.concur_triple_critical Require Import sll_strategy_goal.
From SimpleC.EE.concur_triple_critical Require Import sll_strategy_proof.
From SimpleC.EE.concur_triple_critical Require Import safeexec_strategy_goal.
From SimpleC.EE.concur_triple_critical Require Import safeexec_strategy_proof.
From SimpleC.EE.concur_triple_critical Require Import triple_critical_strategy_goal.
From SimpleC.EE.concur_triple_critical Require Import triple_critical_strategy_proof.

(*----- Function atomic_rev1 -----*)

Definition atomic_rev1_return_wit_1 := 
forall (l1: (((@list Z) * (@list Z)) * (@list Z))) (q: ((Z * Z) * Z)) (p_2: Z) (q0: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p_2 = (fst ((fst (q))))) |]
  &&  (OutsideCritical q (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
|--
  EX l2 p,
  [| (p = (fst ((fst (q))))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  (OutsideCritical q l2 )
.

Definition atomic_rev1_partial_solve_wit_1 := 
forall (l1: (((@list Z) * (@list Z)) * (@list Z))) (q: ((Z * Z) * Z)) (p: Z) ,
  [| (p = (fst ((fst (q))))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  (OutsideCritical q l1 )
|--
  [| (p = (fst ((fst (q))))) |]
  &&  (OutsideCritical q l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_partial_solve_wit_2 := 
forall (l1: (((@list Z) * (@list Z)) * (@list Z))) (q: ((Z * Z) * Z)) (p: Z) (q0: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_C q l1 q0 l0 ) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (os_inv q l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_partial_solve_wit_3 := 
forall (l1: (((@list Z) * (@list Z)) * (@list Z))) (q: ((Z * Z) * Z)) (p: Z) (q0: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (v_3: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (((fst ((fst (q))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  ((p) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_partial_solve_wit_4 := 
forall (l1: (((@list Z) * (@list Z)) * (@list Z))) (q: ((Z * Z) * Z)) (p: Z) (q0: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (v_3: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  ((p) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (sll v_3 (fst ((fst (l0)))) )
  **  ((p) # Ptr  |-> v_3)
  **  (((snd ((fst (q))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_partial_solve_wit_5 := 
forall (l1: (((@list Z) * (@list Z)) * (@list Z))) (q: ((Z * Z) * Z)) (p: Z) (q0: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (retval: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (sll retval (rev ((fst ((fst (l0)))))) )
  **  ((p) # Ptr  |-> retval)
  **  (((snd ((fst (q))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (((fst ((fst (q))))) # Ptr  |-> retval)
  **  (sll retval (rev ((fst ((fst (l0)))))) )
  **  (((snd ((fst (q))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_partial_solve_wit_6_pure := 
forall (l1: (((@list Z) * (@list Z)) * (@list Z))) (q: ((Z * Z) * Z)) (p: Z) (q0: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (os_inv q (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (GTrans_C q0 l0 q (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) ) |]
.

Definition atomic_rev1_partial_solve_wit_6_aux := 
forall (l1: (((@list Z) * (@list Z)) * (@list Z))) (q: ((Z * Z) * Z)) (p: Z) (q0: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (os_inv q (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (GTrans_C q0 l0 q (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) ) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (p = (fst ((fst (q))))) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_partial_solve_wit_6 := atomic_rev1_partial_solve_wit_6_pure -> atomic_rev1_partial_solve_wit_6_aux.

Definition atomic_rev1_which_implies_wit_1 := 
forall (q: ((Z * Z) * Z)) (l: (((@list Z) * (@list Z)) * (@list Z))) ,
  (os_inv q l )
|--
  EX v v_2 v_3,
  (((fst ((fst (q))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l)))) )
  **  (((snd ((fst (q))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l)))) )
  **  (((snd (q))) # Ptr  |-> v)
  **  (sll v (snd (l)) )
.

Definition atomic_rev1_which_implies_wit_2 := 
forall (q: ((Z * Z) * Z)) (rev_l: (@list Z)) (l0: (@list Z)) (l: (@list Z)) (v_3: Z) (v_2: Z) (v: Z) ,
  (((fst ((fst (q))))) # Ptr  |-> v_3)
  **  (sll v_3 rev_l )
  **  (((snd ((fst (q))))) # Ptr  |-> v_2)
  **  (sll v_2 l )
  **  (((snd (q))) # Ptr  |-> v)
  **  (sll v l0 )
|--
  (os_inv q (prod3 (rev_l) (l) (l0)) )
.

(*----- Function atomic_rev1_2 -----*)

Definition atomic_rev1_2_return_wit_1 := 
forall (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p_2: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |]
  &&  (OutsideCritical q0 (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
|--
  EX p l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  (OutsideCritical q0 l2 )
.

Definition atomic_rev1_2_partial_solve_wit_1 := 
forall (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) ,
  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  (OutsideCritical q0 l1 )
|--
  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (OutsideCritical q0 l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_2_partial_solve_wit_2 := 
forall (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_C q0 l1 q0_2 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (InsideCritical q0_2 l0 )
  **  (os_inv q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (os_inv q0 l0 )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_2_partial_solve_wit_3 := 
forall (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (v_3: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  ((p) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_2_partial_solve_wit_4 := 
forall (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (v_3: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  ((p) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (sll v_3 (fst ((fst (l0)))) )
  **  ((p) # Ptr  |-> v_3)
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_2_partial_solve_wit_5 := 
forall (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (retval: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (sll retval (rev ((fst ((fst (l0)))))) )
  **  ((p) # Ptr  |-> retval)
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (((fst ((fst (q0))))) # Ptr  |-> retval)
  **  (sll retval (rev ((fst ((fst (l0)))))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_2_partial_solve_wit_6_pure := 
forall (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (os_inv q0 (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (GTrans_C q0_2 l0 q0 (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) ) |]
.

Definition atomic_rev1_2_partial_solve_wit_6_aux := 
forall (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (os_inv q0 (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (GTrans_C q0_2 l0 q0 (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) ) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_1_rev X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  (InsideCritical q0_2 l0 )
  **  (os_inv q0 (prod3 ((rev ((fst ((fst (l0))))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition atomic_rev1_2_partial_solve_wit_6 := atomic_rev1_2_partial_solve_wit_6_pure -> atomic_rev1_2_partial_solve_wit_6_aux.

Definition atomic_rev1_2_which_implies_wit_1 := 
forall (q0: ((Z * Z) * Z)) (l: (((@list Z) * (@list Z)) * (@list Z))) ,
  (os_inv q0 l )
|--
  EX v v_2 v_3,
  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l)) )
.

Definition atomic_rev1_2_which_implies_wit_2 := 
forall (q0: ((Z * Z) * Z)) (rev_l: (@list Z)) (l0: (@list Z)) (l: (@list Z)) (v_3: Z) (v_2: Z) (v: Z) ,
  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 rev_l )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 l )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v l0 )
|--
  (os_inv q0 (prod3 (rev_l) (l) (l0)) )
.

(*----- Function atomic_pop2_2 -----*)

Definition atomic_pop2_2_return_wit_1_1 := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q_3: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v_2: Z) (l0_2: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| ((snd ((fst (l0)))) = (cons (x_pre_v_2) (l0_2))) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |]
  &&  (OutsideCritical q0 (prod3 ((fst ((fst (l0))))) (l0_2) ((snd (l0)))) )
  **  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((( &( "q" ) )) # Ptr  |-> q_3)
|--
  (EX q l2,
  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (return (None)) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |->_))
  ||
  (EX q_2 l2_2 x_pre_v,
  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (return ((Some (x_pre_v)))) X ) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  (OutsideCritical q0 l2_2 ))
.

Definition atomic_pop2_2_return_wit_1_2 := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q_3: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ((snd ((fst (l0)))) = nil) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |]
  &&  (OutsideCritical q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_3)
|--
  (EX q l2,
  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (return (None)) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |->_))
  ||
  (EX q_2 l2_2 x_pre_v,
  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (return ((Some (x_pre_v)))) X ) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  (OutsideCritical q0 l2_2 ))
.

Definition atomic_pop2_2_partial_solve_wit_1 := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) ,
  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l1 )
  **  ((x_pre) # Int  |->_)
|--
  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (OutsideCritical q0 l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop2_2_partial_solve_wit_2 := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_C q0 l1 q0_2 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (InsideCritical q0_2 l0 )
  **  (os_inv q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((x_pre) # Int  |->_)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (os_inv q0 l0 )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((x_pre) # Int  |->_)
.

Definition atomic_pop2_2_partial_solve_wit_3 := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (v_3: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((x_pre) # Int  |->_)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  ((q) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  ((x_pre) # Int  |->_)
  **  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
.

Definition atomic_pop2_2_partial_solve_wit_4 := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (p_pre_v: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ((snd ((fst (l0)))) = nil) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  ((q) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v (snd ((fst (l0)))) )
  **  ((x_pre) # Int  |->_)
  **  (((fst ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (fst ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
|--
  [| (retval = 0) |] 
  &&  [| ((snd ((fst (l0)))) = nil) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (((fst ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  ((x_pre) # Int  |->_)
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
.

Definition atomic_pop2_2_partial_solve_wit_5 := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (p_pre_v: Z) (x_pre_v: Z) (l0_2: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| ((snd ((fst (l0)))) = (cons (x_pre_v) (l0_2))) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((q) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l0_2 )
  **  (((fst ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (fst ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
|--
  [| (retval = 1) |] 
  &&  [| ((snd ((fst (l0)))) = (cons (x_pre_v) (l0_2))) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (((fst ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l0_2 )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
.

Definition atomic_pop2_2_partial_solve_wit_6_pure := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v: Z) (l0_2: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| ((snd ((fst (l0)))) = (cons (x_pre_v) (l0_2))) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (os_inv q0 (prod3 ((fst ((fst (l0))))) (l0_2) ((snd (l0)))) )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "ret" ) )) # Int  |-> retval)
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0_2 l0 q0 (prod3 ((fst ((fst (l0))))) (l0_2) ((snd (l0)))) ) |]
.

Definition atomic_pop2_2_partial_solve_wit_6_aux := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v: Z) (l0_2: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| ((snd ((fst (l0)))) = (cons (x_pre_v) (l0_2))) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (os_inv q0 (prod3 ((fst ((fst (l0))))) (l0_2) ((snd (l0)))) )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0_2 l0 q0 (prod3 ((fst ((fst (l0))))) (l0_2) ((snd (l0)))) ) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((snd ((fst (l0)))) = (cons (x_pre_v) (l0_2))) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (InsideCritical q0_2 l0 )
  **  (os_inv q0 (prod3 ((fst ((fst (l0))))) (l0_2) ((snd (l0)))) )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q)
.

Definition atomic_pop2_2_partial_solve_wit_6 := atomic_pop2_2_partial_solve_wit_6_pure -> atomic_pop2_2_partial_solve_wit_6_aux.

Definition atomic_pop2_2_partial_solve_wit_7_pure := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ((snd ((fst (l0)))) = nil) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (os_inv q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "ret" ) )) # Int  |-> retval)
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0_2 l0 q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((snd (l0)))) ) |]
.

Definition atomic_pop2_2_partial_solve_wit_7_aux := 
forall (x_pre: Z) (X: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (q: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ((snd ((fst (l0)))) = nil) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (os_inv q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  ((x_pre) # Int  |->_)
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0_2 l0 q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((snd (l0)))) ) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((snd ((fst (l0)))) = nil) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_2_pop X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  (InsideCritical q0_2 l0 )
  **  (os_inv q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((snd (l0)))) )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q)
.

Definition atomic_pop2_2_partial_solve_wit_7 := atomic_pop2_2_partial_solve_wit_7_pure -> atomic_pop2_2_partial_solve_wit_7_aux.

Definition atomic_pop2_2_which_implies_wit_1 := 
forall (q0: ((Z * Z) * Z)) (l: (((@list Z) * (@list Z)) * (@list Z))) ,
  (os_inv q0 l )
|--
  EX v v_2 v_3,
  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l)) )
.

Definition atomic_pop2_2_which_implies_wit_2 := 
forall (q0: ((Z * Z) * Z)) (l2: (@list Z)) (l0: (@list Z)) (l: (@list Z)) (v_3: Z) (v_2: Z) (v: Z) ,
  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 l )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 l0 )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v l2 )
|--
  (os_inv q0 (prod3 (l) (l0) (l2)) )
.

(*----- Function atomic_push2_3 -----*)

Definition atomic_push2_3_return_wit_1 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (r_2: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r_2 = (snd (q0))) |]
  &&  (OutsideCritical q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((cons (x_pre) ((snd (l0)))))) )
  **  ((( &( "r" ) )) # Ptr  |-> r_2)
|--
  EX r l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l2 )
.

Definition atomic_push2_3_partial_solve_wit_1 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (r: Z) ,
  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l1 )
|--
  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (OutsideCritical q0 l1 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition atomic_push2_3_partial_solve_wit_2 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (r: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (RTrans_C q0 l1 q0_2 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (InsideCritical q0_2 l0 )
  **  (os_inv q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (os_inv q0 l0 )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition atomic_push2_3_partial_solve_wit_3 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (r: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (v_3: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((r) # Ptr  |-> v)
  **  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition atomic_push2_3_partial_solve_wit_4 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (r: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (v_3: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((r) # Ptr  |-> v)
  **  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (sll v (snd (l0)) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (sll v (snd (l0)) )
  **  ((r) # Ptr  |-> v)
  **  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l0)))) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition atomic_push2_3_partial_solve_wit_5 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (r: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (v: Z) (v_2: Z) (retval: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (sll retval (cons (x_pre) ((snd (l0)))) )
  **  ((r) # Ptr  |-> retval)
  **  (((fst ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v)
  **  (sll v (snd ((fst (l0)))) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (retval <> 0) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (((fst ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (fst ((fst (l0)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v)
  **  (sll v (snd ((fst (l0)))) )
  **  (((snd (q0))) # Ptr  |-> retval)
  **  (sll retval (cons (x_pre) ((snd (l0)))) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition atomic_push2_3_partial_solve_wit_6_pure := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (r: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (os_inv q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((cons (x_pre) ((snd (l0)))))) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (GTrans_C q0_2 l0 q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((cons (x_pre) ((snd (l0)))))) ) |]
.

Definition atomic_push2_3_partial_solve_wit_6_aux := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (r: Z) (q0_2: ((Z * Z) * Z)) (l0: (((@list Z) * (@list Z)) * (@list Z))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (os_inv q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((cons (x_pre) ((snd (l0)))))) )
  **  (InsideCritical q0_2 l0 )
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (GTrans_C q0_2 l0 q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((cons (x_pre) ((snd (l0)))))) ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q0 = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  (InsideCritical q0_2 l0 )
  **  (os_inv q0 (prod3 ((fst ((fst (l0))))) ((snd ((fst (l0))))) ((cons (x_pre) ((snd (l0)))))) )
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition atomic_push2_3_partial_solve_wit_6 := atomic_push2_3_partial_solve_wit_6_pure -> atomic_push2_3_partial_solve_wit_6_aux.

Definition atomic_push2_3_which_implies_wit_1 := 
forall (q0: ((Z * Z) * Z)) (l: (((@list Z) * (@list Z)) * (@list Z))) ,
  (os_inv q0 l )
|--
  EX v v_2 v_3,
  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 (fst ((fst (l)))) )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 (snd ((fst (l)))) )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v (snd (l)) )
.

Definition atomic_push2_3_which_implies_wit_2 := 
forall (q0: ((Z * Z) * Z)) (l2: (@list Z)) (l0: (@list Z)) (l: (@list Z)) (v_3: Z) (v_2: Z) (v: Z) ,
  (((fst ((fst (q0))))) # Ptr  |-> v_3)
  **  (sll v_3 l )
  **  (((snd ((fst (q0))))) # Ptr  |-> v_2)
  **  (sll v_2 l0 )
  **  (((snd (q0))) # Ptr  |-> v)
  **  (sll v l2 )
|--
  (os_inv q0 (prod3 (l) (l0) (l2)) )
.

(*----- Function triple_work_C -----*)

Definition triple_work_C_safety_wit_1 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q_2: Z) (r: Z) (p_2: Z) (q: Z) (l2: (((@list Z) * (@list Z)) * (@list Z))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push_loc0 (None)) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| False |]
.

Definition triple_work_C_safety_wit_2 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q_2: Z) (r: Z) (p_2: Z) (q: Z) (l2: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push_loc0 ((Some (x_pre_v)))) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| False |]
.

Definition triple_work_C_entail_wit_1 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) ,
  [| (safeExec (LastSeen (l1)) triple_work X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l1 )
  **  ((x_pre) # Int  |->_)
|--
  [| (safeExec (LastSeen (l1)) (bind (atomic_1_rev) (pop2_push3)) X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l1 )
  **  ((x_pre) # Int  |->_)
.

Definition triple_work_C_entail_wit_2 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) (p_2: Z) (l2: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (safeExec (LastSeen (l2)) (pop2_push3 (tt)) X ) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  ((x_pre) # Int  |->_)
|--
  EX l1,
  [| (safeExec (LastSeen (l1)) (bind (atomic_2_pop) (atomic_3_push_loc0)) X ) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  ((x_pre) # Int  |->_)
.

Definition triple_work_C_entail_wit_3_1 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q_2: Z) (r: Z) (p_2: Z) (q_3: Z) (l2_2: (((@list Z) * (@list Z)) * (@list Z))) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (atomic_3_push_loc0 (None)) X ) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_3)
  **  (OutsideCritical q0 l2_2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  EX q l2 x_pre_v retval,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push_loc0 ((Some (x_pre_v)))) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition triple_work_C_entail_wit_3_2 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q_2: Z) (r: Z) (p_2: Z) (q_3: Z) (l2_2: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v_2: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (atomic_3_push_loc0 ((Some (x_pre_v_2)))) X ) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((( &( "q" ) )) # Ptr  |-> q_3)
  **  (OutsideCritical q0 l2_2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  EX q l2 x_pre_v retval,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push_loc0 ((Some (x_pre_v)))) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition triple_work_C_entail_wit_4_1 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q_2: Z) (r: Z) (p_2: Z) (q_3: Z) (l2_2: (((@list Z) * (@list Z)) * (@list Z))) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (atomic_3_push_loc0 (None)) X ) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_3)
  **  (OutsideCritical q0 l2_2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  EX q l2 retval,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push_loc0 (None)) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition triple_work_C_entail_wit_4_2 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q_2: Z) (r: Z) (p_2: Z) (q_3: Z) (l2_2: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (atomic_3_push_loc0 ((Some (x_pre_v)))) X ) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_3)
  **  (OutsideCritical q0 l2_2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  EX q l2 retval,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push_loc0 (None)) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition triple_work_C_entail_wit_5 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) (p_2: Z) (q_2: Z) (l2: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push_loc0 ((Some (x_pre_v)))) X ) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  EX l1,
  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre_v)) X ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition triple_work_C_return_wit_1_1 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p_2: Z) (q_3: Z) (r_2: Z) (p_3: Z) (q_2: Z) (l2_2: (((@list Z) * (@list Z)) * (@list Z))) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (atomic_3_push_loc0 (None)) X ) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (p_3 = (fst ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |] 
  &&  [| (r_2 = (snd (q0))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  (OutsideCritical q0 l2_2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_3)
  **  ((( &( "r" ) )) # Ptr  |-> r_2)
|--
  EX r q p l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |->_)
.

Definition triple_work_C_return_wit_1_2 := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p_2: Z) (q_2: Z) (r_3: Z) (p_3: Z) (q_3: Z) (x_pre_v: Z) (retval: Z) (r_2: Z) (l2_2: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (safeExec (LastSeen (l2_2)) (return (tt)) X ) |] 
  &&  [| (r_2 = (snd (q0))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |] 
  &&  [| (p_3 = (fst ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (r_3 = (snd (q0))) |]
  &&  ((( &( "r" ) )) # Ptr  |-> r_2)
  **  (OutsideCritical q0 l2_2 )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_3)
  **  ((( &( "p" ) )) # Ptr  |-> p_3)
|--
  EX r q p l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |->_)
.

Definition triple_work_C_partial_solve_wit_1_pure := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) ,
  [| (safeExec (LastSeen (l1)) (bind (atomic_1_rev) (pop2_push3)) X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l1 )
  **  ((x_pre) # Int  |->_)
|--
  [| (safeExec (LastSeen (l1)) (bind (atomic_1_rev) (pop2_push3)) X ) |] 
  &&  [| ((fst ((fst (q0)))) = (fst ((fst (q0))))) |]
.

Definition triple_work_C_partial_solve_wit_1_aux := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) ,
  [| (safeExec (LastSeen (l1)) (bind (atomic_1_rev) (pop2_push3)) X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l1 )
  **  ((x_pre) # Int  |->_)
|--
  [| (safeExec (LastSeen (l1)) (bind (atomic_1_rev) (pop2_push3)) X ) |] 
  &&  [| ((fst ((fst (q0)))) = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> (fst ((fst (q0)))))
  **  (OutsideCritical q0 l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  ((x_pre) # Int  |->_)
.

Definition triple_work_C_partial_solve_wit_1 := triple_work_C_partial_solve_wit_1_pure -> triple_work_C_partial_solve_wit_1_aux.

Definition triple_work_C_partial_solve_wit_2_pure := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) (p_2: Z) (l2: (((@list Z) * (@list Z)) * (@list Z))) (l1: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (safeExec (LastSeen (l1)) (bind (atomic_2_pop) (atomic_3_push_loc0)) X ) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  ((x_pre) # Int  |->_)
|--
  [| (safeExec (LastSeen (l2)) (bind (atomic_2_pop) (atomic_3_push_loc0)) X ) |] 
  &&  [| ((snd ((fst (q0)))) = (snd ((fst (q0))))) |] 
  &&  [| (safeExec (LastSeen (l2)) (bind (atomic_2_pop) (atomic_3_push_loc0)) X ) |]
.

Definition triple_work_C_partial_solve_wit_2_aux := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) (p_2: Z) (l2: (((@list Z) * (@list Z)) * (@list Z))) (l1: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (safeExec (LastSeen (l1)) (bind (atomic_2_pop) (atomic_3_push_loc0)) X ) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  ((x_pre) # Int  |->_)
|--
  [| (safeExec (LastSeen (l2)) (bind (atomic_2_pop) (atomic_3_push_loc0)) X ) |] 
  &&  [| ((snd ((fst (q0)))) = (snd ((fst (q0))))) |] 
  &&  [| (safeExec (LastSeen (l2)) (bind (atomic_2_pop) (atomic_3_push_loc0)) X ) |] 
  &&  [| (safeExec (LastSeen (l1)) (bind (atomic_2_pop) (atomic_3_push_loc0)) X ) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> (snd ((fst (q0)))))
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
.

Definition triple_work_C_partial_solve_wit_2 := triple_work_C_partial_solve_wit_2_pure -> triple_work_C_partial_solve_wit_2_aux.

Definition triple_work_C_partial_solve_wit_3_pure := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) (p_2: Z) (q_2: Z) (l2: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v: Z) (retval: Z) (l1: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre_v)) X ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (safeExec (LastSeen (l2)) (atomic_3_push (x_pre_v)) X ) |] 
  &&  [| ((snd (q0)) = (snd (q0))) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push (x_pre_v)) X ) |]
.

Definition triple_work_C_partial_solve_wit_3_aux := 
forall (x_pre: Z) (X: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (q0: ((Z * Z) * Z)) (p: Z) (q: Z) (r: Z) (p_2: Z) (q_2: Z) (l2: (((@list Z) * (@list Z)) * (@list Z))) (x_pre_v: Z) (retval: Z) (l1: (((@list Z) * (@list Z)) * (@list Z))) ,
  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre_v)) X ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  (OutsideCritical q0 l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (safeExec (LastSeen (l2)) (atomic_3_push (x_pre_v)) X ) |] 
  &&  [| ((snd (q0)) = (snd (q0))) |] 
  &&  [| (safeExec (LastSeen (l2)) (atomic_3_push (x_pre_v)) X ) |] 
  &&  [| (safeExec (LastSeen (l1)) (atomic_3_push (x_pre_v)) X ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |] 
  &&  [| (p = (fst ((fst (q0))))) |] 
  &&  [| (q = (snd ((fst (q0))))) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "r" ) )) # Ptr  |-> (snd (q0)))
  **  (OutsideCritical q0 l2 )
  **  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  ((( &( "p" ) )) # Ptr  |-> p_2)
.

Definition triple_work_C_partial_solve_wit_3 := triple_work_C_partial_solve_wit_3_pure -> triple_work_C_partial_solve_wit_3_aux.

Definition atomic_push2_3_derive_aux_push_spec_by_normal_push_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X: (B -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (c: (unit -> (@program ((((@list Z) * (@list Z)) * (@list Z)) -> Prop) B))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) ,
  EX r,
  [| (safeExec (LastSeen (l1)) (bind ((atomic_3_push (x_pre))) (c)) X ) |] 
  &&  [| (r = (snd (q0))) |]
  &&  ((( &( "r" ) )) # Ptr  |-> r)
  **  (OutsideCritical q0 l1 )
|--
EX (q0_2: ((Z * Z) * Z)) (l1_2: (((@list Z) * (@list Z)) * (@list Z))) (X_2: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) ,
  (EX r_3,
  [| (safeExec (LastSeen (l1_2)) (atomic_3_push (x_pre)) X_2 ) |] 
  &&  [| (r_3 = (snd (q0_2))) |]
  &&  ((( &( "r" ) )) # Ptr  |-> r_3)
  **  (OutsideCritical q0_2 l1_2 ))
  **
  ((EX r_4 l2_2,
  [| (safeExec (LastSeen (l2_2)) (return (tt)) X_2 ) |] 
  &&  [| (r_4 = (snd (q0_2))) |]
  &&  ((( &( "r" ) )) # Ptr  |-> r_4)
  **  (OutsideCritical q0_2 l2_2 ))
  -*
  (EX r_2 l2,
  [| (safeExec (LastSeen (l2)) (c (tt)) X ) |] 
  &&  [| (r_2 = (snd (q0))) |]
  &&  ((( &( "r" ) )) # Ptr  |-> r_2)
  **  (OutsideCritical q0 l2 )))
.

Definition atomic_pop2_2_derive_aux_pop_spec_by_normal_pop_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X: (B -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (c: ((@option Z) -> (@program ((((@list Z) * (@list Z)) * (@list Z)) -> Prop) B))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) ,
  EX q,
  [| (safeExec (LastSeen (l1)) (bind (atomic_2_pop) (c)) X ) |] 
  &&  [| (q = (snd ((fst (q0))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q)
  **  (OutsideCritical q0 l1 )
  **  ((x_pre) # Int  |->_)
|--
EX (q0_2: ((Z * Z) * Z)) (l1_2: (((@list Z) * (@list Z)) * (@list Z))) (X_2: ((@option Z) -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) ,
  (EX q_4,
  [| (safeExec (LastSeen (l1_2)) atomic_2_pop X_2 ) |] 
  &&  [| (q_4 = (snd ((fst (q0_2))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_4)
  **  (OutsideCritical q0_2 l1_2 )
  **  ((x_pre) # Int  |->_))
  **
  (((EX q_5 l2_3 x_pre_v_2 retval_2,
  [| (retval_2 = 1) |] 
  &&  [| (safeExec (LastSeen (l2_3)) (return ((Some (x_pre_v_2)))) X_2 ) |] 
  &&  [| (q_5 = (snd ((fst (q0_2))))) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((( &( "q" ) )) # Ptr  |-> q_5)
  **  (OutsideCritical q0_2 l2_3 ))
  ||
  (EX q_6 l2_4 retval_2,
  [| (retval_2 = 0) |] 
  &&  [| (safeExec (LastSeen (l2_4)) (return (None)) X_2 ) |] 
  &&  [| (q_6 = (snd ((fst (q0_2))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_6)
  **  (OutsideCritical q0_2 l2_4 )
  **  ((x_pre) # Int  |->_)))
  -*
  ((EX q_2 l2 x_pre_v retval,
  [| (retval = 1) |] 
  &&  [| (safeExec (LastSeen (l2)) (c ((Some (x_pre_v)))) X ) |] 
  &&  [| (q_2 = (snd ((fst (q0))))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((( &( "q" ) )) # Ptr  |-> q_2)
  **  (OutsideCritical q0 l2 ))
  ||
  (EX q_3 l2_2 retval,
  [| (retval = 0) |] 
  &&  [| (safeExec (LastSeen (l2_2)) (c (None)) X ) |] 
  &&  [| (q_3 = (snd ((fst (q0))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_3)
  **  (OutsideCritical q0 l2_2 )
  **  ((x_pre) # Int  |->_))))
.

Definition atomic_rev1_2_derive_aux_rev_spec_by_normal_rev_spec := 
forall (B: Type) ,
forall (X: (B -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) (c: (unit -> (@program ((((@list Z) * (@list Z)) * (@list Z)) -> Prop) B))) (l1: (((@list Z) * (@list Z)) * (@list Z))) (q0: ((Z * Z) * Z)) ,
  EX p,
  [| (safeExec (LastSeen (l1)) (bind (atomic_1_rev) (c)) X ) |] 
  &&  [| (p = (fst ((fst (q0))))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  (OutsideCritical q0 l1 )
|--
EX (q0_2: ((Z * Z) * Z)) (l1_2: (((@list Z) * (@list Z)) * (@list Z))) (X_2: (unit -> (((((@list Z) * (@list Z)) * (@list Z)) -> Prop) -> Prop))) ,
  (EX p_3,
  [| (safeExec (LastSeen (l1_2)) atomic_1_rev X_2 ) |] 
  &&  [| (p_3 = (fst ((fst (q0_2))))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_3)
  **  (OutsideCritical q0_2 l1_2 ))
  **
  ((EX p_4 l2_2,
  [| (safeExec (LastSeen (l2_2)) (return (tt)) X_2 ) |] 
  &&  [| (p_4 = (fst ((fst (q0_2))))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_4)
  **  (OutsideCritical q0_2 l2_2 ))
  -*
  (EX p_2 l2,
  [| (safeExec (LastSeen (l2)) (c (tt)) X ) |] 
  &&  [| (p_2 = (fst ((fst (q0))))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_2)
  **  (OutsideCritical q0 l2 )))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.
Include triple_critical_Strategy_Correct.

Axiom proof_of_atomic_rev1_return_wit_1 : atomic_rev1_return_wit_1.
Axiom proof_of_atomic_rev1_partial_solve_wit_1 : atomic_rev1_partial_solve_wit_1.
Axiom proof_of_atomic_rev1_partial_solve_wit_2 : atomic_rev1_partial_solve_wit_2.
Axiom proof_of_atomic_rev1_partial_solve_wit_3 : atomic_rev1_partial_solve_wit_3.
Axiom proof_of_atomic_rev1_partial_solve_wit_4 : atomic_rev1_partial_solve_wit_4.
Axiom proof_of_atomic_rev1_partial_solve_wit_5 : atomic_rev1_partial_solve_wit_5.
Axiom proof_of_atomic_rev1_partial_solve_wit_6_pure : atomic_rev1_partial_solve_wit_6_pure.
Axiom proof_of_atomic_rev1_partial_solve_wit_6 : atomic_rev1_partial_solve_wit_6.
Axiom proof_of_atomic_rev1_which_implies_wit_1 : atomic_rev1_which_implies_wit_1.
Axiom proof_of_atomic_rev1_which_implies_wit_2 : atomic_rev1_which_implies_wit_2.
Axiom proof_of_atomic_rev1_2_return_wit_1 : atomic_rev1_2_return_wit_1.
Axiom proof_of_atomic_rev1_2_partial_solve_wit_1 : atomic_rev1_2_partial_solve_wit_1.
Axiom proof_of_atomic_rev1_2_partial_solve_wit_2 : atomic_rev1_2_partial_solve_wit_2.
Axiom proof_of_atomic_rev1_2_partial_solve_wit_3 : atomic_rev1_2_partial_solve_wit_3.
Axiom proof_of_atomic_rev1_2_partial_solve_wit_4 : atomic_rev1_2_partial_solve_wit_4.
Axiom proof_of_atomic_rev1_2_partial_solve_wit_5 : atomic_rev1_2_partial_solve_wit_5.
Axiom proof_of_atomic_rev1_2_partial_solve_wit_6_pure : atomic_rev1_2_partial_solve_wit_6_pure.
Axiom proof_of_atomic_rev1_2_partial_solve_wit_6 : atomic_rev1_2_partial_solve_wit_6.
Axiom proof_of_atomic_rev1_2_which_implies_wit_1 : atomic_rev1_2_which_implies_wit_1.
Axiom proof_of_atomic_rev1_2_which_implies_wit_2 : atomic_rev1_2_which_implies_wit_2.
Axiom proof_of_atomic_pop2_2_return_wit_1_1 : atomic_pop2_2_return_wit_1_1.
Axiom proof_of_atomic_pop2_2_return_wit_1_2 : atomic_pop2_2_return_wit_1_2.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_1 : atomic_pop2_2_partial_solve_wit_1.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_2 : atomic_pop2_2_partial_solve_wit_2.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_3 : atomic_pop2_2_partial_solve_wit_3.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_4 : atomic_pop2_2_partial_solve_wit_4.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_5 : atomic_pop2_2_partial_solve_wit_5.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_6_pure : atomic_pop2_2_partial_solve_wit_6_pure.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_6 : atomic_pop2_2_partial_solve_wit_6.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_7_pure : atomic_pop2_2_partial_solve_wit_7_pure.
Axiom proof_of_atomic_pop2_2_partial_solve_wit_7 : atomic_pop2_2_partial_solve_wit_7.
Axiom proof_of_atomic_pop2_2_which_implies_wit_1 : atomic_pop2_2_which_implies_wit_1.
Axiom proof_of_atomic_pop2_2_which_implies_wit_2 : atomic_pop2_2_which_implies_wit_2.
Axiom proof_of_atomic_push2_3_return_wit_1 : atomic_push2_3_return_wit_1.
Axiom proof_of_atomic_push2_3_partial_solve_wit_1 : atomic_push2_3_partial_solve_wit_1.
Axiom proof_of_atomic_push2_3_partial_solve_wit_2 : atomic_push2_3_partial_solve_wit_2.
Axiom proof_of_atomic_push2_3_partial_solve_wit_3 : atomic_push2_3_partial_solve_wit_3.
Axiom proof_of_atomic_push2_3_partial_solve_wit_4 : atomic_push2_3_partial_solve_wit_4.
Axiom proof_of_atomic_push2_3_partial_solve_wit_5 : atomic_push2_3_partial_solve_wit_5.
Axiom proof_of_atomic_push2_3_partial_solve_wit_6_pure : atomic_push2_3_partial_solve_wit_6_pure.
Axiom proof_of_atomic_push2_3_partial_solve_wit_6 : atomic_push2_3_partial_solve_wit_6.
Axiom proof_of_atomic_push2_3_which_implies_wit_1 : atomic_push2_3_which_implies_wit_1.
Axiom proof_of_atomic_push2_3_which_implies_wit_2 : atomic_push2_3_which_implies_wit_2.
Axiom proof_of_triple_work_C_safety_wit_1 : triple_work_C_safety_wit_1.
Axiom proof_of_triple_work_C_safety_wit_2 : triple_work_C_safety_wit_2.
Axiom proof_of_triple_work_C_entail_wit_1 : triple_work_C_entail_wit_1.
Axiom proof_of_triple_work_C_entail_wit_2 : triple_work_C_entail_wit_2.
Axiom proof_of_triple_work_C_entail_wit_3_1 : triple_work_C_entail_wit_3_1.
Axiom proof_of_triple_work_C_entail_wit_3_2 : triple_work_C_entail_wit_3_2.
Axiom proof_of_triple_work_C_entail_wit_4_1 : triple_work_C_entail_wit_4_1.
Axiom proof_of_triple_work_C_entail_wit_4_2 : triple_work_C_entail_wit_4_2.
Axiom proof_of_triple_work_C_entail_wit_5 : triple_work_C_entail_wit_5.
Axiom proof_of_triple_work_C_return_wit_1_1 : triple_work_C_return_wit_1_1.
Axiom proof_of_triple_work_C_return_wit_1_2 : triple_work_C_return_wit_1_2.
Axiom proof_of_triple_work_C_partial_solve_wit_1_pure : triple_work_C_partial_solve_wit_1_pure.
Axiom proof_of_triple_work_C_partial_solve_wit_1 : triple_work_C_partial_solve_wit_1.
Axiom proof_of_triple_work_C_partial_solve_wit_2_pure : triple_work_C_partial_solve_wit_2_pure.
Axiom proof_of_triple_work_C_partial_solve_wit_2 : triple_work_C_partial_solve_wit_2.
Axiom proof_of_triple_work_C_partial_solve_wit_3_pure : triple_work_C_partial_solve_wit_3_pure.
Axiom proof_of_triple_work_C_partial_solve_wit_3 : triple_work_C_partial_solve_wit_3.
Axiom proof_of_atomic_push2_3_derive_aux_push_spec_by_normal_push_spec : atomic_push2_3_derive_aux_push_spec_by_normal_push_spec.
Axiom proof_of_atomic_pop2_2_derive_aux_pop_spec_by_normal_pop_spec : atomic_pop2_2_derive_aux_pop_spec_by_normal_pop_spec.
Axiom proof_of_atomic_rev1_2_derive_aux_rev_spec_by_normal_rev_spec : atomic_rev1_2_derive_aux_rev_spec_by_normal_rev_spec.

End VC_Correct.
