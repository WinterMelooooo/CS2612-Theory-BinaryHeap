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
Require Import guarded_critical_sll_lib.
Import sll_C_Rules.
Require Import guarded_critical_sll_lib.
Import sll_C_Rules.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import guarded_critical_sll_lib.
Import sll_C_Rules.
Local Open Scope stmonad.
Require Import guarded_critical_sll_lib.
Local Open Scope sac.
From SimpleC.EE.concur_guarded_critical Require Import common_strategy_goal.
From SimpleC.EE.concur_guarded_critical Require Import common_strategy_proof.
From SimpleC.EE.concur_guarded_critical Require Import sll_strategy_goal.
From SimpleC.EE.concur_guarded_critical Require Import sll_strategy_proof.
From SimpleC.EE.concur_guarded_critical Require Import safeexec_strategy_goal.
From SimpleC.EE.concur_guarded_critical Require Import safeexec_strategy_proof.
From SimpleC.EE.concur_guarded_critical Require Import guarded_critical_strategy_goal.
From SimpleC.EE.concur_guarded_critical Require Import guarded_critical_strategy_proof.

(*----- Function atomic_rev1 -----*)

Definition atomic_rev1_return_wit_1 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (OutsideCritical q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  EX l2,
  ((( &( "p" ) )) # Ptr  |-> q)
  **  (OutsideCritical q l2 )
.

Definition atomic_rev1_partial_solve_wit_1 := 
forall (l1: (@list Z)) (q: Z) ,
  ((( &( "p" ) )) # Ptr  |-> q)
  **  (OutsideCritical q l1 )
|--
  (OutsideCritical q l1 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev1_partial_solve_wit_2 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_C q l1 q0 l0 ) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (os_inv q l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev1_partial_solve_wit_3 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q_v: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  ((q) # Ptr  |-> q_v)
  **  (sll q_v l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (sll q_v l0 )
  **  ((q) # Ptr  |-> q_v)
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev1_partial_solve_wit_4 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (sll retval (rev (l0)) )
  **  ((q) # Ptr  |-> retval)
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  ((q) # Ptr  |-> retval)
  **  (sll retval (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev1_partial_solve_wit_5_pure := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |]
.

Definition atomic_rev1_partial_solve_wit_5_aux := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev1_partial_solve_wit_5 := atomic_rev1_partial_solve_wit_5_pure -> atomic_rev1_partial_solve_wit_5_aux.

Definition atomic_rev1_which_implies_wit_1 := 
forall (q: Z) (l: (@list Z)) ,
  (os_inv q l )
|--
  EX q_v,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v l )
.

Definition atomic_rev1_which_implies_wit_2 := 
forall (q: Z) (rev_l: (@list Z)) (q_v: Z) ,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v rev_l )
|--
  (os_inv q rev_l )
.

(*----- Function atomic_rev2 -----*)

Definition atomic_rev2_return_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (OutsideCritical q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> q)
  **  (OutsideCritical q l2 )
.

Definition atomic_rev2_partial_solve_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) ,
  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> q)
  **  (OutsideCritical q l1 )
|--
  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (OutsideCritical q l1 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev2_partial_solve_wit_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_C q l1 q0 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv q l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev2_partial_solve_wit_3 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q_v: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((q) # Ptr  |-> q_v)
  **  (sll q_v l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (sll q_v l0 )
  **  ((q) # Ptr  |-> q_v)
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev2_partial_solve_wit_4 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (sll retval (rev (l0)) )
  **  ((q) # Ptr  |-> retval)
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  ((q) # Ptr  |-> retval)
  **  (sll retval (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev2_partial_solve_wit_5_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |]
.

Definition atomic_rev2_partial_solve_wit_5_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev X ) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev2_partial_solve_wit_5 := atomic_rev2_partial_solve_wit_5_pure -> atomic_rev2_partial_solve_wit_5_aux.

Definition atomic_rev2_which_implies_wit_1 := 
forall (q: Z) (l: (@list Z)) ,
  (os_inv q l )
|--
  EX q_v,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v l )
.

Definition atomic_rev2_which_implies_wit_2 := 
forall (q: Z) (rev_l: (@list Z)) (q_v: Z) ,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v rev_l )
|--
  (os_inv q rev_l )
.

(*----- Function atomic_rev_twice1 -----*)

Definition atomic_rev_twice1_return_wit_1 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) ,
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (OutsideCritical q (rev (l0_2)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  EX l2,
  ((( &( "p" ) )) # Ptr  |-> q)
  **  (OutsideCritical q l2 )
.

Definition atomic_rev_twice1_partial_solve_wit_1 := 
forall (l1: (@list Z)) (q: Z) ,
  ((( &( "p" ) )) # Ptr  |-> q)
  **  (OutsideCritical q l1 )
|--
  (OutsideCritical q l1 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_2 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_C q l1 q0 l0 ) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (os_inv q l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_3 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q_v: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  ((q) # Ptr  |-> q_v)
  **  (sll q_v l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (sll q_v l0 )
  **  ((q) # Ptr  |-> q_v)
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_4 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (sll retval (rev (l0)) )
  **  ((q) # Ptr  |-> retval)
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  ((q) # Ptr  |-> retval)
  **  (sll retval (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_5_pure := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |]
.

Definition atomic_rev_twice1_partial_solve_wit_5_aux := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_5 := atomic_rev_twice1_partial_solve_wit_5_pure -> atomic_rev_twice1_partial_solve_wit_5_aux.

Definition atomic_rev_twice1_partial_solve_wit_6 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (OutsideCritical q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (OutsideCritical q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_7 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) ,
  [| (RTrans_C q (rev (l0)) q0_2 l0_2 ) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (InsideCritical q0_2 l0_2 )
  **  (os_inv q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (os_inv q l0_2 )
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_8 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) (q_v: Z) ,
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  ((q) # Ptr  |-> q_v)
  **  (sll q_v l0_2 )
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (sll q_v l0_2 )
  **  ((q) # Ptr  |-> q_v)
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_9 := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) (retval: Z) ,
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (sll retval (rev (l0_2)) )
  **  ((q) # Ptr  |-> retval)
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  ((q) # Ptr  |-> retval)
  **  (sll retval (rev (l0_2)) )
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_10_pure := 
forall (l1: (@list Z)) (q: Z) (q0_2: Z) (l0_2: (@list Z)) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs (rev (l0_2)) l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (RTrans_Abs l1 l0_2 ) |] 
  &&  [| (q = q0_2) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |]
.

Definition atomic_rev_twice1_partial_solve_wit_10_aux := 
forall (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) ,
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (os_inv q (rev (l0_2)) )
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0_2 l0_2 q (rev (l0_2)) ) |] 
  &&  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |]
  &&  (InsideCritical q0_2 l0_2 )
  **  (os_inv q (rev (l0_2)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice1_partial_solve_wit_10 := atomic_rev_twice1_partial_solve_wit_10_pure -> atomic_rev_twice1_partial_solve_wit_10_aux.

Definition atomic_rev_twice1_which_implies_wit_1 := 
forall (q: Z) (l: (@list Z)) ,
  (os_inv q l )
|--
  EX q_v,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v l )
.

Definition atomic_rev_twice1_which_implies_wit_2 := 
forall (q: Z) (rev_l: (@list Z)) (q_v: Z) ,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v rev_l )
|--
  (os_inv q rev_l )
.

Definition atomic_rev_twice1_which_implies_wit_3 := 
forall (q: Z) (l: (@list Z)) ,
  (os_inv q l )
|--
  EX q_v,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v l )
.

Definition atomic_rev_twice1_which_implies_wit_4 := 
forall (q: Z) (rev_l2: (@list Z)) (q_v: Z) ,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v rev_l2 )
|--
  (os_inv q rev_l2 )
.

(*----- Function atomic_rev_twice2 -----*)

Definition atomic_rev_twice2_return_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) ,
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (OutsideCritical q (rev (l0_2)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  EX l2,
  [| (safeExec (LastSeen (l2)) (return (tt)) X ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> q)
  **  (OutsideCritical q l2 )
.

Definition atomic_rev_twice2_partial_solve_wit_1 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) ,
  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> q)
  **  (OutsideCritical q l1 )
|--
  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (OutsideCritical q l1 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_2 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_C q l1 q0 l0 ) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (os_inv q l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_3 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q_v: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  ((q) # Ptr  |-> q_v)
  **  (sll q_v l0 )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (sll q_v l0 )
  **  ((q) # Ptr  |-> q_v)
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_4 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (retval: Z) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (sll retval (rev (l0)) )
  **  ((q) # Ptr  |-> retval)
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  ((q) # Ptr  |-> retval)
  **  (sll retval (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_5_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |]
.

Definition atomic_rev_twice2_partial_solve_wit_5_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (InsideCritical q0 l0 )
  **  (os_inv q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_5 := atomic_rev_twice2_partial_solve_wit_5_pure -> atomic_rev_twice2_partial_solve_wit_5_aux.

Definition atomic_rev_twice2_partial_solve_wit_6 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (OutsideCritical q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (OutsideCritical q (rev (l0)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_7 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) ,
  [| (RTrans_C q (rev (l0)) q0_2 l0_2 ) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (InsideCritical q0_2 l0_2 )
  **  (os_inv q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (os_inv q l0_2 )
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_8 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) (q_v: Z) ,
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  ((q) # Ptr  |-> q_v)
  **  (sll q_v l0_2 )
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (sll q_v l0_2 )
  **  ((q) # Ptr  |-> q_v)
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_9 := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) (retval: Z) ,
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (sll retval (rev (l0_2)) )
  **  ((q) # Ptr  |-> retval)
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  ((q) # Ptr  |-> retval)
  **  (sll retval (rev (l0_2)) )
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_10_pure := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0_2: Z) (l0_2: (@list Z)) (q0: Z) (l0: (@list Z)) ,
  [| (RTrans_Abs (rev (l0_2)) l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (RTrans_Abs l1 l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (os_inv q (rev (l0)) )
  **  (InsideCritical q0 l0 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0 l0 q (rev (l0)) ) |]
.

Definition atomic_rev_twice2_partial_solve_wit_10_aux := 
forall (X: (unit -> (((@list Z) -> Prop) -> Prop))) (l1: (@list Z)) (q: Z) (q0: Z) (l0: (@list Z)) (q0_2: Z) (l0_2: (@list Z)) ,
  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (os_inv q (rev (l0_2)) )
  **  (InsideCritical q0_2 l0_2 )
  **  ((( &( "p" ) )) # Ptr  |-> q)
|--
  [| (GTrans_C q0_2 l0_2 q (rev (l0_2)) ) |] 
  &&  [| (RTrans_Abs (rev (l0)) l0_2 ) |] 
  &&  [| (q = q0_2) |] 
  &&  [| (RTrans_Abs l1 l0 ) |] 
  &&  [| (q = q0) |] 
  &&  [| (safeExec (LastSeen (l1)) atomic_rev_twice X ) |]
  &&  (InsideCritical q0_2 l0_2 )
  **  (os_inv q (rev (l0_2)) )
  **  ((( &( "p" ) )) # Ptr  |-> q)
.

Definition atomic_rev_twice2_partial_solve_wit_10 := atomic_rev_twice2_partial_solve_wit_10_pure -> atomic_rev_twice2_partial_solve_wit_10_aux.

Definition atomic_rev_twice2_which_implies_wit_1 := 
forall (q: Z) (l: (@list Z)) ,
  (os_inv q l )
|--
  EX q_v,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v l )
.

Definition atomic_rev_twice2_which_implies_wit_2 := 
forall (q: Z) (rev_l: (@list Z)) (q_v: Z) ,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v rev_l )
|--
  (os_inv q rev_l )
.

Definition atomic_rev_twice2_which_implies_wit_3 := 
forall (q: Z) (l: (@list Z)) ,
  (os_inv q l )
|--
  EX q_v,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v l )
.

Definition atomic_rev_twice2_which_implies_wit_4 := 
forall (q: Z) (rev_l2: (@list Z)) (q_v: Z) ,
  ((q) # Ptr  |-> q_v)
  **  (sll q_v rev_l2 )
|--
  (os_inv q rev_l2 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.
Include guarded_critical_Strategy_Correct.

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
Axiom proof_of_atomic_rev2_partial_solve_wit_5_pure : atomic_rev2_partial_solve_wit_5_pure.
Axiom proof_of_atomic_rev2_partial_solve_wit_5 : atomic_rev2_partial_solve_wit_5.
Axiom proof_of_atomic_rev2_which_implies_wit_1 : atomic_rev2_which_implies_wit_1.
Axiom proof_of_atomic_rev2_which_implies_wit_2 : atomic_rev2_which_implies_wit_2.
Axiom proof_of_atomic_rev_twice1_return_wit_1 : atomic_rev_twice1_return_wit_1.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_1 : atomic_rev_twice1_partial_solve_wit_1.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_2 : atomic_rev_twice1_partial_solve_wit_2.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_3 : atomic_rev_twice1_partial_solve_wit_3.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_4 : atomic_rev_twice1_partial_solve_wit_4.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_5_pure : atomic_rev_twice1_partial_solve_wit_5_pure.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_5 : atomic_rev_twice1_partial_solve_wit_5.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_6 : atomic_rev_twice1_partial_solve_wit_6.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_7 : atomic_rev_twice1_partial_solve_wit_7.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_8 : atomic_rev_twice1_partial_solve_wit_8.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_9 : atomic_rev_twice1_partial_solve_wit_9.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_10_pure : atomic_rev_twice1_partial_solve_wit_10_pure.
Axiom proof_of_atomic_rev_twice1_partial_solve_wit_10 : atomic_rev_twice1_partial_solve_wit_10.
Axiom proof_of_atomic_rev_twice1_which_implies_wit_1 : atomic_rev_twice1_which_implies_wit_1.
Axiom proof_of_atomic_rev_twice1_which_implies_wit_2 : atomic_rev_twice1_which_implies_wit_2.
Axiom proof_of_atomic_rev_twice1_which_implies_wit_3 : atomic_rev_twice1_which_implies_wit_3.
Axiom proof_of_atomic_rev_twice1_which_implies_wit_4 : atomic_rev_twice1_which_implies_wit_4.
Axiom proof_of_atomic_rev_twice2_return_wit_1 : atomic_rev_twice2_return_wit_1.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_1 : atomic_rev_twice2_partial_solve_wit_1.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_2 : atomic_rev_twice2_partial_solve_wit_2.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_3 : atomic_rev_twice2_partial_solve_wit_3.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_4 : atomic_rev_twice2_partial_solve_wit_4.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_5_pure : atomic_rev_twice2_partial_solve_wit_5_pure.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_5 : atomic_rev_twice2_partial_solve_wit_5.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_6 : atomic_rev_twice2_partial_solve_wit_6.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_7 : atomic_rev_twice2_partial_solve_wit_7.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_8 : atomic_rev_twice2_partial_solve_wit_8.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_9 : atomic_rev_twice2_partial_solve_wit_9.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_10_pure : atomic_rev_twice2_partial_solve_wit_10_pure.
Axiom proof_of_atomic_rev_twice2_partial_solve_wit_10 : atomic_rev_twice2_partial_solve_wit_10.
Axiom proof_of_atomic_rev_twice2_which_implies_wit_1 : atomic_rev_twice2_which_implies_wit_1.
Axiom proof_of_atomic_rev_twice2_which_implies_wit_2 : atomic_rev_twice2_which_implies_wit_2.
Axiom proof_of_atomic_rev_twice2_which_implies_wit_3 : atomic_rev_twice2_which_implies_wit_3.
Axiom proof_of_atomic_rev_twice2_which_implies_wit_4 : atomic_rev_twice2_which_implies_wit_4.

End VC_Correct.
