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
Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function local -----*)

Definition local_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (y_pre >= INT_MIN) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition local_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <= 100) |] 
  &&  [| (y_pre >= 0) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (y_pre >= INT_MIN) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| ((y_pre - (signed_last_nbits (x_pre) (32)) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre - (signed_last_nbits (x_pre) (32)) )) |]
.

Definition local_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre > 100) |] 
  &&  [| (y_pre >= 0) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (y_pre >= INT_MIN) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition local_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre < 0) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (y_pre >= INT_MIN) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # UInt  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition local_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  TT && emp 
|--
  [| (x_pre >= 0) |] 
  &&  [| (y_pre >= INT_MIN) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
.

Definition local_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <= 100) |] 
  &&  [| (y_pre >= 0) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (y_pre >= INT_MIN) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((y_pre - (signed_last_nbits (x_pre) (32)) ) >= INT_MIN) |] 
  &&  [| ((y_pre - (signed_last_nbits (x_pre) (32)) ) <= INT_MAX) |]
  &&  emp
.

Definition local_return_wit_2_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre < 0) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (y_pre >= INT_MIN) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= INT_MAX) |]
  &&  emp
.

Definition local_return_wit_2_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre > 100) |] 
  &&  [| (y_pre >= 0) |] 
  &&  [| (x_pre >= 0) |] 
  &&  [| (y_pre >= INT_MIN) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 >= INT_MIN) |] 
  &&  [| (0 <= INT_MAX) |]
  &&  emp
.

(*----- Function local2 -----*)

Definition local2_return_wit_1 := 
forall (x_pre: Z) ,
  TT && emp 
|--
  [| ((unsigned_last_nbits (((unsigned_last_nbits ((2 * x_pre )) (32)) + 1 )) (32)) = (unsigned_last_nbits (((2 * x_pre ) + 1 )) (32))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_local_safety_wit_1 : local_safety_wit_1.
Axiom proof_of_local_safety_wit_2 : local_safety_wit_2.
Axiom proof_of_local_safety_wit_3 : local_safety_wit_3.
Axiom proof_of_local_safety_wit_4 : local_safety_wit_4.
Axiom proof_of_local_entail_wit_1 : local_entail_wit_1.
Axiom proof_of_local_return_wit_1 : local_return_wit_1.
Axiom proof_of_local_return_wit_2_1 : local_return_wit_2_1.
Axiom proof_of_local_return_wit_2_2 : local_return_wit_2_2.
Axiom proof_of_local2_return_wit_1 : local2_return_wit_1.

End VC_Correct.
