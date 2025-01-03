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
Require Import fieldtest_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import fieldtest_strategy_goal.
From SimpleC.EE Require Import fieldtest_strategy_proof.

(*----- Function f -----*)

Definition f_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((y_pre) # Int  |-> (p.(b) (1)))
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition f_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) > 2) |] 
  &&  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((y_pre) # Int  |-> (p.(b) (1)))
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| False |]
.

Definition f_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) <= 2) |] 
  &&  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((y_pre) # Int  |-> (p.(b) (1)))
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (((p.(a) (1)) + (p.(b) (1)) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((p.(a) (1)) + (p.(b) (1)) )) |]
.

Definition f_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) <= 2) |] 
  &&  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((y_pre) # Int  |-> (p.(b) (1)))
|--
  [| (((p.(a) (1)) + (p.(b) (1)) ) = ((p.(a) (1)) + (p.(b) (1)) )) |]
  &&  (IntPairSep x_pre y_pre p )
.

Definition f_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  (IntPairSep x_pre y_pre p )
|--
  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((y_pre) # Int  |-> (p.(b) (1)))
.

(*----- Function g -----*)

Definition g_safety_wit_1 := 
forall (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b) (1)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition g_safety_wit_2 := 
forall (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) > 2) |] 
  &&  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b) (1)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| False |]
.

Definition g_safety_wit_3 := 
forall (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) <= 2) |] 
  &&  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b) (1)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (((p.(a) (1)) + (p.(b) (1)) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((p.(a) (1)) + (p.(b) (1)) )) |]
.

Definition g_return_wit_1 := 
forall (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) <= 2) |] 
  &&  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b) (1)))
|--
  [| (((p.(a) (1)) + (p.(b) (1)) ) = ((p.(a) (1)) + (p.(b) (1)) )) |]
  &&  (IntPairSep2 x_pre p )
.

Definition g_partial_solve_wit_1 := 
forall (x_pre: Z) (p: IntPair) ,
  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  (IntPairSep2 x_pre p )
|--
  [| ((p.(a) (1)) = 1) |] 
  &&  [| ((p.(b) (1)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a) (1)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b) (1)))
.

(*----- Function g2 -----*)

Definition g2_safety_wit_1 := 
forall (A: Type) (x_pre: Z) (b0: A) (a0: A) (p: (@Pair A)) ,
  [| ((p.(a1) (a0)) = 1) |] 
  &&  [| ((p.(b1) (b0)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a1) (a0)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b1) (b0)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition g2_safety_wit_2 := 
forall (A: Type) (x_pre: Z) (b0: A) (a0: A) (p: (@Pair A)) ,
  [| ((p.(a1) (a0)) > 2) |] 
  &&  [| ((p.(a1) (a0)) = 1) |] 
  &&  [| ((p.(b1) (b0)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a1) (a0)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b1) (b0)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| False |]
.

Definition g2_safety_wit_3 := 
forall (A: Type) (x_pre: Z) (b0: A) (a0: A) (p: (@Pair A)) ,
  [| ((p.(a1) (a0)) <= 2) |] 
  &&  [| ((p.(a1) (a0)) = 1) |] 
  &&  [| ((p.(b1) (b0)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a1) (a0)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b1) (b0)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (((p.(a1) (a0)) + (p.(b1) (b0)) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((p.(a1) (a0)) + (p.(b1) (b0)) )) |]
.

Definition g2_return_wit_1 := 
forall (A: Type) (x_pre: Z) (b0: A) (a0: A) (p: (@Pair A)) ,
  [| ((p.(a1) (a0)) <= 2) |] 
  &&  [| ((p.(a1) (a0)) = 1) |] 
  &&  [| ((p.(b1) (b0)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a1) (a0)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b1) (b0)))
|--
  [| (((p.(a1) (a0)) + (p.(b1) (b0)) ) = ((p.(a1) (a0)) + (p.(b1) (b0)) )) |]
  &&  (IntPairSep3 x_pre p a0 b0 )
.

Definition g2_partial_solve_wit_1 := 
forall (A: Type) (x_pre: Z) (b0: A) (a0: A) (p: (@Pair A)) ,
  [| ((p.(a1) (a0)) = 1) |] 
  &&  [| ((p.(b1) (b0)) = 2) |]
  &&  (IntPairSep3 x_pre p a0 b0 )
|--
  [| ((p.(a1) (a0)) = 1) |] 
  &&  [| ((p.(b1) (b0)) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a1) (a0)))
  **  ((( &( "z" ) )) # Int  |-> (p.(b1) (b0)))
.

(*----- Function g3 -----*)

Definition g3_safety_wit_1 := 
forall (x_pre: Z) (p: Pair0) ,
  [| ((p.(a2) ) = 1) |] 
  &&  [| ((p.(b2) ) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a2) ))
  **  ((( &( "z" ) )) # Int  |-> (p.(b2) ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition g3_safety_wit_2 := 
forall (x_pre: Z) (p: Pair0) ,
  [| ((p.(a2) ) > 2) |] 
  &&  [| ((p.(a2) ) = 1) |] 
  &&  [| ((p.(b2) ) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a2) ))
  **  ((( &( "z" ) )) # Int  |-> (p.(b2) ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| False |]
.

Definition g3_safety_wit_3 := 
forall (x_pre: Z) (p: Pair0) ,
  [| ((p.(a2) ) <= 2) |] 
  &&  [| ((p.(a2) ) = 1) |] 
  &&  [| ((p.(b2) ) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a2) ))
  **  ((( &( "z" ) )) # Int  |-> (p.(b2) ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (((p.(a2) ) + (p.(b2) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((p.(a2) ) + (p.(b2) ) )) |]
.

Definition g3_return_wit_1 := 
forall (x_pre: Z) (p: Pair0) ,
  [| ((p.(a2) ) <= 2) |] 
  &&  [| ((p.(a2) ) = 1) |] 
  &&  [| ((p.(b2) ) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a2) ))
  **  ((( &( "z" ) )) # Int  |-> (p.(b2) ))
|--
  [| (((p.(a2) ) + (p.(b2) ) ) = ((p.(a2) ) + (p.(b2) ) )) |]
  &&  (IntPairSep4 x_pre p )
.

Definition g3_partial_solve_wit_1 := 
forall (x_pre: Z) (p: Pair0) ,
  [| ((p.(a2) ) = 1) |] 
  &&  [| ((p.(b2) ) = 2) |]
  &&  (IntPairSep4 x_pre p )
|--
  [| ((p.(a2) ) = 1) |] 
  &&  [| ((p.(b2) ) = 2) |]
  &&  ((x_pre) # Int  |-> (p.(a2) ))
  **  ((( &( "z" ) )) # Int  |-> (p.(b2) ))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include fieldtest_Strategy_Correct.

Axiom proof_of_f_safety_wit_1 : f_safety_wit_1.
Axiom proof_of_f_safety_wit_2 : f_safety_wit_2.
Axiom proof_of_f_safety_wit_3 : f_safety_wit_3.
Axiom proof_of_f_return_wit_1 : f_return_wit_1.
Axiom proof_of_f_partial_solve_wit_1 : f_partial_solve_wit_1.
Axiom proof_of_g_safety_wit_1 : g_safety_wit_1.
Axiom proof_of_g_safety_wit_2 : g_safety_wit_2.
Axiom proof_of_g_safety_wit_3 : g_safety_wit_3.
Axiom proof_of_g_return_wit_1 : g_return_wit_1.
Axiom proof_of_g_partial_solve_wit_1 : g_partial_solve_wit_1.
Axiom proof_of_g2_safety_wit_1 : g2_safety_wit_1.
Axiom proof_of_g2_safety_wit_2 : g2_safety_wit_2.
Axiom proof_of_g2_safety_wit_3 : g2_safety_wit_3.
Axiom proof_of_g2_return_wit_1 : g2_return_wit_1.
Axiom proof_of_g2_partial_solve_wit_1 : g2_partial_solve_wit_1.
Axiom proof_of_g3_safety_wit_1 : g3_safety_wit_1.
Axiom proof_of_g3_safety_wit_2 : g3_safety_wit_2.
Axiom proof_of_g3_safety_wit_3 : g3_safety_wit_3.
Axiom proof_of_g3_return_wit_1 : g3_return_wit_1.
Axiom proof_of_g3_partial_solve_wit_1 : g3_partial_solve_wit_1.

End VC_Correct.
