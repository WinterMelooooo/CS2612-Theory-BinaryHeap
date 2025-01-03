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
Require Import int_array_lib.
Require Import sll_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import sll_strategy_goal.
From SimpleC.EE Require Import sll_strategy_proof.

(*----- Function add -----*)

Definition add_safety_wit_1 := 
forall (t_pre: Z) (x: Z) ,
  [| (0 < x) |] 
  &&  [| (x < 200) |] 
  &&  [| (0 < t_pre) |] 
  &&  [| (t_pre < 100) |]
  &&  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
|--
  [| ((x + t_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x + t_pre )) |]
.

Definition add_return_wit_1 := 
forall (t_pre: Z) (x_2: Z) ,
  [| (0 < x_2) |] 
  &&  [| (x_2 < 200) |] 
  &&  [| (0 < t_pre) |] 
  &&  [| (t_pre < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_2 + t_pre ))
|--
  EX x,
  [| (x = (x_2 + t_pre )) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
.

(*----- Function add_call -----*)

Definition add_call_safety_wit_1 := 
forall (x: Z) ,
  [| (0 < x) |] 
  &&  [| (x < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition add_call_safety_wit_2 := 
forall (x_2: Z) (x: Z) ,
  [| (x = (x_2 + 1 )) |] 
  &&  [| (0 < x_2) |] 
  &&  [| (x_2 < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition add_call_safety_wit_3 := 
forall (x_2: Z) (x_3: Z) (x: Z) ,
  [| (x = (x_3 + 2 )) |] 
  &&  [| (x_3 = (x_2 + 1 )) |] 
  &&  [| (0 < x_2) |] 
  &&  [| (x_2 < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition add_call_return_wit_1 := 
forall (x_2: Z) (x_4: Z) (x_5: Z) (x_3: Z) ,
  [| (x_3 = (x_5 + 3 )) |] 
  &&  [| (x_5 = (x_4 + 2 )) |] 
  &&  [| (x_4 = (x_2 + 1 )) |] 
  &&  [| (0 < x_2) |] 
  &&  [| (x_2 < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x_3)
|--
  EX x,
  [| (x = (x_2 + 6 )) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
.

Definition add_call_partial_solve_wit_1_pure := 
forall (x: Z) ,
  [| (0 < x) |] 
  &&  [| (x < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (0 < x) |] 
  &&  [| (x < 200) |] 
  &&  [| (0 < 1) |] 
  &&  [| (1 < 100) |]
.

Definition add_call_partial_solve_wit_1_aux := 
forall (x: Z) ,
  [| (0 < x) |] 
  &&  [| (x < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (0 < x) |] 
  &&  [| (x < 200) |] 
  &&  [| (0 < 1) |] 
  &&  [| (1 < 100) |] 
  &&  [| (0 < x) |] 
  &&  [| (x < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
.

Definition add_call_partial_solve_wit_1 := add_call_partial_solve_wit_1_pure -> add_call_partial_solve_wit_1_aux.

Definition add_call_partial_solve_wit_2_pure := 
forall (x_2: Z) (x: Z) ,
  [| (x = (x_2 + 1 )) |] 
  &&  [| (0 < x_2) |] 
  &&  [| (x_2 < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (0 < x) |] 
  &&  [| (x < 200) |] 
  &&  [| (0 < 2) |] 
  &&  [| (2 < 100) |]
.

Definition add_call_partial_solve_wit_2_aux := 
forall (x: Z) (x_2: Z) ,
  [| (x_2 = (x + 1 )) |] 
  &&  [| (0 < x) |] 
  &&  [| (x < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x_2)
|--
  [| (0 < x_2) |] 
  &&  [| (x_2 < 200) |] 
  &&  [| (0 < 2) |] 
  &&  [| (2 < 100) |] 
  &&  [| (x_2 = (x + 1 )) |] 
  &&  [| (0 < x) |] 
  &&  [| (x < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x_2)
.

Definition add_call_partial_solve_wit_2 := add_call_partial_solve_wit_2_pure -> add_call_partial_solve_wit_2_aux.

Definition add_call_partial_solve_wit_3_pure := 
forall (x_2: Z) (x_3: Z) (x: Z) ,
  [| (x = (x_3 + 2 )) |] 
  &&  [| (x_3 = (x_2 + 1 )) |] 
  &&  [| (0 < x_2) |] 
  &&  [| (x_2 < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (0 < x) |] 
  &&  [| (x < 200) |] 
  &&  [| (0 < 3) |] 
  &&  [| (3 < 100) |]
.

Definition add_call_partial_solve_wit_3_aux := 
forall (x: Z) (x_2: Z) (x_3: Z) ,
  [| (x_3 = (x_2 + 2 )) |] 
  &&  [| (x_2 = (x + 1 )) |] 
  &&  [| (0 < x) |] 
  &&  [| (x < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x_3)
|--
  [| (0 < x_3) |] 
  &&  [| (x_3 < 200) |] 
  &&  [| (0 < 3) |] 
  &&  [| (3 < 100) |] 
  &&  [| (x_3 = (x_2 + 2 )) |] 
  &&  [| (x_2 = (x + 1 )) |] 
  &&  [| (0 < x) |] 
  &&  [| (x < 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x_3)
.

Definition add_call_partial_solve_wit_3 := add_call_partial_solve_wit_3_pure -> add_call_partial_solve_wit_3_aux.

(*----- Function add_rec -----*)

Definition add_rec_safety_wit_1 := 
forall (n_pre: Z) (x: Z) ,
  [| (0 <= x) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x + n_pre ) <= 100) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition add_rec_safety_wit_2 := 
forall (n_pre: Z) (x: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x + n_pre ) <= 100) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
|--
  [| ((x + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x + 1 )) |]
.

Definition add_rec_safety_wit_3 := 
forall (n_pre: Z) (x: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x + n_pre ) <= 100) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition add_rec_safety_wit_4 := 
forall (n_pre: Z) (x: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x + n_pre ) <= 100) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> (x + 1 ))
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition add_rec_safety_wit_5 := 
forall (n_pre: Z) (x: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x + n_pre ) <= 100) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> (x + 1 ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition add_rec_return_wit_1 := 
forall (n_pre: Z) (x_2: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= x_2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x_2 + n_pre ) <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x_2)
|--
  EX x,
  [| (x = (x_2 + n_pre )) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
.

Definition add_rec_return_wit_2 := 
forall (n_pre: Z) (x_2: Z) (x_3: Z) ,
  [| (x_3 = ((x_2 + 1 ) + (n_pre - 1 ) )) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= x_2) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x_2 + n_pre ) <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x_3)
|--
  EX x,
  [| (x = (x_2 + n_pre )) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
.

Definition add_rec_partial_solve_wit_1_pure := 
forall (n_pre: Z) (x: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x + n_pre ) <= 100) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> (x + 1 ))
|--
  [| (0 <= (x + 1 )) |] 
  &&  [| (0 <= (n_pre - 1 )) |] 
  &&  [| (((x + 1 ) + (n_pre - 1 ) ) <= 100) |]
.

Definition add_rec_partial_solve_wit_1_aux := 
forall (n_pre: Z) (x: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x + n_pre ) <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> (x + 1 ))
|--
  [| (0 <= (x + 1 )) |] 
  &&  [| (0 <= (n_pre - 1 )) |] 
  &&  [| (((x + 1 ) + (n_pre - 1 ) ) <= 100) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((x + n_pre ) <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> (x + 1 ))
.

Definition add_rec_partial_solve_wit_1 := add_rec_partial_solve_wit_1_pure -> add_rec_partial_solve_wit_1_aux.

(*----- Function array_sum -----*)

Definition array_sum_safety_wit_1 := 
forall (l: (@list Z)) (i: Z) (n: Z) (a: Z) ,
  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_sum_safety_wit_2 := 
forall (l: (@list Z)) (i: Z) (n: Z) (a: Z) ,
  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_sum_safety_wit_3 := 
forall (l: (@list Z)) (i_2: Z) (n: Z) (a: Z) (ret: Z) (i: Z) ,
  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a n l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "a" ) )) # Ptr  |-> a)
|--
  [| ((ret + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + (Znth i l 0) )) |]
.

Definition array_sum_safety_wit_4 := 
forall (l: (@list Z)) (i_2: Z) (n: Z) (a: Z) (ret: Z) (i: Z) ,
  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a n l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_sum_entail_wit_1 := 
forall (l: (@list Z)) (i: Z) (n: Z) (a: Z) ,
  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (0 = (sum ((sublist (0) (0) (l))))) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
.

Definition array_sum_entail_wit_2 := 
forall (l: (@list Z)) (i: Z) (n: Z) (a: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a n l )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n) |] 
  &&  [| ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
.

Definition array_sum_return_wit_1 := 
forall (l: (@list Z)) (i_2: Z) (n_2: Z) (a_2: Z) (ret: Z) (i: Z) ,
  [| (i >= n_2) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_2) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_2) |] 
  &&  [| (n_2 < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_2)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_2)
  **  (store_int_array a_2 n_2 l )
|--
  EX a n,
  [| (ret = (sum (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
.

Definition array_sum_partial_solve_wit_1 := 
forall (l: (@list Z)) (i: Z) (n: Z) (a: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
|--
  [| (i_2 < n) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (((a + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (store_int_array_missing_i_rec a i_2 0 n l )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
.

(*----- Function array_sum_call -----*)

Definition array_sum_call_return_wit_1 := 
forall (l: (@list Z)) (i: Z) (n_3: Z) (a_2: Z) (n_2: Z) (retval: Z) ,
  [| (retval = (sum (l))) |] 
  &&  [| (0 < n_3) |] 
  &&  [| (n_3 < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_3)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_2)
  **  (store_int_array a_2 n_2 l )
|--
  EX a n,
  [| (retval = (sum (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
.

Definition array_sum_call_partial_solve_wit_1_pure := 
forall (i: Z) (l: (@list Z)) (i_2: Z) (n: Z) (a: Z) ,
  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
|--
  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
.

Definition array_sum_call_partial_solve_wit_1_aux := 
forall (i: Z) (l: (@list Z)) (i_2: Z) (n: Z) (a: Z) ,
  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
|--
  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  (store_int_array a n l )
.

Definition array_sum_call_partial_solve_wit_1 := array_sum_call_partial_solve_wit_1_pure -> array_sum_call_partial_solve_wit_1_aux.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (l: (@list Z)) (p: Z) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_entail_wit_1 := 
forall (l: (@list Z)) (p: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l )
|--
  EX l1 l2,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll 0 l1 )
  **  (sll p l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition reverse_entail_wit_2 := 
forall (l: (@list Z)) (p: Z) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_next: Z) (v_data: Z) (l2_new: (@list Z)) ,
  [| (l2_2 = (cons (v_data) (l2_new))) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1_2))) (l2_2))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll v_next l2_new )
  **  (sll w l1_2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  EX l1 l2,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v l1 )
  **  (sll v_next l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition reverse_return_wit_1 := 
forall (l: (@list Z)) (p: Z) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v = 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  ((( &( "p" ) )) # Ptr  |->_)
  **  (sll w (rev (l)) )
.

Definition reverse_partial_solve_wit_1_pure := 
forall (l: (@list Z)) (p: Z) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  ((( &( "w" ) )) # Ptr  |-> w)
  **  (sll w l1 )
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  (sll v l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (v <> 0) |]
.

Definition reverse_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (p: Z) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (v <> 0) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v l2 )
  **  (sll w l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
.

Definition reverse_partial_solve_wit_1 := reverse_partial_solve_wit_1_pure -> reverse_partial_solve_wit_1_aux.

Definition reverse_which_implies_wit_1 := 
forall (l2: (@list Z)) (v: Z) ,
  [| (v <> 0) |]
  &&  (sll v l2 )
|--
  EX v_next v_data l2_new,
  [| (l2 = (cons (v_data) (l2_new))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> v_next)
  **  (sll v_next l2_new )
.

(*----- Function reverse_call -----*)

Definition reverse_call_return_wit_1 := 
forall (l: (@list Z)) (retval: Z) ,
  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (sll retval (rev ((rev (l)))) )
|--
  ((( &( "p" ) )) # Ptr  |->_)
  **  (sll retval l )
.

Definition reverse_call_partial_solve_wit_1 := 
forall (l: (@list Z)) (p: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l )
|--
  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l )
.

Definition reverse_call_partial_solve_wit_2 := 
forall (l: (@list Z)) (retval: Z) ,
  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (sll retval (rev (l)) )
|--
  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (sll retval (rev (l)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_add_safety_wit_1 : add_safety_wit_1.
Axiom proof_of_add_return_wit_1 : add_return_wit_1.
Axiom proof_of_add_call_safety_wit_1 : add_call_safety_wit_1.
Axiom proof_of_add_call_safety_wit_2 : add_call_safety_wit_2.
Axiom proof_of_add_call_safety_wit_3 : add_call_safety_wit_3.
Axiom proof_of_add_call_return_wit_1 : add_call_return_wit_1.
Axiom proof_of_add_call_partial_solve_wit_1_pure : add_call_partial_solve_wit_1_pure.
Axiom proof_of_add_call_partial_solve_wit_1 : add_call_partial_solve_wit_1.
Axiom proof_of_add_call_partial_solve_wit_2_pure : add_call_partial_solve_wit_2_pure.
Axiom proof_of_add_call_partial_solve_wit_2 : add_call_partial_solve_wit_2.
Axiom proof_of_add_call_partial_solve_wit_3_pure : add_call_partial_solve_wit_3_pure.
Axiom proof_of_add_call_partial_solve_wit_3 : add_call_partial_solve_wit_3.
Axiom proof_of_add_rec_safety_wit_1 : add_rec_safety_wit_1.
Axiom proof_of_add_rec_safety_wit_2 : add_rec_safety_wit_2.
Axiom proof_of_add_rec_safety_wit_3 : add_rec_safety_wit_3.
Axiom proof_of_add_rec_safety_wit_4 : add_rec_safety_wit_4.
Axiom proof_of_add_rec_safety_wit_5 : add_rec_safety_wit_5.
Axiom proof_of_add_rec_return_wit_1 : add_rec_return_wit_1.
Axiom proof_of_add_rec_return_wit_2 : add_rec_return_wit_2.
Axiom proof_of_add_rec_partial_solve_wit_1_pure : add_rec_partial_solve_wit_1_pure.
Axiom proof_of_add_rec_partial_solve_wit_1 : add_rec_partial_solve_wit_1.
Axiom proof_of_array_sum_safety_wit_1 : array_sum_safety_wit_1.
Axiom proof_of_array_sum_safety_wit_2 : array_sum_safety_wit_2.
Axiom proof_of_array_sum_safety_wit_3 : array_sum_safety_wit_3.
Axiom proof_of_array_sum_safety_wit_4 : array_sum_safety_wit_4.
Axiom proof_of_array_sum_entail_wit_1 : array_sum_entail_wit_1.
Axiom proof_of_array_sum_entail_wit_2 : array_sum_entail_wit_2.
Axiom proof_of_array_sum_return_wit_1 : array_sum_return_wit_1.
Axiom proof_of_array_sum_partial_solve_wit_1 : array_sum_partial_solve_wit_1.
Axiom proof_of_array_sum_call_return_wit_1 : array_sum_call_return_wit_1.
Axiom proof_of_array_sum_call_partial_solve_wit_1_pure : array_sum_call_partial_solve_wit_1_pure.
Axiom proof_of_array_sum_call_partial_solve_wit_1 : array_sum_call_partial_solve_wit_1.
Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_partial_solve_wit_1_pure : reverse_partial_solve_wit_1_pure.
Axiom proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Axiom proof_of_reverse_which_implies_wit_1 : reverse_which_implies_wit_1.
Axiom proof_of_reverse_call_return_wit_1 : reverse_call_return_wit_1.
Axiom proof_of_reverse_call_partial_solve_wit_1 : reverse_call_partial_solve_wit_1.
Axiom proof_of_reverse_call_partial_solve_wit_2 : reverse_call_partial_solve_wit_2.

End VC_Correct.
