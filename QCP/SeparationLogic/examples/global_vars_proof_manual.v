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
Require Import global_vars_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import int_array_lib.
Import naive_C_Rules.
Require Import sll_lib.
Local Open Scope sac.

Lemma proof_of_array_sum_entail_wit_1 : array_sum_entail_wit_1.
Proof.
   pre_process.
Qed.

Lemma proof_of_array_sum_entail_wit_2 : array_sum_entail_wit_2.
Proof.
   pre_process.
   prop_apply store_int_array_length.
   entailer!. subst ret.
   rewrite (sublist_split 0 (i_2 + 1) i_2)  ; try lia.
   rewrite sum_app.
   rewrite (sublist_single _ _ 0) ; try lia.
   simpl.
   lia.
Qed.

Lemma proof_of_array_sum_return_wit_1 : array_sum_return_wit_1.
Proof.
   pre_process.
   Exists a_2 n_2.
   prop_apply store_int_array_length.
   entailer!.
   replace i with n_2 in * by lia.
   subst n_2 ret.
   unfold sublist.
   simpl. rewrite firstn_all2 ; lia.
Qed.

Lemma proof_of_array_sum_safety_wit_3 : array_sum_safety_wit_3.
Proof.
   pre_process.
   prop_apply store_int_array_length.
   Intros.
   destruct (Z.eq_dec i 0).
   + subst i. simpl in *. subst ret.
     specialize (H5 0). 
     entailer!.  
   + assert (0 <= ret < i * 100).
     {  
       subst ret.
       assert (i = Z.of_nat (List.length (sublist 0 i l))).
       { rewrite sublist_length ; lia. }
       rewrite H2 at 3.
       apply sum_bound_lt.
       - intro. rewrite H7 in H2. simpl in *; lia.
       - intros. rewrite <- H2 in H7.
         rewrite Znth_sublist_lt ; try lia.
         apply H5. lia.
     }
     assert (0 <= Znth i l 0 < 100).
     { apply H5. lia. }
     entailer!.
Qed.

Lemma proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Proof.
   pre_process.
   Exists nil l.
   simpl sll.
   entailer!.   
Qed.

Lemma proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Proof.
   pre_process.
   Exists (v_data :: l1_2) l2_new.
   entailer!.
   + simpl sll.
   Exists w.
   entailer!.
   + subst l2_2.
   simpl.
   rewrite <- app_assoc.
   simpl.
   apply H1.
Qed.

Lemma proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Proof.
   pre_process.
   sep_apply (sll_zero v l2); [ | tauto].
   entailer!.
   subst l2.
   rewrite app_nil_r in H0.
   subst l.
   rewrite rev_involutive.
   entailer!.
   apply store_ptr_undef_store_ptr.
Qed.

Lemma proof_of_reverse_call_return_wit_1 : reverse_call_return_wit_1.
Proof.
   pre_process.
   rewrite rev_involutive.
   entailer!.
   apply store_ptr_undef_store_ptr.
Qed.