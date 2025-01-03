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
Require Import int_array_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import int_array_lib.
Require Import sll_merge_rel_lib.
Local Open Scope stmonad.
Require Import int_array_merge_rel_lib.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof. 
  pre_process.
  Exists l0 (@nil Z) (@nil Z).
  Exists s1 s2 (@nil Z).
  entailer!.
  unfold store_int_array_rec. simpl.
  entailer!.
Qed.  

Lemma proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Proof. 
  pre_process.
  replace (k - k) with 0 in * by lia.
  replace (j - j) with 0 in * by lia.
  replace (i - i) with 0 in * by lia.
  prop_apply (store_int_array_rec_Zlength arr_pre j).
  Intros.
  destruct l2_2;[rewrite Zlength_nil in H10;lia | ].
  clear H10.
  prop_apply (store_int_array_rec_Zlength ret_pre k).
  Intros.
  destruct l6_2;[rewrite Zlength_nil in H10;lia | ].
  clear H10.
  rewrite Znth0_cons.
  replace (replace_Znth 0 z (z0 :: l6_2)) with (z :: l6_2) by easy.
  sep_apply (store_int_array_rec_cons ret_pre);[ | lia].
  sep_apply (store_int_array_rec_cons arr_pre j);[ | lia].
  sep_apply (store_int_array_rec_tail_merge arr_pre (q_pre + 1));[ | lia].
  sep_apply (store_int_array_rec_tail_merge ret_pre);[ | lia].
  prop_apply (store_int_array_rec_Zlength arr_pre i).
  Exists l6_2 (l5_2 ++ z :: nil) l4_2.
  Exists l1_2 l2_2 (l3_2 ++ z :: nil).
  entailer!.
  unfold merge_from_mid_rel in *.
  rewrite (whilebreak_unfold _ _) in H2.
  prove_by_one_abs_step (inl (l1_2, l2_2, l3_2 ++ z :: nil)).
  destruct l1_2. rewrite Zlength_nil in H14. lia.
  unfold merge_body.
  rewrite !Znth0_cons in H.
  abs_choice_right.
  abs_test_step; [ lia | ].
  abs_return_step.
Qed. 

Lemma proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Proof. 
  pre_process.
  replace (k - k) with 0 in * by lia.
  replace (j - j) with 0 in * by lia.
  replace (i - i) with 0 in * by lia.
  prop_apply (store_int_array_rec_Zlength arr_pre i).
  Intros.
  destruct l1_2;[rewrite Zlength_nil in H10;lia | ].
  clear H10.
  prop_apply (store_int_array_rec_Zlength ret_pre k).
  Intros.
  destruct l6_2;[rewrite Zlength_nil in H10;lia | ].
  clear H10.
  rewrite Znth0_cons.
  replace (replace_Znth 0 z (z0 :: l6_2)) with (z :: l6_2) by easy.
  sep_apply (store_int_array_rec_cons ret_pre);[ | lia].
  sep_apply (store_int_array_rec_cons arr_pre i);[ | lia].
  sep_apply (store_int_array_rec_tail_merge arr_pre p_pre);[ | lia].
  sep_apply (store_int_array_rec_tail_merge ret_pre);[ | lia].
  prop_apply (store_int_array_rec_Zlength arr_pre j).
  Exists l6_2 l5_2 (l4_2 ++ z :: nil).
  Exists l1_2 l2_2 (l3_2 ++ z :: nil).
  entailer!.
  unfold merge_from_mid_rel in *.
  rewrite (whilebreak_unfold _ _) in H2.
  prove_by_one_abs_step (inl (l1_2, l2_2, l3_2 ++ z :: nil)).
  destruct l2_2. rewrite Zlength_nil in H14. lia.
  unfold merge_body.
  rewrite !Znth0_cons in H.
  abs_choice_left.
  abs_test_step; [ lia | ].
  abs_return_step.
Qed. 

Lemma proof_of_merge_entail_wit_3_1 : merge_entail_wit_3_1.
Proof. 
  pre_process.
  rewrite <- derivable1_orp_intros1.
  Exists l6_3 l5_3 l4_3.
  Exists l1_3 l2_3 l3_3.
  prop_apply (store_int_array_rec_Zlength arr_pre j).
  Intros.
  assert (j > r_pre + 1 \/ j <= r_pre + 1) as [ | ] by lia. 
  pose proof Zlength_nonneg l2_3. lia.
  entailer!.
Qed.

Lemma proof_of_merge_entail_wit_3_2 : merge_entail_wit_3_2.
Proof. 
  pre_process.
  rewrite <- derivable1_orp_intros2.
  Exists l6_3 l5_3 l4_3.
  Exists l1_3 l2_3 l3_3.
  prop_apply (store_int_array_rec_Zlength arr_pre i).
  Intros.
  assert (i > q_pre + 1 \/ i <= q_pre + 1) as [ | ] by lia. 
  pose proof Zlength_nonneg l1_3. lia.
  entailer!.
Qed. 

Lemma proof_of_merge_entail_wit_5 : merge_entail_wit_5.
Proof. 
  pre_process.
  replace (k - k) with 0 in * by lia.
  replace (j - j) with 0 in * by lia.
  replace (i - i) with 0 in * by lia.
  prop_apply (store_int_array_rec_Zlength arr_pre i).
  Intros.
  destruct l1_3;[rewrite Zlength_nil in H9;lia | ].
  clear H9.
  prop_apply (store_int_array_rec_Zlength ret_pre k).
  Intros.
  destruct l6_3;[rewrite Zlength_nil in H9;lia | ].
  clear H9.
  rewrite Znth0_cons.
  replace (replace_Znth 0 z (z0 :: l6_3)) with (z :: l6_3) by easy.
  sep_apply (store_int_array_rec_cons ret_pre);[ | lia].
  sep_apply (store_int_array_rec_cons arr_pre i);[ | lia].
  sep_apply (store_int_array_rec_tail_merge arr_pre p_pre);[ | lia].
  sep_apply (store_int_array_rec_tail_merge ret_pre);[ | lia].
  prop_apply (store_int_array_rec_Zlength arr_pre j).
  rewrite <- derivable1_orp_intros1.
  Exists l6_3 l5_3 (l4_3 ++ z :: nil).
  Exists l1_3 l2_3 (l3_3 ++ z :: nil).
  entailer!.
  replace (r_pre + 1 - j) with 0 in * by lia.
  destruct l2_3. 2:{ rewrite Zlength_cons in H13. pose proof Zlength_nonneg l2_3. lia. }
  unfold merge_from_mid_rel in *.
  rewrite (whilebreak_unfold _ _) in H0.
  rewrite (whilebreak_unfold _ _).
  cbn [merge_body] in *.
  destruct l1_3.
  rewrite <- app_assoc. easy.
  rewrite <- app_assoc. easy.
Qed. 

Lemma proof_of_merge_entail_wit_6_1 : merge_entail_wit_6_1.
Proof. 
  pre_process.
  prop_apply (store_int_array_rec_Zlength arr_pre i).
  Intros.
  destruct l1. 2:{ rewrite Zlength_cons in H9. pose proof Zlength_nonneg l1. lia. }
  Exists l6_2 l5_2 l4_2.
  Exists l2_2 l3_2.
  unfold store_int_array_rec at 1. simpl. 
  entailer!.
Qed. 

Lemma proof_of_merge_entail_wit_6_2 : merge_entail_wit_6_2.
Proof. 
  pre_process.
  prop_apply (store_int_array_rec_Zlength arr_pre i).
  Intros.
  destruct l1. 2:{ rewrite Zlength_cons in H9. pose proof Zlength_nonneg l1. lia. }
  Exists l6_2 l5_2 l4_2.
  Exists l2_2 l3_2.
  unfold store_int_array_rec at 1. simpl. 
  entailer!.
Qed.

Lemma proof_of_merge_entail_wit_7 : merge_entail_wit_7.
Proof. 
  pre_process.
  replace (k - k) with 0 in * by lia.
  replace (j - j) with 0 in * by lia.
  replace (i - i) with 0 in * by lia.
  prop_apply (store_int_array_rec_Zlength arr_pre j).
  Intros.
  destruct l2_2;[rewrite Zlength_nil in H9;lia | ].
  clear H9.
  prop_apply (store_int_array_rec_Zlength ret_pre k).
  Intros.
  destruct l6_2;[rewrite Zlength_nil in H9;lia | ].
  clear H9.
  rewrite Znth0_cons.
  replace (replace_Znth 0 z (z0 :: l6_2)) with (z :: l6_2) by easy.
  sep_apply (store_int_array_rec_cons ret_pre);[ | lia].
  sep_apply (store_int_array_rec_cons arr_pre j);[ | lia].
  sep_apply (store_int_array_rec_tail_merge arr_pre (q_pre + 1));[ | lia].
  sep_apply (store_int_array_rec_tail_merge ret_pre);[ | lia].
  Exists l6_2 (l5_2 ++ z :: nil) l4_2.
  Exists l2_2 (l3_2 ++ z :: nil).
  entailer!.
  unfold merge_from_mid_rel in *.
  rewrite (whilebreak_unfold _ _) in H0.
  rewrite (whilebreak_unfold _ _).
  cbn [merge_body] in *.
  rewrite <- app_assoc. easy.
Qed. 

Lemma proof_of_merge_return_wit_1 : merge_return_wit_1.
Proof. 
  pre_process.
  subst i.
  prop_apply (store_int_array_rec_Zlength arr_pre j).
  Intros.
  destruct l2. 2:{ rewrite Zlength_cons in H8. pose proof Zlength_nonneg l2. lia. }
  rewrite Zlength_nil in H8. 
  replace j with (r_pre + 1) in * by lia.
  replace k with (r_pre + 1) in * by lia.
  prop_apply (store_int_array_rec_Zlength ret_pre (r_pre + 1)).
  Intros.
  destruct l6.
  2: { rewrite Zlength_cons in H9. pose proof Zlength_nonneg l6. lia.  }
  unfold store_int_array_rec at 1 2. simpl.
  sep_apply store_int_array_rec_divide_rev;[ | auto].
  Exists (l4 ++ l5) l3.
  entailer!.
  unfold merge_from_mid_rel in H0.
  rewrite (whilebreak_unfold _ _) in H0.
  rewrite <- (app_nil_r l3).
  prove_by_one_abs_step (inr (l3 ++ nil)).
  abs_return_step.
Qed.

Lemma proof_of_mergeSort_safety_wit_1 : mergeSort_safety_wit_1.
Proof. 
  pre_process.
  assert (0 <= (r_pre - l_pre) ÷ 2 < r_pre - l_pre ).
  { split.
    apply Z.quot_pos; lia.
    apply Z.quot_lt;lia. }
  entailer!.
Qed. 

Lemma proof_of_mergeSort_entail_wit_1 : mergeSort_entail_wit_1.
Proof. 
  pre_process.
  assert (0 <= (r_pre - l_pre) ÷ 2 < r_pre - l_pre ).
  { split.
    apply Z.quot_pos; lia.
    apply Z.quot_lt;lia. }
  prop_apply store_int_array_rec_Zlength.
  Intros.
  rewrite store_int_array_rec_divide with (m :=  (l_pre + (r_pre - l_pre) ÷ 2 + 1)) by lia.
  rewrite store_int_array_rec_divide with (x:= ret_pre) (m :=  (l_pre + (r_pre - l_pre) ÷ 2 + 1)) by lia.
  Exists (sublist 0 (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) s1) (sublist (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) (r_pre + 1 - l_pre) s1).
  entailer!.
  replace ((l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre)) with ((r_pre - l_pre) ÷ 2 + 1) by lia.
  assert (Zlength  (sublist ((r_pre - l_pre) ÷ 2 + 1) (r_pre + 1 - l_pre) s1) = (r_pre - l_pre) - ((r_pre - l_pre) ÷ 2)).
  { rewrite Zlength_sublist by lia.
    lia. }
  destruct (sublist ((r_pre - l_pre) ÷ 2 + 1) (r_pre + 1 - l_pre) s1) eqn:?. 
  rewrite Zlength_nil in H6. lia.
  unfold mergesortrec_loc1.
  rewrite (gmergesortrec_unfold s1) in H0.
  unfold gmergesortrec_f in H0.
  safe_choice_r H0.
  prove_by_one_abs_step ((sublist 0 ((r_pre - l_pre) ÷ 2 + 1) s1), (z::l)).
  apply hseval_stateless_ret.
  unfold ext_split.
  rewrite <- Heql.
  rewrite <- sublist_split.
  rewrite sublist_self by easy.
  auto.
  lia.
  rewrite <- Zlength_correct.
  lia.
  lia.
Qed. 

Lemma proof_of_mergeSort_entail_wit_2 : mergeSort_entail_wit_2.
Proof. 
  pre_process.
  Exists l2_2 l2_3 l1_2.
  entailer!.
Qed. 

Lemma proof_of_mergeSort_entail_wit_3 : mergeSort_entail_wit_3.
Proof. 
  pre_process.
  Exists (l3 ++ l2) l1_2 l1.
  entailer!.
  prop_apply (store_int_array_rec_Zlength ret_pre (m + 1)).
  prop_apply (store_int_array_rec_Zlength ret_pre l_pre).
  Intros.
  rewrite (store_int_array_rec_divide ret_pre l_pre (r_pre + 1) (l3 ++ l2) (m + 1)); try lia.
  replace ((m + 1 - l_pre)) with (Zlength l3)  by lia.
  rewrite sublist_app_exact1.
  rewrite sublist_split_app_r with (len := (Zlength l3)) by lia.
  replace ((Zlength l3 - Zlength l3)) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_app.
  lia.
Qed.

Lemma proof_of_mergeSort_return_wit_1_1 : mergeSort_return_wit_1_1.
Proof. 
  pre_process.
  prop_apply (store_int_array_rec_Zlength arr_pre l_pre).
  Intros.
  replace (r_pre + 1 - l_pre) with 1 in * by lia.
  Exists s1 s1.
  entailer!.
  destruct s1. rewrite Zlength_nil in H4. lia.
  destruct s1. 2:{ rewrite !Zlength_cons in H4. pose proof Zlength_nonneg s1. lia.  }
  rewrite (gmergesortrec_unfold _) in H0.
  unfold gmergesortrec_f in H0.
  safe_choice_l H0.
  eapply highstependret_derive with (P':= (fun _ => ATrue));eauto.
  apply hseval_stateless_ret.
  unfold ext_sort.
  easy.
Qed.


Lemma proof_of_mergeSort_derive_low_level_spec_aux_by_low_level_spec : mergeSort_derive_low_level_spec_aux_by_low_level_spec.
Proof. 
  pre_process.
  Exists l0.
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists X'.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros s3 s2.
  Exists s3 s2.
  unfold applyf.
  entailer!.
  apply (H3 (fun _ => ATrue)).
  tauto.
Qed. 

