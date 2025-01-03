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
From SimpleC.EE Require Import eval_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import int_array_lib.
Require Import eval_lib.
Local Open Scope sac.

(* Locally use Z.eqb_eq *)
Local Hint Resolve Z.eqb_eq : core.

Lemma proof_of_eval_entail_wit_1 : eval_entail_wit_1.
Proof.
  pre_process.
  exfalso. 
  destruct op ; simpl in * ; lia.
Qed.

Lemma proof_of_eval_entail_wit_2 : eval_entail_wit_2.
Proof.
  pre_process.
  destruct e0 ; simpl in * ; Intros.
  - lia. 
  - lia.
  - Intros x. lia.
  - Intros x p2. lia. 
Qed.

Lemma proof_of_eval_return_wit_1 : eval_return_wit_1.
Proof.
  pre_process.
  subst.
  simpl.
  entailer!.
Qed.

Lemma proof_of_eval_return_wit_2 : eval_return_wit_2.
Proof.
  pre_process.
  subst.
  simpl.
  entailer!.
Qed.

Lemma proof_of_eval_return_wit_3 : eval_return_wit_3.
Proof.
  pre_process.
  subst.
  rewrite H5.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  get_bin_op_from_id op.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn : I1; 
    [ | destruct ((expr_eval e2 l =? 0)%Z) eqn : I2]; 
      auto; [ destruct H1 | destruct H]; apply Z.eqb_eq; auto.
Qed. 

Lemma proof_of_eval_return_wit_4 : eval_return_wit_4.
Proof.
  pre_process.
  subst.
  rewrite H5.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  get_bin_op_from_id op.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn : I1; 
      [ | destruct ((expr_eval e2 l =? 0)%Z) eqn : I2]; auto.
  destruct H0.
  rewrite Z.eqb_neq in I2.
  contradiction.
Qed.

Lemma proof_of_eval_return_wit_5 : eval_return_wit_5.
  pre_process.
  subst.
  rewrite H3.
  simpl store_expr.
  Exists v_2 v.  
  entailer!.
  get_bin_op_from_id op.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn : I1; 
    [ | destruct ((expr_eval e2 l =? 0)%Z) eqn : I2]; auto.
  destruct H0.
  rewrite Z.eqb_neq in I1.
  contradiction.
Qed. 

Lemma proof_of_eval_return_wit_6 : eval_return_wit_6.
Proof.
  pre_process.
  subst.
  rewrite H4.
  simpl store_expr.
  Exists v_2 v.  
  entailer!.
  get_bin_op_from_id op.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn : I1; auto.
  destruct ((expr_eval e2 l =? 0)%Z) eqn : I2; auto.
  destruct H.
  rewrite Z.eqb_eq in I1.
  exact I1.
Qed.

Lemma proof_of_eval_return_wit_7 : eval_return_wit_7.
Proof.
  pre_process.
  subst.
  rewrite H6.
  simpl store_expr.
  Exists v_2 v.  
  entailer!.
  get_bin_op_from_id op.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn : I1; auto.
  destruct ((expr_eval e2 l =? 0)%Z) eqn : I2; auto.
  destruct H.
  rewrite Z.eqb_eq in I2.
  exact I2.
Qed.

Lemma proof_of_eval_return_wit_8 : eval_return_wit_8.
Proof. 
  pre_process.
  subst.
  rewrite H6.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  get_bin_op_from_id op.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn : I1; auto.
  - destruct ((expr_eval e2 l =? 0)%Z) eqn : I2; auto.
    destruct H0.
    rewrite Z.eqb_neq in I2.
    contradiction.
  - destruct H0.
    rewrite Z.eqb_neq in I1.
    rewrite <- H2 in I1.
    contradiction.
Qed.

Lemma proof_of_eval_return_wit_9 : eval_return_wit_9.
Proof.
  pre_process.
  subst.
  rewrite H5.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
Qed.

Lemma proof_of_eval_return_wit_10 : eval_return_wit_10.
Proof.
  pre_process.
  subst.
  rewrite H6.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
Qed.

Lemma proof_of_eval_return_wit_11 : eval_return_wit_11.
Proof.
  pre_process.
  subst.
  rewrite H7.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
Qed. 

Lemma proof_of_eval_return_wit_12 : eval_return_wit_12.
Proof.
  pre_process.
  subst.
  rewrite H8.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
Qed.

Lemma proof_of_eval_return_wit_13 : eval_return_wit_13.
Proof.
  pre_process.
  subst.
  rewrite H9.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
Qed.

Lemma proof_of_eval_return_wit_14_1 : eval_return_wit_14_1.
Proof.
  pre_process.
  subst.
  rewrite H11.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l <? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.ltb_lt in I.
  lia.
Qed.

Lemma proof_of_eval_return_wit_14_2 : eval_return_wit_14_2.
Proof.
  pre_process.
  subst.
  rewrite H11.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l <? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.ltb_nlt in I.
  lia.
Qed.

Lemma proof_of_eval_return_wit_15_1 : eval_return_wit_15_1.
Proof.
  pre_process.
  subst.
  rewrite H12.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l >? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.gtb_lt in I.
  lia.
Qed. 

Lemma proof_of_eval_return_wit_15_2 : eval_return_wit_15_2.
Proof.
  pre_process.
  subst.
  rewrite H12.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l >? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.gtb_ltb in I.
  rewrite Z.ltb_nlt in I.
  lia.
Qed. 

Lemma proof_of_eval_return_wit_16_1 : eval_return_wit_16_1.
Proof.
  pre_process.
  subst.
  rewrite H13.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l <=? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.leb_le in I.
  lia.
Qed.

Lemma proof_of_eval_return_wit_16_2 : eval_return_wit_16_2.
Proof.
  pre_process.
  subst.
  rewrite H13.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l <=? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.leb_gt in I.
  lia.
Qed. 

Lemma proof_of_eval_return_wit_17_1 : eval_return_wit_17_1.
Proof.
  pre_process.
  subst.
  rewrite H14.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l >=? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.geb_le in I.
  lia.
Qed.

Lemma proof_of_eval_return_wit_17_2 : eval_return_wit_17_2.
Proof. 
  pre_process.
  subst.
  rewrite H14.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l >=? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.geb_leb in I.
  rewrite Z.leb_gt in I.
  lia.
Qed.

Lemma proof_of_eval_return_wit_18_1 : eval_return_wit_18_1.
Proof.
  pre_process.
  subst.
  rewrite H15.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l =? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.eqb_eq in I.
  lia.
Qed.

Lemma proof_of_eval_return_wit_18_2 : eval_return_wit_18_2.
Proof. 
  pre_process.
  subst.
  rewrite H15.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l =? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.eqb_neq in I.
  lia.
Qed.

Lemma proof_of_eval_return_wit_19_1 : eval_return_wit_19_1.
Proof.
  pre_process.
  subst.
  rewrite H16.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l =? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.eqb_neq in I.
  lia.
Qed.

Lemma proof_of_eval_return_wit_19_2 : eval_return_wit_19_2.
Proof.
  pre_process.
  subst.
  rewrite H16.
  get_bin_op_from_id op.
  simpl store_expr.
  Exists v_2 v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l =? expr_eval e2 l)%Z) eqn: I; auto.
  rewrite Z.eqb_eq in I.
  lia.
Qed. 

Lemma proof_of_eval_return_wit_20_1 : eval_return_wit_20_1.
Proof.
  pre_process.
  subst.
  rewrite H3.
  get_un_op_from_id op.
  simpl store_expr.
  Exists v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn: I; auto.
  rewrite Z.eqb_eq in I.
  lia.
Qed. 

Lemma proof_of_eval_return_wit_20_2 : eval_return_wit_20_2.
Proof.
  pre_process.
  subst.
  rewrite H3.
  get_un_op_from_id op.
  simpl store_expr.
  Exists v.
  entailer!.
  simpl.
  destruct ((expr_eval e1 l =? 0)%Z) eqn: I; auto.
  rewrite Z.eqb_neq in I.
  lia.
Qed. 

Lemma proof_of_eval_return_wit_21 : eval_return_wit_21.
Proof.
  pre_process.
  subst.
  destruct op.
  1: { simpl in H0. contradiction. } 
  simpl store_expr.
  Exists v.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_6_pure : eval_partial_solve_wit_6_pure.
Proof.
  pre_process.
  subst.
  rewrite H2.
  get_bin_op_from_id op.
  inversion H6; subst.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_7_pure : eval_partial_solve_wit_7_pure.
Proof.
  pre_process.
  subst.
  rewrite H3.
  get_bin_op_from_id op.
  inversion H7; subst.
  entailer!.
Qed. 

Lemma proof_of_eval_partial_solve_wit_8_pure : eval_partial_solve_wit_8_pure.
Proof.
  pre_process.
  subst.
  rewrite H3.
  get_bin_op_from_id op.
  inversion H7; subst.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_9_pure : eval_partial_solve_wit_9_pure.
Proof.
  pre_process.
  subst.
  rewrite H4.
  get_bin_op_from_id op.
  inversion H8; subst.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_10_pure : eval_partial_solve_wit_10_pure.
Proof.
  pre_process.
  subst.
  inversion H7.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_11_pure : eval_partial_solve_wit_11_pure.
Proof.
  pre_process.
  subst.
  inversion H7.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_13_pure : eval_partial_solve_wit_13_pure.
Proof.
  pre_process.
  subst.
  inversion H7.
  entailer!.
Qed.

Lemma proof_of_eval_partial_solve_wit_14_pure : eval_partial_solve_wit_14_pure.
Proof.
  pre_process.
  subst.
  inversion H7.
  entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_1 : eval_which_implies_wit_1.
Proof.
  pre_process.
  destruct e0.
  + Exists 0.
    unfold store_expr, store_expr_aux.
    entailer!.
  + Exists 1.
    unfold store_expr, store_expr_aux.
    entailer!.
  + Exists 3.
    simpl.
    Intros p.
    Exists p.
    entailer!.
  + Exists 2.
    simpl.
    Intros p1 p2.
    Exists p1 p2.
    entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_2 : eval_which_implies_wit_2.
Proof.
  pre_process.
  subst e_t.
  unfold store_expr_aux.
  destruct e0.
  4: { Intros p1 p2. discriminate. }
  3: { Intros p1. discriminate. }
  2: { Intros. discriminate. }
  Exists z.
  entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_3 : eval_which_implies_wit_3.
Proof.
  pre_process.
  prop_apply store_int_array_length.
  subst e_t.
  unfold store_expr_aux.
  destruct e0.
  4: { Intros p1 p2. discriminate. }
  3: { Intros p1. discriminate. }
  1: { Intros. discriminate. }
  Exists z.
  inversion H0.
  entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_4 : eval_which_implies_wit_4.
Proof. 
  pre_process.
  subst e_t.
  unfold store_expr_aux.
  destruct e0.
  { Intros. discriminate. }
  { Intros. discriminate. }
  { Intros p. discriminate. }
  Intros p1 p2.
  Exists p2 p1 (BinOpID b) b.
  Exists e0_1 e0_2.
  entailer!.
Qed.

Lemma proof_of_eval_which_implies_wit_5 : eval_which_implies_wit_5.
Proof.
  pre_process.
  subst e_t.
  unfold store_expr_aux.
  destruct e0.
  { Intros. discriminate. }
  { Intros. discriminate. }
  2: { Intros p1 p2. discriminate. }
  Intros p.
  Exists p (UnOpID u) u.
  Exists e0.
  entailer!.
Qed. 

Lemma proof_of_eval_safety_wit_13 : eval_safety_wit_13.
Proof.
  pre_process.
  subst.
  get_bin_op_from_id op.
  inversion H9; subst.
  unfold bin_safe_cond in H11.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_15 : eval_safety_wit_15.
Proof.
  pre_process.
  subst.
  get_bin_op_from_id op.
  inversion H10; subst.
  unfold bin_safe_cond in H12.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_17 : eval_safety_wit_17.
Proof.
  pre_process.
  subst.
  get_bin_op_from_id op.
  inversion H11; subst.
  unfold bin_safe_cond in H13.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_19 : eval_safety_wit_19.
Proof.
  pre_process.
  subst.
  get_bin_op_from_id op.
  inversion H12; subst.
  unfold bin_safe_cond in H14.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_21 : eval_safety_wit_21.
Proof.
  pre_process.
  subst.
  get_bin_op_from_id op.
  inversion H13; subst.
  unfold bin_safe_cond in H15.
  entailer!.
Qed.

Lemma proof_of_eval_safety_wit_30 : eval_safety_wit_30.
Proof.
  pre_process.
  subst.
  destruct op.
  1: { unfold UnOpID in H0. contradiction. }
  inversion H7; subst.
  unfold un_safe_cond in H8.
  entailer!.
Qed.