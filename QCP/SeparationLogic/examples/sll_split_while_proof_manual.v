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
From SimpleC.EE Require Import sll_split_while_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import sll_merge_rel_lib.
Local Open Scope stmonad.
Local Open Scope sac.

Lemma proof_of_split_while_entail_wit_2_1 : split_while_entail_wit_2_1.
Proof. 
  pre_process.
  Exists x_next_2 x l1_new_2 (x_data :: l1_2) (x_data_2 :: l2_2).
  entailer!.
  apply store_ptr_undef_store_ptr.
Qed.

Lemma proof_of_split_while_entail_wit_2_2 : split_while_entail_wit_2_2.
Proof. 
  pre_process.
  sepcon_lift  (sll x_next l1_new ).
  subst x_next.
  sep_apply sll_zero;[ | auto ].
  Intros.
  subst.
  Exists q_v_2 x nil (x_data :: l1_2) l2_2.
  simpl (sll 0 nil).
  entailer!.
  apply store_ptr_undef_store_ptr.
  unfold split_rec_rel in *.
  rewrite (program_para_equiv (split_rec_rel_unfold)) in *.
  unfold split_rec_rel_f in *.
  pose proof (program_para_equiv (bind_ID_left reversepair)) (l2_2, x_data :: l1_2).
  rewrite H1 in H0.
  exact H0.
Qed.

Lemma proof_of_split_while_partial_solve_wit_2_pure : split_while_partial_solve_wit_2_pure.
Proof. 
  pre_process.
  subst; entailer!.
Qed. 

Lemma proof_of_split_while_partial_solve_wit_4_pure : split_while_partial_solve_wit_4_pure.
Proof. 
  pre_process.
  subst; entailer!.
Qed. 

Lemma proof_of_split_while_return_wit_1 : split_while_return_wit_1.
Proof.
  pre_process.
  Exists q_v p_v l1 l2.
  sep_apply sll_zero;[ | auto ].
  entailer!.
  subst.
  unfold split_rec_rel in H0.
  unfold maketuple.
  eapply highstependret_derive with (P':= fun _ => ATrue);eauto.
  apply split_rec_rel_eval_xnil.
Qed. 

Lemma proof_of_split_while_which_implies_wit_2 : split_while_which_implies_wit_2.
Proof. 
  pre_process.
  entailer!.
  sep_apply sllseg_len1;[ | auto ].
  sep_apply sllseg_sll.
  simpl ( (_ :: _) ++ _).
  reflexivity.
  subst.
  eapply  split_rel_eval_xnotnil;eauto.
Qed.

Lemma proof_of_split_while_which_implies_wit_4 : split_while_which_implies_wit_4.
Proof. 
  pre_process.
  entailer!.
  sep_apply sllseg_len1;[ | auto ].
  sep_apply sllseg_sll.
  simpl ( (_ :: _) ++ _).
  reflexivity.
  subst l.
  unfold split_rec_rel in H.
  rewrite (program_para_equiv (split_rec_rel_unfold)) in H.
  unfold split_rec_rel_f in H. 
  rewrite bind_mcompose in H.
  rewrite bind_2_reversepair_equiv_Id in H.
  rewrite bind_ID_right in H.
  exact H.
Qed. 

