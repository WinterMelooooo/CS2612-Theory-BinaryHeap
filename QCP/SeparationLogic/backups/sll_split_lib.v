Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Lia.
From SetsClass Require Import SetsClass.
From AUXLib Require Import relations Axioms. 
From StateMonad.monadnrm Require Export monadbasic safeexec_lib.


Import SetsNotation.
Local Open Scope sets.

Export MonadNotation.
Local Open Scope stmonad.

Definition maketuple (x p :list Z): ((list Z) * (list Z)) := (x, p).

#[export] Instance merge_state  : stateclass := {|
  Σ := unit
|}.

Definition splitcallX (X:  ((list Z) * (list Z)) -> unit -> Prop) : ((list Z) * (list Z)) -> unit -> Prop := 
  fun '(p,q) _ =>  X (q,p) tt.

Section splitrec_monad.

  Definition splitrec_f  (W : ((list Z) * (list Z) * (list Z)) ->  program ((list Z) * (list Z) * (list Z))) 
                          : ((list Z) * (list Z) * (list Z)) -> program ((list Z) * (list Z) * (list Z)) :=
    fun '(x, p, q) => match x with 
                      | nil => return (x, p, q)
                      | xh :: x' => W (x', q,  xh::p)
                      end.

  Definition splitrec : ((list Z) * (list Z) * (list Z)) -> program ((list Z) * (list Z) * (list Z)) := 
    BW_LFix splitrec_f.

  Definition splitrel x p q :=
    '(x, p, q) <- splitrec (x, p, q) ;; return (p, q).

  Definition reverse_splitret x p q :=
    '(p,q) <- (splitrel x p q) ;; return (q,p).

  Lemma mono_splitrec_f: mono splitrec_f.
  Proof.
    intros.
    unfold splitrec_f.
    unfold mono, order_rel, R_whileret, order_rel, R_func, order_rel, R_while_fin.
    intros f1 f2 H x s1.
    destruct x as ((x & p) & q).
    destruct x.
    reflexivity.
    apply H.
  Qed.
  
  Lemma continuous_splitrec_f: continuous splitrec_f.
  Proof.
    intros.
    unfold splitrec_f.
    unfold continuous, omega_lub, oLub_whileret, omega_lub, oLub_func, omega_lub, oLub_while_fin.
    intros l Hl.
    unfold equiv, Equiv_whileret, equiv, Equiv_func, Equiv, equiv, Equiv_while_fin.
    sets_unfold.
    intros x s x0 s0.
    destruct x as ((x & p) & q).
    split;intros.
    + destruct x. exists O. auto.
      auto.
    + destruct H as (n & H).
      destruct x;auto.
      eexists;eauto.
  Qed.



  Lemma splitrec_unfold: splitrec == splitrec_f splitrec.
  Proof.
    intros.
    symmetry.
    apply BW_LFix_is_fix.
    apply mono_splitrec_f.
    apply continuous_splitrec_f.
  Qed. 


  Lemma splitrec_eval_xnil: forall p q P, 
    P -@ (splitrec (nil, p, q)) -⥅ 
    P ♯ (nil, p, q).
  Proof.
    intros.
    erewrite (program_para_equiv (splitrec_unfold)).
    unfold splitrec_f.
    apply  highret_eval2.
  Qed.

  Lemma splitrec_eval_xnotnil: forall z x p q P x0 p0 q0,
    P -@ (splitrec (x, q, z :: p)) -⥅ P ♯ (x0, p0, q0) ->
    P -@ (splitrec (z :: x, p, q)) -⥅ P ♯ (x0, p0, q0).
  Proof.
    intros.
    erewrite (program_para_equiv (splitrec_unfold)).
    unfold splitrec_f.
    auto.
  Qed.

  Lemma splitrec_safeexec_xnotnil: forall z x p q,
    forall P X, safeExec P (splitrec ((z :: x), p, q)) X -> 
                safeExec P (splitrec (x, q, z::p)) X.
  Proof.
    intros.
    erewrite (program_para_equiv (splitrec_unfold)) in H.
    unfold splitrec_f in H.
    auto.
  Qed.

  Lemma splitrel_eval_xnotnil: forall z x p q,
    forall P X, safeExec P (splitrel (z::x) p q) X ->
                safeExec P (splitrel x q (z::p)) X.
  Proof. 
    unfold splitrel. intros.
    erewrite (program_para_equiv (splitrec_unfold)) in H.
    unfold splitrec_f in H.
    auto.
  Qed.
    



  


End splitrec_monad.









