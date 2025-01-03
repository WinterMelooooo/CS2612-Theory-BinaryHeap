Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From StateMonad.monaderror Require Import monadEbasic monadEwhile monadesafe_lib.


Import SetsNotation.
Local Open Scope sets.

Import MonadwitherrDeno.
Export MonadNotation.
Local Open Scope stmonad.

Local Open Scope order_scope.
Local Open Scope Z_scope.

Definition Hoare {Σ A: Type}
(P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop): Prop :=
  ((forall (a: A)(σ1 σ2: Σ), 
    P σ1 -> c.(nrm) σ1 a σ2 -> Q a σ2)
  /\ (forall (σ1: Σ), P σ1 -> c.(err) σ1 -> False)).

Lemma Hoare_assert {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Prop),
    Q ->
    Hoare P (assert Q) (fun _ => P).
Proof.
  intros.
  unfold Hoare, assert; simpl; split; intros.
  + destruct H1; subst; tauto.
  + tauto.
Qed. 

Lemma Hoare_implies {A Σ: Type}:
  forall (P P': Σ -> Prop) (P0: Prop)
         (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> P0 /\ P' σ) ->
    (P0 -> Hoare P' c Q) ->
    Hoare P c Q.
Proof.
  unfold Hoare; intros.
  split; intros.
  + specialize (H _ H1).
    destruct (H0 ltac:(tauto)); clear H0.
    eapply H3; eauto.
    tauto.
  + specialize (H _ H1).
    destruct (H0 ltac:(tauto)); clear H0.
    eapply H4; eauto.
    tauto.
Qed.

Lemma Hoare_unit_pre {A: Type} :
  forall (P: Prop) (c: program unit A) (Q: A -> unit -> Prop),
    (P -> Hoare (fun _ => True) c Q) ->
    Hoare (fun _ => P) c Q.
Proof.
  intros.
  eapply Hoare_implies; eauto.
  intros; tauto.
Qed.

Lemma Hoare_pre {B Σ: Type} : 
  forall (P P': Σ -> Prop) (c: program Σ B) (Q: B -> Σ -> Prop),
    (forall σ, P' σ -> P σ) ->
    Hoare P c Q ->
    Hoare P' c Q.
Proof.
  unfold Hoare; intros.
  destruct H0; split.
  + intros.
    eapply H0; eauto.
  + intros.
    eapply H1; eauto.
Qed.

Lemma Hoare_post {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q Q': A -> Σ -> Prop),
    (forall a σ, Q a σ -> Q' a σ) ->
    Hoare P c Q ->
    Hoare P c Q'.
Proof.
  unfold Hoare; intros.
  split; try tauto.
  intros. destruct H0 as [H0 _].
  specialize (H0 a σ1 σ2).
  specialize (H a σ2). tauto.
Qed.

Lemma Hoare_choice {A Σ: Type}:
  forall (P: Σ -> Prop) (c1 c2: program Σ A) (Q: A -> Σ -> Prop),
    Hoare P c1 Q -> Hoare P c2 Q -> Hoare P (choice c1 c2) Q.
Proof.
  unfold Hoare; intros.
  destruct H as [H1 H2]; destruct H0 as [H3 H4].
  split; intros; unfold choice in H0; simpl in H0.
  - specialize (H1 a σ1); specialize (H3 a σ1).
    destruct H0; [apply H1 | apply H3]; auto.
  - specialize (H2 σ1); specialize (H4 σ1).
    destruct H0; [apply H2 | apply H4]; auto.
Qed.

Lemma Hoare_test {A Σ: Type}:
  forall (P1: Σ -> Prop) (P2: Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (P2 -> Hoare P1 c Q) -> Hoare P1 (test P2;; c) Q.
Proof.
  split; intros; unfold test in H1; simpl in H1.
  - unfold nrm_nrm in H1. destruct H1 as [_ [? [[Hs HP] H1]]].
    subst σ1. specialize (H HP). destruct H as [H _].
    specialize (H a x σ2). tauto.
  - destruct H1; [tauto |].
    unfold nrm_err in H1. destruct H1 as [_ [s [[? ?] ?]]].
    subst σ1. specialize (H H2). destruct H as [_ H].
    specialize (H s). tauto.
Qed.

Lemma Hoare_assert_bind {A Σ: Type}:
  forall (P: Σ -> Prop) (P': Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> P') ->
    (P' -> Hoare P c Q) -> 
    Hoare P (assert P';; c) Q.
Proof.
  unfold Hoare; intros.
  split; intros; unfold assert in H2; simpl in H2.
  - unfold nrm_nrm in H2. destruct H2 as [_ [s [[Hs HP] Hn]]].
    subst σ1. specialize (H0 HP). destruct H0 as [H0 _].
    specialize (H0 a s σ2). tauto.
  - pose proof (H σ1) H1. 
    destruct H2; [tauto |].
    unfold nrm_err in H2. destruct H2 as [_ [s [[? ?] ?]]].
    subst σ1. specialize (H0 H3). destruct H0 as [_ H0].
    specialize (H0 s). tauto.  
Qed.

Lemma Hoare_return {A Σ: Type}:
  forall (P: Σ -> Prop) (a: A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> Q a σ) ->
    Hoare P (return a) Q.
Proof.
  intros; unfold Hoare; simpl; split; intros; try tauto.
  destruct H1; subst. unfold ret.
  specialize (H σ1); tauto.
Qed.

Definition inl_case {A B Σ: Type} (ab: A + B): (program Σ A) := 
  {|
    nrm := fun s1 r s2 => match ab with
                          | inl a => s1 = s2 /\ r = a
                          | inr _ => False
                          end;
    err := ∅;
  |}.

Definition inr_case {A B Σ: Type} (ab: A + B): (program Σ B) := 
  {|
    nrm := fun s1 r s2 => match ab with
                          | inl _ => False
                          | inr b => s1 = s2 /\ r = b
                          end;
    err := ∅;
  |}.

Lemma Hoare_sum {A B Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ (A + B)) (Q: A -> Σ -> Prop) (R: B -> Σ -> Prop),
    Hoare P (x <- c;; inl_case x) Q ->
    Hoare P (x <- c;; inr_case x) R ->
    Hoare P c (fun x σ => match x with
                          | inl a => Q a σ
                          | inr b => R b σ
                          end).
Proof.
  intros.
  unfold Hoare in *.
  split; intros.
  2:{ 
    destruct H as [_ H], H0 as [_ H0].
    specialize (H σ1 H1).
    unfold bind in H.
    simpl in H.
    sets_unfold in H.
    tauto.
  }
  destruct H as [H _], H0 as [H0 _].
  destruct a.
  - specialize (H a σ1 σ2 H1).
    apply H; clear H.
    unfold bind; simpl.
    unfold nrm_nrm.
    exists (inl a); exists σ2.
    simpl; tauto.
  - specialize (H0 b σ1 σ2 H1).
    apply H0; clear H0.
    unfold bind; simpl.
    unfold nrm_nrm.
    exists (inr b); exists σ2.
    simpl; tauto.
Qed.

Lemma Hoare_inl_inr {A B Σ: Type}:
  forall (P: Σ -> Prop) (b: B) (Q: A -> Σ -> Prop),
    Hoare P (inl_case(inr b)) Q.
Proof.
  intros; unfold inl_case.
  unfold Hoare; simpl; split; intros; tauto.
Qed.

Lemma Hoare_inr_inl {A B Σ: Type}:
  forall (P: Σ -> Prop) (a: A) (Q: B -> Σ -> Prop),
    Hoare P (inr_case(inl a)) Q.
Proof.
  intros; unfold inr_case.
  unfold Hoare; simpl; split; intros; tauto.
Qed.

Lemma Hoare_inl_inl {A B Σ: Type}:
  forall (P: Σ -> Prop) (a: A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> Q a σ) ->
    Hoare P ((@inl_case A B Σ) (inl a)) Q.
Proof.
  intros; unfold inl_case.
  unfold Hoare; simpl; split; intros; try tauto.
  destruct H1; subst.
  apply H; auto.
Qed.

Lemma Hoare_inr_inr {A B Σ: Type}:
  forall (P: Σ -> Prop) (b: B) (Q: B -> Σ -> Prop),
    (forall σ, P σ -> Q b σ) ->
    Hoare P ((@inr_case A B Σ) (inr b)) Q.
Proof.
  intros; unfold inr_case.
  unfold Hoare; simpl; split; intros; try tauto.
  destruct H1; subst.
  apply H; auto.
Qed.

Lemma Hoare_conj {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop) (R: A -> Σ -> Prop),
    Hoare P c Q ->
    Hoare P c R ->
    Hoare P c (fun a σ => Q a σ /\ R a σ).
Proof.
  intros.
  unfold Hoare in *.
  split; try tauto.
  intros.
  destruct H as [H _], H0 as [H0 _].
  specialize (H a σ1 σ2).
  specialize (H0 a σ1 σ2).
  tauto.
Qed.

Lemma whilebreak_ind {Σ A B: Type}:
forall (f: A -> program Σ (A + B)) (P: A -> Σ -> Prop) (Q: B -> Σ -> Prop),
  (forall a, Hoare (P a) (f a) (fun ab σ =>
  match ab with
  | inl a => P a σ
  | inr b => Q b σ
  end)) -> (forall a, Hoare (P a) (whilebreak f a) Q).
Proof.
unfold Hoare.
intros.
unfold whilebreak.
pose proof fun a => proj2 (H a).
pose proof fun a => proj1 (H a).
clear H; rename H1 into H.
split; intros.
+ destruct H2 as [n ?].
  revert a σ1 H1 H2. induction n; simpl; intros.
  1: { hnf in H2. tauto. }
  unfold whilebreak_f in H2 at 1.
  unfold bind in H2.
  destruct H2 as [ab [σ12 [? ?]]].
  destruct ab as [a12 | b0].
  - revert H3; apply IHn.
    revert H2; apply H.
    tauto.
  - hnf in H3.
    unfold ret in H3.
    destruct H3; subst b0 σ12.
    revert H2; apply H.
    tauto.
+ simpl in H2.
  destruct H2 as [n ?].
  revert a σ1 H1 H2; induction n; simpl.
  - tauto.
  - unfold nrm_err.
    sets_unfold.
    intros.
    destruct H2.
    * apply (H0 a σ1 H1); tauto.
    * destruct H2 as [? [?  ] ].
      destruct x in H2.
      ** destruct H2.
         pose proof H a (inl a0) σ1 x0 H1 H2.
         simpl in H4.
         apply (IHn a0 x0 H4 H3).
      ** destruct H2.
         hnf in H3.
         tauto.
Qed.

Lemma BW_fix_ind {Σ A B: Type}:
  forall (f: (A -> program Σ B) -> (A -> program Σ B))
         (P: A -> Σ -> Prop) (Q: A -> B -> Σ -> Prop),
    (forall W: A -> program Σ B,
       (forall a b σ1 σ2, P a σ1 -> (W a).(nrm) σ1 b σ2 -> Q a b σ2) ->
       (forall a b σ1 σ2, P a σ1 -> (f W a).(nrm) σ1 b σ2 -> Q a b σ2)) ->
    (forall W: A -> program Σ B,
      (forall a σ1, P a σ1 -> (W a).(err) σ1 -> False) ->
       (forall a σ1, P a σ1 -> (f W a).(err) σ1 -> False)) ->
    (forall a b σ1 σ2, P a σ1 -> (BW_fix f a).(nrm) σ1 b σ2 -> Q a b σ2) /\ 
      (forall a σ1, P a σ1 -> (BW_fix f a).(err) σ1 -> False).
Proof.
  intros.
  split.
  + intros.
    destruct H2 as [n ?].
    revert a b σ1 σ2 H1 H2; induction n; simpl.
    1: { intros. hnf in H2. tauto. }
    apply H.
    apply IHn.
  + intros.
    simpl in H2.
    sets_unfold in H2.
    destruct H2 as [n ?].
    intros; revert a σ1 H1 H2; induction n; simpl.
    - tauto.
    - sets_unfold in H0.
      apply H0.
      intros.
      eapply IHn; eauto.
Qed.

Lemma range_plus_1_aux: forall (P: Z -> Prop) lo hi,
(forall i, lo <= i < hi -> P i) ->
(forall i, lo + 1 <= i < hi -> P i).
Proof.
intros.
apply H.
lia.
Qed.

Lemma range_iter_ind' {A Σ: Type} : 
forall (f: Z -> A -> program Σ A) (P: Z -> A -> Σ -> Prop) (lo hi: Z),
  lo <= hi ->
  (forall i, lo <= i < hi -> forall a, Hoare (P i a) (f i a) (P (i+1))) -> 
  (forall a, Hoare (P lo a) (range_iter lo hi f a) (P hi)).
Proof.
unfold Hoare.
intros.
pose proof fun i Hi a => (proj1 (H0 i Hi a)) as Hnrm.
pose proof fun i Hi a => (proj2 (H0 i Hi a)) as Herr.
clear H0.
unfold range_iter.
split; intros.
+ unfold range_iter_f in H1. 
  destruct H1 as [n ?].
  clear Herr.
  revert a a0 σ1 σ2 lo H Hnrm H0 H1. induction n; simpl.
  1: { intros. hnf in H1. tauto. }
  unfold nrm_nrm; sets_unfold.
  intros. destruct H1.
  - destruct H1 as [? [? [[? ?] ?]]].
    subst.
    destruct H3 as [? [? [? ?]]].
    pose proof Hnrm lo ltac:(lia) a _ _ _ H0 H1.
    pose proof (range_plus_1_aux _ _ _ Hnrm) as Hnrm'.
    eapply IHn; [ | | exact H4 | ].
    * lia.
    * apply Hnrm'.
    * apply H3.
  - destruct H1 as [? [? [[? ?] [? ?] ] ] ].
    assert (lo = hi) by lia.
    subst.
    unfold ret.
    tauto.
+ unfold range_iter_f in H1.
  simpl in H1.
  destruct H1 as [n ?].
  revert a σ1 lo H Hnrm Herr H0 H1; induction n; intros.
  - simpl in H1.
    apply H1.
  - simpl in H1.
    sets_unfold in H1.
    destruct H1 as [ [? | ?] | [? | ?] ]; try tauto.
    * unfold nrm_err in H1.
      destruct H1 as [? [? [? ?]]].
      destruct H1; subst.
      destruct H2; [ eapply (Herr lo ltac:(lia)); eauto | ].
      destruct H1 as [? [? [? ?]]].
      pose proof (range_plus_1_aux _ _ _ Hnrm) as Hnrm'.
      pose proof (range_plus_1_aux _ _ _ Herr) as Herr'.
      eapply (IHn _ _ (lo + 1) ltac:(lia)); eauto.
      eapply Hnrm; eauto.
      lia.
    * unfold nrm_err in H1.
      destruct H1 as [? [? ?] ].
      tauto.
Qed.

Lemma range_iter_break_ind' {A B Σ: Type} : 
forall (f: Z -> A -> program Σ (A + B)) (P: Z -> A -> Σ -> Prop) (Q: B -> Σ -> Prop) (lo hi: Z),
  lo <= hi ->
  (forall i, lo <= i < hi -> forall a,
     Hoare (P i a) (f i a) (fun res => match res with
                                       | inl a => P (i+1) a
                                       | inr b => Q b
                                       end)) -> 
  (forall a, Hoare (P lo a) (range_iter_break lo hi f a)
               (fun res σ => match res with
                             | inl a => P hi a σ
                             | inr b => Q b σ
                             end)).
Proof.
  unfold Hoare.
  intros.
  pose proof fun i Hi a => (proj1 (H0 i Hi a)) as Hnrm.
  pose proof fun i Hi a => (proj2 (H0 i Hi a)) as Herr.
  clear H0.
  unfold range_iter_break.
  split; intros.
  + unfold range_iter_break_f in H1.
    destruct H1 as [n ?].
    clear Herr.
    revert a a0 σ1 σ2 lo H Hnrm H0 H1. induction n; simpl.
    1: { intros. hnf in H1. tauto. }
    unfold nrm_nrm; sets_unfold.
    intros. destruct H1.
    - destruct H1 as [? [? [[? ?] ?]]].
      subst.
      destruct H3 as [? [? [? ?]]].
      destruct x1.
      * pose proof Hnrm lo ltac:(lia) a _ _ _ H0 H1.
        pose proof (range_plus_1_aux _ _ _ Hnrm) as Hnrm'.
        eapply IHn; [ | | exact H4 | ].
       ++ lia.
       ++ apply Hnrm'.
       ++ apply H3.
      * hnf in H3.
        destruct H3; subst.
        simpl.
        pose proof Hnrm lo ltac:(lia) a _ _ _ H0 H1.
        simpl in H3.
        tauto.
    - destruct H1 as [? [? [[? ?] [? ?] ] ] ].
      assert (lo = hi) by lia.
      subst.
      unfold ret.
      tauto.
  + unfold range_iter_break_f in H1.
    simpl in H1.
    destruct H1 as [n ?].
    revert a σ1 lo H Hnrm Herr H0 H1; induction n; intros.
    - simpl in H1.
      apply H1.
    - simpl in H1.
      sets_unfold in H1.
      destruct H1 as [ [? | ?] | [? | ?] ]; try tauto.
      * unfold nrm_err in H1.
        destruct H1 as [? [? [? ?]]].
        destruct H1; subst.
        destruct H2; [ eapply (Herr lo ltac:(lia)); eauto | ].
        destruct H1 as [? [? [? ?]]].
        pose proof (range_plus_1_aux _ _ _ Hnrm) as Hnrm'.
        pose proof (range_plus_1_aux _ _ _ Herr) as Herr'.
        destruct x1.
       ++ eapply (IHn _ _ (lo + 1) ltac:(lia)); eauto.
          specialize (Hnrm lo ltac:(lia) _ _ _ _ H0 H1).
          eapply Hnrm; eauto.
       ++ hnf in H2.
          tauto.
      * unfold nrm_err in H1.
        destruct H1 as [? [? ?] ].
        tauto.
Qed.

Lemma range_iter_ind {A Σ: Type}:
  forall (f: Z -> A -> program Σ A)
         (Q: Σ -> Prop) (P: Z -> A -> Σ -> Prop) (lo hi: Z),
    lo <= hi ->
    forall a, 
      (forall σ, Q σ -> P lo a σ) ->
      (forall i, lo <= i < hi -> forall a, Hoare (P i a) (f i a) (P (i+1))) -> 
      Hoare Q (range_iter lo hi f a) (P hi).
Proof.
  intros.
  eapply Hoare_pre; [ | apply (range_iter_ind' f P lo hi H H1)].
  auto.
Qed.

Lemma range_iter_break_ind {A B Σ: Type}:
  forall (f: Z -> A -> program Σ (A + B))
         (P: Z -> A -> Σ -> Prop)
         (Q1: Σ -> Prop)
         (Q2: B -> Σ -> Prop) (lo hi: Z),
    lo <= hi ->
    forall a,
      (forall σ, Q1 σ -> P lo a σ) ->
      (forall i, lo <= i < hi -> forall a,
         Hoare (P i a) (f i a) (fun res => match res with
                                           | inl a => P (i+1) a
                                           | inr b => Q2 b
                                           end)) -> 
      Hoare Q1
            (range_iter_break lo hi f a)
            (fun res σ => match res with
                          | inl a => P hi a σ
                          | inr b => Q2 b σ
                          end).
Proof.
  intros.
  eapply Hoare_pre; [ | apply (range_iter_break_ind' f P Q2 lo hi H H1)].
  auto.
Qed.

Lemma Hoare_bind {A B Σ: Type}: 
forall (P: Σ -> Prop) (Q : A -> Σ -> Prop) (R: B -> Σ -> Prop)
(c1: program Σ A) (c2: A -> program Σ B) ,
Hoare P c1 Q -> (forall a, Hoare (Q a) (c2 a) R) -> Hoare P (bind c1 c2) R.
Proof.
  unfold Hoare.
  intros.
  split; simpl.
  + unfold nrm_nrm; intros.
    destruct H2 as [? [? [? ?]]].
    destruct H.
    specialize (H0 x).
    destruct H0.
    eapply H0; eauto.
  + sets_unfold.
    unfold nrm_err; intros.
    destruct H2.
    - destruct H.
      apply (H3 σ1 H1 H2).
    - destruct H2 as [? [? [? ?]]].
      specialize (H0 x).
      destruct H; destruct H0.
      eapply H5; eauto.
Qed.

Lemma range_iter_no_iter {A Σ: Type} : 
forall (f: Z -> A -> program Σ A) (P: A -> Σ -> Prop) (lo hi: Z),
hi < lo ->
(forall a, Hoare (P a) (range_iter lo hi f a) P).
Proof.
  intros.
  unfold Hoare, range_iter, range_iter_f.
  split; intros.
  + destruct H1 as [n ?]; simpl in H1.
    destruct n; simpl in H1.
    - tauto.
    - unfold nrm_nrm in H1; simpl in H1.
      destruct H1.
      * destruct H1 as [? [? [? ?]]].
        lia.
      * destruct H1 as [? [? [? [? ?]]]].
        destruct H1; subst.
        unfold ret.
        tauto.
  + destruct H1 as [n ?]; simpl in H1.
    destruct n; simpl in H1.
    - tauto.
    - unfold nrm_err in H1; simpl in H1.
      destruct H1.
      * destruct H1; [tauto |].
        destruct H1 as [? [? [? ?]]].
        lia.
      * destruct H1; [tauto |].
        destruct H1 as [? [? [? ?]]].
        tauto.
Qed.

Lemma Hoare_proequiv:
  forall {A Σ: Type} (c1 c2: program Σ A) (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    c1 == c2 ->
    Hoare P c1 Q -> Hoare P c2 Q.
Proof.
  intros.
  unfold Hoare in *.
  destruct H0 as [H0 H1].
  unfold Sets.equiv in H; destruct H as [Hn He].
  split; intros.
  + specialize (H0 a σ1 σ2 H).
    apply H0; clear H0.    
    sets_unfold in Hn.
    apply Hn; auto.
  + specialize (H1 σ1 H).
    apply H1; clear H1.
    sets_unfold in He.
    apply He; auto.
Qed.

#[export] Instance Hoare_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (equiv ==> eq ==> iff) (@Hoare Σ A P).
Proof.
  unfold Proper, respectful; intros.
  subst x0; split; intros.
  - apply Hoare_proequiv with x; easy.
  - apply Hoare_proequiv with y; easy.
Qed.

Ltac hoare_intros :=
  apply Hoare_unit_pre; intros.

Ltac hoare_step :=
  match goal with
  | |- Hoare _ (test _ ;; _) _ => apply Hoare_test; intros; try hoare_step
  | |- Hoare _ (choice _ _) _ => apply Hoare_choice; try hoare_step
  | |- Hoare _ (_ <- return _;; _) _ => rewrite return_equiv; try hoare_step
  | |- Hoare _ (assert _ ;; _) _ => apply Hoare_assert_bind; intros; [ | try hoare_step]
  | |- Hoare _ (return _) _ => apply Hoare_return; intros
  | |- Hoare _ (inl_case (inr _)) _ => apply Hoare_inl_inr
  | |- Hoare _ (inr_case (inl _)) _ => apply Hoare_inr_inl
  | |- Hoare _ (inl_case (inl _)) _ => apply Hoare_inl_inl; intros
  | |- Hoare _ (inr_case (inr _)) _ => apply Hoare_inr_inr; intros
  end.
