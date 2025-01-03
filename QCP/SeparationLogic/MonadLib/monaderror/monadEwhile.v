Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From StateMonad Require Import monadEbasic.


Import SetsNotation.
Local Open Scope sets.
Export CPO_lift.
Local Open Scope order_scope.

(*************************************************************************************************************)
(**********************************          monad program registerd         *********************************)
(**********************************                program Σ A               *********************************)
(**********************************   class                                  *********************************)
(**********************************     1 : Order                            *********************************)
(**********************************       1.1 : Transitive                   *********************************)
(**********************************       1.2 : Reflexiitive                 *********************************)
(**********************************     2 : PartialOrder_Setoid              *********************************)
(**********************************     3 : OmegaCompletePartialOrder_Setoid *********************************)
(*************************************************************************************************************)

#[export] Instance oLub_program {Σ A: Type} : OmegaLub (MonadwitherrDeno.program Σ A) :=
  ProgramPO.indexed_union.

#[export] Instance bot_program {Σ A: Type} : Bot (MonadwitherrDeno.program Σ A) :=
  ProgramPO.bot.

#[export] Instance oCPO_program {Σ A: Type} : CompletePartialOrder_Setoid (MonadwitherrDeno.program Σ A).
Proof.
  split.
  + apply program_PO.
  + unfold seq_mono, seq_least_upper_bound, seq_upper_bound.
    unfold omega_lub, order_rel, program_order, oLub_program; simpl.
    intros T H.
    split.
    - intros n.
      specialize (H n) as [H H1].
      constructor;simpl in *. 
      * sets_unfold. intros.
        exists n.
        tauto.
      * sets_unfold. intros.
        exists n.
        tauto.
    - intros a H0.
      constructor;simpl in *.
      * sets_unfold.
        intros.
        destruct H1 as [n ?].
        specialize (H0 n) as [H0 _]. eapply H0;eauto.
      * sets_unfold.
        intros.
        destruct H1 as [n ?].
        specialize (H0 n) as [_ H0]. eapply H0;eauto.
  + unfold least_element.
    unfold bot, order_rel, program_order, bot_program; simpl.
    intros a.
    constructor;simpl.
    sets_unfold. 
    tauto.
    sets_unfold. 
    tauto.
Qed.

(*************************************************************************************************************)
(**********************************     lift monad program registerd         *********************************)
(**********************************           B -> program Σ A               *********************************)
(**********************************   class                                  *********************************)
(**********************************     1 : Order                            *********************************)
(**********************************       1.1 : Transitive                   *********************************)
(**********************************       1.2 : Reflexiitive                 *********************************)
(**********************************     2 : PartialOrder_Setoid              *********************************)
(**********************************     3 : OmegaCompletePartialOrder_Setoid *********************************)
(*************************************************************************************************************)
#[export] Instance Transitive_lift  {A: Type} {B: Type} {RB: Order B} {TB: Transitive (@order_rel B _) } 
  : Transitive (@order_rel (A -> B) _ ).
Proof.
  unfold Transitive, order_rel, R_lift, LiftConstructors.lift_rel2.
  intros.
  etransitivity;eauto.
Qed.

#[export] Instance Reflexive_lift  {A: Type} {B: Type} {RB: Order B} {ReflB: Reflexive (@order_rel B _) } 
  : Reflexive (@order_rel (A -> B) _ ).
Proof.
  unfold Reflexive, order_rel, R_lift, LiftConstructors.lift_rel2.
  intros.
  reflexivity.
Qed.



(*************************************************************************************************************)
(**********************************     mono and continuous_lemmas           *********************************)
(*************************************************************************************************************)
Section mono_and_continuous_lemmas.
  Import MonadwitherrDeno.
  Import MonadNotation.
  Local Open Scope stmonad.
  Context {Σ: Type}.

  Notation " ⋃  a " := (omega_lub a): order_scope.

  Definition increasing {A: Type} {RA: Order A } (T : nat -> A):= @seq_mono A RA T.

  Definition mono {A: Type} {RA: Order A}  {B: Type} {RB: Order B}  
    (f : A -> B) := Proper (order_rel ==> order_rel) f.
  Definition continuous {A: Type} {RA: Order A} {oLubA: OmegaLub A}
          {B: Type} {EB: Equiv B} {oLubB: OmegaLub B}
    (f : A -> B) := @seq_continuous  A RA oLubA B EB oLubB f.



  Lemma increasing_program_plus : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    increasing c -> c n <= c (n + m).
  Proof.
    induction m;intros.
    - assert (n + 0 = n) by lia. rewrite H0.
      reflexivity.
    - assert (n + S m = S (n + m)) by lia.
      rewrite H0.
      transitivity (c (n + m)).
      eapply IHm;auto.
      eapply H.
  Qed. 


  Lemma increasing_program_le : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    (n <= m)%nat ->  increasing c  -> c n <= c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus;auto.
  Qed.

  Lemma bind_omega_union_distr_l:
  forall
    {A B: Type}
    (c1: program Σ A)
    (c2: nat -> A ->program Σ B),
    bind c1 (⋃  c2) == ⋃  (fun n => bind c1 (c2 n)).
  Proof.
    intros.
    constructor.
    *
      intros s a s0. split; intros.
      - destruct H as [a0 [? [? [n ?]] ] ].
        exists n. exists a0, x. auto.
      - destruct H as [n [a0 [s1 [? ?]] ] ].
        exists a0, s1. split.
        + auto.
        + exists n. auto.
    * intros s. split;intros.
      - destruct H as [ | [a0 [? [? [n ?]]]]].
        exists 0. left;auto.
        exists n. right. exists a0, x. auto.
      - destruct H as  [n [ | [a0 [s1 [? ?]] ] ]].
        left. auto.
        right.
        exists a0, s1. split.
        + auto.
        + exists n. auto.
  Qed.

  Lemma bind_omega_union_distr_r:
  forall
    {A B: Type}
    (c1: nat -> program Σ A)
    (c2: A -> program Σ B),
    bind (⋃ c1) c2  == ⋃ (fun n => bind (c1 n) c2).
  Proof.
    intros.
    constructor.
    *  
      intros s a s0. split; intros.
      - destruct H as [a0 [? [[n ?] ?] ] ].
        exists n. exists a0, x. auto.
      - destruct H as [n [a0 [s1 [? ?]] ] ].
        exists a0, s1. split.
        + exists n. auto.
        + auto.
    * intros s. split;intros.
      - destruct H as [ [n H] | ].
        exists n. left. auto.
        destruct H as [a0 [? [[n ?] ?] ] ].
        exists n. right. exists a0, x. auto.
      - destruct H as [n [ | [a0 [s1 [? ?]] ] ]].
        left. exists n. auto.
        right. exists a0, s1. split.
        exists n. auto.
        auto.
  Qed.

  Lemma bind_omega_union_distr_r':
  forall
    {A B C: Type}
    (c1: nat -> A -> program Σ B)
    (c2: B -> program Σ C) a,
    bind ((⋃ c1) a) c2  == ⋃ (fun n => bind (c1 n a) c2).
  Proof.
    intros.
    constructor.
    * 
      intros s c s0. split; intros.
      - destruct H as [a0 [? [[n ?] ?] ] ].
        exists n. exists a0, x. auto.
      - destruct H as [n [a0 [s1 [? ?]] ] ].
        exists a0, s1. split.
        + exists n. auto.
        + auto.
    * intro s. split;intros.
      - destruct H as [ [n H] | [a0 [? [[n ?] ?] ] ] ].
        exists n. left. auto.
        exists n. right. exists a0, x. auto.
      - destruct H as [n [ | [a0 [s1 [? ?]] ]] ].
        left. exists n. auto.
        right. exists a0, s1. split.
        + exists n. auto.
        + auto.     
  Qed.

  Lemma mcompose_omega_union_distr_r:
  forall
    {A B C: Type}
    (c1: nat -> A -> program Σ B)
    (c2: B -> program Σ C),
    mcompose (⋃ c1) c2  == ⋃ (fun n => mcompose (c1 n) c2).
  Proof.
    intros.
    intros a.
    constructor.
    *
      intros s c s0. split; intros.
      - destruct H as [a0 [? [[n ?] ?] ] ].
        exists n. exists a0, x. auto.
      - destruct H as [n [a0 [s1 [? ?]] ] ].
        exists a0, s1. split.
        + exists n. auto.
        + auto.
    * intros s. split; intros.
      - destruct H as [ [n H] | [a0 [? [[n ?] ?] ] ]].
        exists n. left. auto.
        exists n. right. exists a0, x. auto.
      - destruct H as [n [ | [a0 [s1 [? ?]] ] ]].
        left. exists n. auto.
        right.
        exists a0, s1. split.
        + exists n. auto.
        + auto.
  Qed.

  Lemma bind_omega_union_distr_both:
  forall
    {A B C: Type}
    (c1: nat -> A -> program Σ B)
    (c2: nat -> B -> program Σ C),
    increasing c1 -> increasing c2 ->
    (fun a => bind ((⋃ c1) a) (⋃ c2)) == ⋃ (fun n => fun a => bind (c1 n a) (c2 n)).
  Proof.
    intros * Hc1 Hc2.
    sets_unfold.
    intros a.
    constructor.
    * 
      intros s c s0. split; intros.
      - destruct H as [b [s1 [[n0 ?] [n1 ?]] ] ].
        assert (n0 <= n1 \/ n1 < n0)%nat as [ | ] by lia.
        { exists n1. exists b, s1. split;auto. 
        eapply increasing_program_le;eauto. }
        exists n0. exists b, s1. split;auto. 
        eapply increasing_program_le with (n := n1);eauto.
        lia.
      - destruct H as [n [a0 [s1 [? ?]] ] ].
        exists a0, s1. split.
        + eexists. eauto.
        + exists n. auto.
    * intros s. split;intros.
      - destruct H as [ [n0 ?]| [b [s1 [[n0 ?] [n1 ?]] ] ]].
        exists n0. left. auto.
        assert (n0 <= n1 \/ n1 < n0)%nat as [ | ] by lia.
        { exists n1. right.  exists b, s1. split;auto. 
        eapply increasing_program_le;eauto. }
        exists n0. right. exists b, s1. split;auto. 
        eapply increasing_program_le with (n := n1);eauto.
        lia.
      - destruct H as [n [ | [a0 [s1 [? ?]] ]] ].
        left. exists n. auto.
        right.
        exists a0, s1. split.
        + eexists. eauto.
        + exists n. auto.
  Qed.

  Lemma bind_mono_left:
    forall {A B: Type}  (c2: A -> program Σ B),
      mono (fun c1 => (bind c1 c2)).
  Proof.
    intros.
    unfold mono.
    hnf.
    intros [c1 e1] [c1' e1'] [H H0]. 
    constructor;simpl in *.
    - 
      unfold nrm_nrm. 
      sets_unfold. clear H0.
      intros x b x0 H0.
      destruct H0 as (a & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
      eapply H. eauto.
    - unfold nrm_err.
      sets_unfold. 
      intros s H1.
      destruct H1.
      left. apply H0;eauto.
      destruct H1 as (a & x1 & ? & ?).
      right.
      exists a, x1.
      split;auto.
      apply H. auto.
  Qed.

  Lemma bind_mono_left':
    forall {A B C D: Type}  (c2: D -> B -> program Σ C) a,
      mono (fun (c1:A -> program Σ B) => (fun d => bind (c1 a) (c2 d))).
  Proof.
    intros.
    unfold mono.
    hnf.
    intros c1 c1'. 
    intros H d.
    specialize (H a) as [H H'].
    constructor; simpl.
    - unfold nrm_nrm. 
      intros  x c x0 H0.
      destruct H0 as (b & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
      apply H. auto.
    - unfold nrm_err.
      sets_unfold.
      intros s H0.
      destruct H0.
      left. apply H'. auto.
      right. 
      destruct H0 as (b & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
      apply H. auto. 
  Qed.

  Lemma bind_mono_right:
    forall {A B: Type}  (c1: program Σ A),
      mono (fun (c2 : A -> program Σ B) => (bind c1 c2)).
  Proof.
    intros.
    unfold mono.
    hnf.
    intros c2 c2' H. 
    constructor;simpl.
    - sets_unfold. 
      unfold nrm_nrm.
      intros x b x0 H0.
      destruct H0 as (a & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
      apply H. auto.
    - sets_unfold. 
      unfold nrm_err.
      intros s H0.
      destruct H0.
      left. auto.
      destruct H0 as (a & x1 & ? & ?).
      right.
      do 2 eexists.
      split;eauto.
      apply H. auto.
  Qed.

  Lemma bind_mono_f_right:
    forall {A B C: Type}  (c1: program Σ B) (f: (A -> program Σ C) -> (B -> program Σ C)),
      mono f ->
      mono (fun (c2 : A -> program Σ C) => (bind c1 (f c2))).
  Proof.
    intros.
    unfold mono in *.
    hnf.
    intros c2 c2' H0. 
    constructor;simpl.
    - sets_unfold. 
      unfold nrm_nrm.
      intros x b x0 H1.
      destruct H1 as (a0 & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
      eapply H;eauto.
    - sets_unfold. 
      unfold nrm_err.
      intros x H1.
      destruct H1.
      left. auto.
      destruct H1 as (a0 & x1 & ? & ?).
      right.
      do 2 eexists.
      split;eauto.
      eapply H;eauto. 
  Qed.

  Lemma bind_mono_f_right':
    forall {B C: Type}  (c1: program Σ B) (f: (program Σ C) -> (B -> program Σ C)),
      mono f ->
      mono (fun (c2 : program Σ C) => (bind c1 (f c2))).
  Proof.
    intros.
    unfold mono in *.
    hnf. hnf in H. 
    intros c2 c2' H0. 
    constructor;simpl.
    - sets_unfold. 
      unfold nrm_nrm.
      intros x b x0 H1.
      destruct H1 as (a0 & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
      eapply H;eauto.
    - sets_unfold. 
      unfold nrm_err.
      intros x H1.
      destruct H1.
      left. auto.
      destruct H1 as (a0 & x1 & ? & ?).
      right.
      do 2 eexists.
      split;eauto.
      eapply H;eauto. 
  Qed.

  Lemma bind_mono_compose_right:
    forall {A B C: Type}  (c1: A -> program Σ B) (f: (A -> program Σ C) -> (B -> program Σ C)),
      mono f ->
      mono (fun (c2 : A -> program Σ C) =>(fun a => (bind (c1 a) (f c2)))).
  Proof.
    intros.
    unfold mono in *.
    hnf. hnf in H.
    intros c2 c2' H0. 
    sets_unfold.
    constructor;simpl.
    - sets_unfold. 
      unfold nrm_nrm.
      intros x b x0 H1.
      destruct H1 as (a0 & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
      eapply H;eauto.
    - sets_unfold. 
      unfold nrm_err.
      intros x H1.
      destruct H1.
      left. auto.
      destruct H1 as (a0 & x1 & ? & ?).
      right.
      do 2 eexists.
      split;eauto.
      eapply H;eauto. 
  Qed.

  Lemma bind_mono_compose_right':
    forall {A B C D: Type}  (c1: D -> program Σ B) (f: D -> (A -> program Σ C) -> (B -> program Σ C)),
      (forall d, mono (f d))->
      mono (fun (c2 : A -> program Σ C) d => (bind (c1 d) (f d c2))).
  Proof.
    intros.
    unfold mono in *.
    hnf.
    intros c2 c2' H0. 
    sets_unfold.
    constructor;simpl.
    - sets_unfold. 
      unfold nrm_nrm.
      intros x b x0 H1.
      destruct H1 as (a0 & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
      specialize (H a).
      eapply H;eauto.
    - sets_unfold. 
      unfold nrm_err.
      intros x H1.
      destruct H1.
      left. auto.
      destruct H1 as (a0 & x1 & ? & ?).
      right.
      do 2 eexists.
      split;eauto.
      specialize (H a).
      eapply H;eauto. 
  Qed.

  Lemma bind_continuous_left:
    forall {A B: Type}  (c2: A -> program Σ B),
      continuous (fun c1 => (bind c1 c2)).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono.
    unfold  omega_lub, oLub_program.
    intros l H.
    constructor;simpl.
    *  
      sets_unfold.
      intros s b s0.
      unfold nrm_nrm.
      split;intros.
      - destruct H0 as (a & x1 & (n & ?) & ?).
        do 3 eexists.
        split;eauto.
      - destruct H0 as (n & a & x1 & ? & ?).
        do 2 eexists.
        split;eauto.
    * sets_unfold.
      intros s.
      unfold nrm_err.
      split;intros.
      - destruct H0 as [ [n ?] | (a & x1 & (n & ?) & ?)].
        eexists. left. eauto. 
        eexists.
        right.
        do 2 eexists.
        split;eauto.
      - destruct H0 as (n & ?).
        destruct H0 as [ | (a & x1 & ? & ?)].
        left. eexists. eauto.
        right.
        do 2 eexists.
        split;eauto. 
  Qed.

  Lemma bind_continuous_right:
    forall {A B: Type}  (c1: program Σ A),
      continuous (fun (c2: A -> program Σ B)  => (bind c1 c2)).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono.
    unfold  omega_lub, oLub_program.
    intros l H.
    constructor;simpl.
    * 
      sets_unfold.
      unfold nrm_nrm.
      intros x b x0.
      split;intros.
      - destruct H0 as (a & x1 & ? & (n & ?)).
        do 3 eexists.
        split;eauto.
      - destruct H0 as (n & a & x1 & ? & ?).
        do 2 eexists.
        split;[eauto |].
        eexists. eauto.
    * sets_unfold.
      intros s.
      unfold nrm_err.
      split;intros.
      - destruct H0 as [  | (a & x1 & ? & (n & ?))].
        exists 0.
        left. eauto. 
        exists n.
        right.
        do 2 eexists.
        split;eauto.
      - destruct H0 as (n & ?).
        destruct H0 as [ | (a & x1 & ? & ?)].
        left.  eauto.
        right.
        do 2 eexists.
        split;[eauto |].
        eexists. eauto. 
  Qed.
  
  Lemma bind_continuous_f_right:
    forall {A B C: Type}  (c1: program Σ B) (f: (A -> program Σ C) -> (B -> program Σ C)),
      continuous f ->
      continuous (fun (c2 : A -> program Σ C) =>(bind c1 (f c2))).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono.
    unfold  omega_lub, oLub_program.
    intros l Hl.
    sets_unfold.
    sets_unfold in H.
    specialize (H _ Hl).
    unfold bind.
    constructor;simpl.
    * unfold nrm_nrm.
      split;intros.
      - destruct H0 as (b & x1 & ? & ?).
        apply H in H1.
        destruct H1 as (n & ?).
        do 3 eexists.
        split;eauto.
      - destruct H0 as (n & b & x1 & ? & ?).
        do 2 eexists.
        split;eauto.
        apply H.
        sets_unfold.
        exists n.
        eauto.
    * unfold nrm_err.
      split;intros.
      - destruct H0 as [ | (b & x1 & ? & ?)].
        exists 0. left;eauto.
        apply H in H1.
        destruct H1 as (n & ?).
        exists n.
        right.
        do 2 eexists.
        split;eauto.
      - destruct H0 as (n & H0).
        destruct H0.
        left. auto.
        destruct H0 as (b & x1 & ? & ?).
        right.
        do 2 eexists.
        split;eauto.
        apply H.
        sets_unfold.
        exists n.
        eauto.
  Qed.

  Lemma bind_continuous_f_right':
    forall {B C: Type}  (c1: program Σ B) (f: (program Σ C) -> (B -> program Σ C)),
      continuous f ->
      continuous (fun (c2 : program Σ C) =>(bind c1 (f c2))).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono in *.
    unfold  omega_lub, oLub_program in *.
    intros l Hl.
    sets_unfold.
    sets_unfold in H.
    specialize (H _ Hl).
    unfold bind.
    constructor;simpl.
    * unfold nrm_nrm.
      split;intros.
      - destruct H0 as (b & x1 & ? & ?).
        apply H in H1.
        destruct H1 as (n & ?).
        do 3 eexists.
        split;eauto.
      - destruct H0 as (n & b & x1 & ? & ?).
        do 2 eexists.
        split;eauto.
        apply H.
        sets_unfold.
        exists n.
        eauto.
    * unfold nrm_err.
      split;intros.
      - destruct H0 as [ | (b & x1 & ? & ?)].
        exists 0. left;eauto.
        apply H in H1.
        destruct H1 as (n & ?).
        exists n.
        right.
        do 2 eexists.
        split;eauto.
      - destruct H0 as (n & H0).
        destruct H0.
        left. auto.
        destruct H0 as (b & x1 & ? & ?).
        right.
        do 2 eexists.
        split;eauto.
        apply H.
        sets_unfold.
        exists n.
        eauto.
  Qed.

  Lemma bind_continuous_compose_right:
    forall {A B C: Type}  (c1: A -> program Σ B) (f: (A -> program Σ C) -> (B -> program Σ C)),
      continuous f ->
      continuous (fun (c2 : A -> program Σ C) => (fun a => (bind (c1 a) (f c2)))).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono in *.
    unfold  omega_lub, oLub_program in *.
    intros l Hl.
    sets_unfold.
    sets_unfold in H.
    specialize (H _ Hl).
    unfold bind.
    constructor;simpl.
    * unfold nrm_nrm.
      split;intros.
      - destruct H0 as (b & x1 & ? & ?).
        apply H in H1.
        destruct H1 as (n & ?).
        do 3 eexists.
        split;eauto.
      - destruct H0 as (n & b & x1 & ? & ?).
        do 2 eexists.
        split;eauto.
        apply H.
        sets_unfold.
        exists n.
        eauto.
    * unfold nrm_err.
      split;intros.
      - destruct H0 as [ | (b & x1 & ? & ?)].
        exists 0. left;eauto.
        apply H in H1.
        destruct H1 as (n & ?).
        exists n.
        right.
        do 2 eexists.
        split;eauto.
      - destruct H0 as (n & H0).
        destruct H0.
        left. auto.
        destruct H0 as (b & x1 & ? & ?).
        right.
        do 2 eexists.
        split;eauto.
        apply H.
        sets_unfold.
        exists n.
        eauto.
  Qed.

  Lemma bind_continuous_compose_right':
    forall {A B C D: Type}  (c1: D -> program Σ B) (f: D -> (A -> program Σ C) -> (B -> program Σ C)),
      (forall d, continuous (f d)) ->
      continuous (fun (c2 : A -> program Σ C) => (fun d => (bind (c1 d) (f d c2)))).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono in *.
    unfold  omega_lub, oLub_program in *.
    intros l Hl.
    sets_unfold.
    sets_unfold in H.
    intros d.
    specialize (H d _ Hl).
    unfold bind.
    constructor;simpl.
    * unfold nrm_nrm.
      split;intros.
      - destruct H0 as (b & x1 & ? & ?).
        apply H in H1.
        destruct H1 as (n & ?).
        do 3 eexists.
        split;eauto.
      - destruct H0 as (n & b & x1 & ? & ?).
        do 2 eexists.
        split;eauto.
        apply H.
        sets_unfold.
        exists n.
        eauto.
    * unfold nrm_err.
      split;intros.
      - destruct H0 as [ | (b & x1 & ? & ?)].
        exists 0. left;eauto.
        apply H in H1.
        destruct H1 as (n & ?).
        exists n.
        right.
        do 2 eexists.
        split;eauto.
      - destruct H0 as (n & H0).
        destruct H0.
        left. auto.
        destruct H0 as (b & x1 & ? & ?).
        right.
        do 2 eexists.
        split;eauto.
        apply H.
        sets_unfold.
        exists n.
        eauto.
  Qed.

  Lemma  omega_union_introa: forall {A B: Type} (l: nat -> A -> program Σ B) a,
    (⋃ l) a == (⋃ (fun n => l n a)).
  Proof.
    intros.
    sets_unfold.
    constructor;simpl.
    split;intros;auto.
    split;intros;auto.
  Qed.
  

End mono_and_continuous_lemmas.

(*************************************************************************************************************)
(**********************************          while op for state monad        *********************************)
(**********************************                 program Σ A              *********************************)
(**********************************   1. while cond body :                   *********************************)
(**********************************            program Σ unit                *********************************)
(**********************************   2. whileret cond body :                *********************************)
(**********************************            A -> program Σ A              *********************************)
(**********************************   3. whilebreak body :                   *********************************)
(**********************************            A -> program Σ B              *********************************)
(*************************************************************************************************************)

Section  while_monad.

  Context {Σ: Type}.
  Import MonadwitherrDeno.
  Import MonadNotation.
  Local Open Scope stmonad.

  Definition while_f (cond:  (program Σ bool))  (body : (program Σ unit)) 
                     (W :  (program Σ unit)) 
                        : (program Σ unit) :=
  (x <- cond ;; (match x with 
  | true =>  seq body W
  | false => M_to_program (ret tt)
  end)).

 (* program Σ bool *) (* program Σ unit *)
  Definition while (cond: (program Σ bool)) (body : program Σ unit)  := BW_fix (while_f cond body).

  Definition whileret_f {A: Type}  (cond: A -> (program Σ bool)) (body : A -> (program Σ A)) 
                     (W :  A -> program Σ A) 
                        : A -> program Σ A :=
  fun a => (x <- (cond a) ;; match x with 
  | true =>  bind (body a) W
  | false => M_to_program (ret a)
  end).

  Definition whileret {A: Type}  (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  := BW_fix (whileret_f cond body).

  Definition whilebreak_f {A B: Type} (body: A -> program Σ (A + B)) (W: A -> program Σ B): A -> program Σ B :=
    fun a =>
      x <- body a;;
      match x with
      | inl a' => W a'
      | inr b => return b
      end.

  Definition whilebreak {A B: Type} (body: A -> program Σ (A + B)): A -> program Σ B :=
    BW_fix (whilebreak_f body).

  Definition range_iter_f {A: Type} (hi: Z) (body: Z -> A -> program Σ A) (W: Z -> A -> program Σ A): Z -> A -> program Σ A :=
    fun lo a0 => 
      choice
        (test (lo < hi)%Z;;
         a1 <- body lo a0;;
         W (lo + 1)%Z a1)
        (test (lo >= hi)%Z;;
         return a0).

  Definition range_iter {A: Type} (lo hi: Z) (body: Z -> A -> program Σ A): A -> program Σ A :=
    BW_fix (range_iter_f hi body) lo.

  Definition range_iter_break_f {A B: Type} (hi: Z) (body: Z -> A -> program Σ (A + B)) (W: Z -> A -> program Σ (A + B)): Z -> A -> program Σ (A + B) :=
    fun lo a0 => 
      choice
        (test (lo < hi)%Z;;
         ab <- body lo a0;;
         match ab with
         | inl a1 => W (lo + 1)%Z a1
         | inr b => return inr b
         end)
        (test (lo >= hi)%Z;;
         return (inl a0)).

  Definition range_iter_break {A B: Type} (lo hi: Z) (body: Z -> A -> program Σ (A + B)): A -> program Σ (A + B) :=
    BW_fix (range_iter_break_f hi body) lo.

  Definition Repeat_f  (body : (program Σ unit)) 
                      (W : (program Σ unit)) 
                          : (program Σ unit) :=
    W ;; body.

  Definition Repeat (body : (program Σ unit))  := BW_fix (Repeat_f body).

  Definition return_some {A: Type} (a: option A): program Σ bool :=
    match a with 
    | Some _ => return true
    | None => return false
    end.
    
  Lemma whilef_mono:
    forall cond body,
    mono (fun x => while_f cond body x).
  Proof.
    intros.
    unfold while_f.
    eapply bind_mono_f_right'.
    unfold mono. hnf.
    intros c1 c2 H.
    unfold order_rel, R_lift, LiftConstructors.lift_rel2.
    intros b.
    constructor;simpl.
    *  
      unfold seq, bind.
      destruct b;simpl.
      - unfold nrm_nrm. sets_unfold.
        intros x a x0 H0.
        destruct H0 as (a0 & x1 & ? & H0).
        exists a0, x1.
        split;auto.
        apply H;auto.
      - sets_unfold.
        intros. auto. 
    * unfold seq, bind.
      destruct b;simpl.
      - unfold nrm_err. sets_unfold.
        intros x H0.
        destruct H0 as [ | (a0 & x1 & ? & H0)].
        left;auto.
        right.
        exists a0, x1.
        split;auto.
        apply H;auto.
      - sets_unfold.
        intros. auto.  
  Qed.

  Lemma whilef_continuous:
    forall cond body,
    continuous (fun x => while_f cond body x).
  Proof.
    intros.
    unfold while_f.
    eapply bind_continuous_f_right'.
    unfold continuous, seq_continuous, seq_mono.
    intros l Hl.
    intros b.
    constructor;simpl.
    * sets_unfold.
      unfold seq,bind.
      intros x c x0. split; intros.
      + 
        destruct b;simpl in *.
        - destruct H as [t [x1 [? [n ?] ] ]].
          exists n. 
          exists t, x1.
          split; auto.
        - exists O. auto.
      + destruct b;simpl in *.
        - destruct H as [n [t [x1 [? ?] ] ]].
          exists t, x1. split;auto.
          exists n. auto.
        - destruct H. auto.
    * sets_unfold.
      unfold seq,bind.
      intros x. split; intros.
      + 
        destruct b;simpl in *.
        - destruct H as [ | [t [x1 [? [n ?] ] ]]].
          exists 0. left. auto.
          exists n. right. 
          exists t, x1.
          split; auto.
        - exists O. auto.
      + destruct b;simpl in *.
        - destruct H as [n [ | [t [x1 [? ?] ] ]]].
          left. auto.
          right.
          exists t, x1. split;auto.
          exists n. auto.
        - destruct H. auto. 
  Qed.

  Lemma whileretf_mono:
    forall {A: Type}  cond (body : A -> (program Σ A)),
    mono (fun x => whileret_f cond body x).
  Proof.
    intros.
    unfold whileret_f.
    eapply bind_mono_compose_right'.
    intros a.
    unfold mono. hnf. intros c1 c2 H.
    unfold seq, bind, order_rel, R_lift, LiftConstructors.lift_rel2.
    intros b.
    constructor;simpl.
    * 
      sets_unfold.
      intros x a0 x0.
      destruct b;simpl.
      - unfold nrm_nrm;intros. 
        destruct H0 as (? & ? & ? & ?).
        do 2 eexists.
        split;eauto.
        apply H;auto.
      - auto.
    * sets_unfold.
      intros x.
      destruct b;simpl;auto.
      intros H0.
      destruct H0.
      - left;auto. 
      - right. unfold nrm_err;intros. 
        destruct H0 as (? & ? & ? & ?).
        do 2 eexists.
        split;eauto.
        apply H;auto.
  Qed.

  Lemma whileretf_continuous:
    forall {A: Type}  cond (body : A -> (program Σ A)),
    continuous (fun x => whileret_f cond body x).
  Proof.
    intros.
    unfold whileret_f.
    eapply bind_continuous_compose_right'.
    intros a.
    unfold continuous, seq_continuous, seq_mono.
    intros l H b.
    constructor;simpl.
    * unfold seq,bind.
      sets_unfold.
      intros x a' x'.
      split; intros.
      + 
        destruct b;simpl in *.
        - destruct H0 as [t [x1 [? [n ?] ] ]].
          exists n.
          exists t, x1.
          split; auto.
        - exists O. auto. 
      + destruct b;simpl in *.
        - destruct H0 as [n [t [x1 [? ?] ] ]].
          exists t, x1. split;eauto.
          exists n. auto.
        - destruct H0. auto. 
    * unfold seq,bind.
      sets_unfold.
      intros x.
      split; intros.
      + 
        destruct b;simpl in *.
        - destruct H0 as [ | [t [x1 [? [n ?] ] ]]];[exists 0;left;auto | ].
          exists n. right.
          exists t, x1.
          split; auto.
        - exists O. auto. 
      + destruct H0 as [n H0].
        destruct b;simpl in *.
        - destruct H0 as [ | [t [x1 [? ?] ] ]];[left;auto | ].
          right.
          exists t, x1. split;eauto.
          exists n. auto.
        - auto. 
  Qed.

  Lemma whilebreak_f_mono:
    forall {A B} (body: A -> program Σ (A + B)),
      mono (whilebreak_f body).
  Proof.
    intros.
    unfold mono. hnf. intros D1 D2 ?.
    unfold order_rel, R_lift, LiftConstructors.lift_rel2.
    unfold whilebreak_f.
    sets_unfold.
    unfold seq, bind.
    intros a.
    constructor;simpl in *.
    * unfold nrm_nrm. 
      intros sigma b sigma'.
      intros [ c0 [sigma0 [? ?]]].
      exists c0, sigma0.
      split; [tauto |].
      destruct c0 as [a0 | b0].
      + apply H; tauto.
      + tauto.
     * unfold nrm_err. 
      intros sigma. 
      intros [ | [c0 [sigma0 [? ?]]]].
      left;auto.
      right.
      exists c0, sigma0.
      split; [tauto |].
      destruct c0 as [a0 | b0].
      + apply H; tauto.
      + tauto.
  Qed.

  Lemma whilebreak_f_continuous:
    forall {A B} (body: A -> program Σ (A + B)),
      continuous (whilebreak_f body).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono.
    intros.
    unfold whilebreak_f.
    unfold seq,bind.
    intros a.
    constructor;simpl in *.
    * unfold nrm_nrm;simpl.
      intros sigma b sigma'.
      split.
      + intros [c0 [sigma0 [? ?]]].
        destruct c0 as [a0 | b0].
        - destruct H1 as [i ?]; exists i.
          exists (inl a0), sigma0.
          tauto.
        - exists (0%nat), (inr b0), sigma0.
          tauto.
      + intros [i [c0 [sigma0 [? ?]]]].
        exists c0, sigma0.
        split; [tauto |].
        destruct c0; [exists i |]; tauto.
    * unfold nrm_err;simpl.
      intros sigma.
      split.
      + intros [ | [c0 [sigma0 [? ?]]]].
        exists 0. left;auto.
        destruct c0 as [a0 | b0].
        - destruct H1 as [i ?]; exists i.
          right.
          exists (inl a0), sigma0.
          tauto.
        - exists (0%nat). right. exists (inr b0), sigma0.
          tauto.
      + intros [i [ | [c0 [sigma0 [? ?]]]]].
        left;auto.
        right.
        exists c0, sigma0.
        split; [tauto |].
        destruct c0; [exists i |]; tauto. 
  Qed.

  Lemma Repeatf_mono:
    forall body,
    mono (fun x => Repeat_f body x).
  Proof.
    intros.
    unfold Repeat_f.
    eapply bind_mono_left.
  Qed.

  Lemma Repeatf_continuous:
    forall body,
    continuous (fun x => Repeat_f body x).
  Proof.
    intros.
    unfold Repeat_f.
    eapply bind_continuous_left.
  Qed.

  Lemma range_iter_f_mono:
    forall {A: Type} hi (body: Z -> A -> program Σ A),
    mono (range_iter_f hi body).
  Proof.
    intros. unfold range_iter_f.
    unfold mono; hnf. intros c1 c2 H; rename H into H0.
    unfold order_rel, R_lift, LiftConstructors.lift_rel2 in *.
    intros.
    constructor; unfold choice; simpl.
    - unfold nrm_nrm; sets_unfold; intros.
      destruct H. 
      + destruct H as [u [? ?]].
        destruct H as [[? ?] [? ?]]. 
        destruct H2 as [? [? ?]].
        left. exists u; exists x.
        split; auto.
        exists x0; exists x1.
        apply H0 in H3; split; auto.
      + destruct H as [u [? ?]].
        right. exists u; exists x; auto.
    - repeat rewrite Sets_empty_union.
      unfold nrm_err; sets_unfold; intros.
      destruct H.
      + destruct H as [u [? ?]].
        left; exists u; exists x.
        split; try tauto.
        destruct H as [? ?].
        destruct H1; try tauto.
        destruct H1 as [? [? [? ?]]].
        right; exists x0; exists x1.
        apply H0 in H2; auto.
      + destruct H as [u [? ?]].
        right; exists u; exists x; auto.
  Qed.

  Lemma range_iter_f_continuous:
    forall {A: Type} hi (body: Z -> A -> program Σ A),
    continuous (range_iter_f hi body).
  Proof.
    intros; unfold continuous, seq_continuous, seq_mono.
    intros;  unfold range_iter_f.
    constructor; unfold choice; simpl; rename H into H0.
    - unfold nrm_nrm; sets_unfold; split; intros; 
      [destruct H | destruct H; destruct H].
      + repeat destruct H as [? H].
        exists x3; left.
        exists x; exists x0; split; try tauto.
        exists x1; exists x2; tauto.
      + destruct H as [? [? ?]].
        exists 0; right.
        exists x; exists x0; tauto.
      + repeat destruct H as [? H].
        left; exists x0; exists x1.
        split; try tauto.
        exists x2; exists x3; split; try tauto.
        exists x; auto.
      + destruct H as [? [? ?]].
        right; exists x0; exists x1; tauto.
   - repeat rewrite Sets_empty_union.
     assert (For: forall P, False \/ P <-> P) by tauto.
     unfold nrm_err; sets_unfold; split; intros;
     [destruct H | destruct H; destruct H].
     + repeat destruct H as [? H].
       destruct H.
       { 
         exists 0; left; rewrite For.
         exists x; exists x0; tauto.
       }
       repeat destruct H as [? H].
       exists x3; left; rewrite For.
       exists x; exists x0.
       split; try tauto.
       right; exists x1; exists x2; tauto.
    + repeat destruct H as [? H]; tauto.
    + destruct H; try tauto; left.
      repeat destruct H as [? H].
      exists x0; exists x1; split; try tauto.
      destruct H; try tauto.
      repeat destruct H as [? H].
      right; exists x2; exists x3.
      split; try tauto.
      exists x; tauto.
    + destruct H; tauto.       
  Qed.

  (* basically the same with range_iter_f_mono *)
  Lemma range_iter_break_f_mono:
    forall {A B: Type} hi (body: Z -> A -> program Σ (A+B)),
    mono (range_iter_break_f hi body).
  Proof.
    intros. unfold range_iter_break_f.
    unfold mono; hnf; intros c1 c2 H; rename H into H0.
    unfold order_rel, R_lift, LiftConstructors.lift_rel2 in *.
    intros.
    constructor; unfold choice; simpl.
    - unfold nrm_nrm; sets_unfold; intros.
      destruct H. 
      + destruct H as [u [? ?]].
        destruct H as [[? ?] [? ?]]. 
        destruct H2 as [? [? ?]].
        left. exists u; exists x.
        split; auto.
        exists x0; exists x1.
        destruct x0; try apply H0 in H3; tauto.
      + destruct H as [u [? ?]].
        right. exists u; exists x; auto.
    - repeat rewrite Sets_empty_union.
      unfold nrm_err; sets_unfold; intros.
      destruct H.
      + destruct H as [u [? ?]].
        left; exists u; exists x.
        split; try tauto.
        destruct H as [? ?].
        destruct H1; try tauto.
        destruct H1 as [? [? [? ?]]].
        right; exists x0; exists x1.
        destruct x0; try apply H0 in H2; tauto.
      + destruct H as [u [? ?]].
        right; exists u; exists x; auto.
  Qed.

  Lemma range_iter_break_f_continuous:
    forall {A B: Type} hi (body: Z -> A -> program Σ (A+B)),
    continuous (range_iter_break_f hi body).
  Proof.
    intros; unfold continuous, seq_continuous, seq_mono.
    intros; sets_unfold; unfold range_iter_break_f.
    constructor; unfold choice; simpl; rename H into H0.
    - unfold nrm_nrm; sets_unfold; split; intros; 
      [destruct H | destruct H; destruct H].
      + repeat destruct H as [? H]. 
        destruct x1.
        * destruct H as [x3 ?].
          exists x3; left.
          exists x; exists x0; split; try tauto.
          exists (inl a4); exists x2; tauto.
        * exists 0; left.
          exists x; exists x0; split; try tauto.
          exists (inr b); exists x2; tauto.
      + destruct H as [? [? ?]].
        exists 0; right.
        exists x; exists x0; tauto.
      + repeat destruct H as [? H].
        left; exists x0; exists x1.
        split; try tauto.
        exists x2; exists x3; split; try tauto.
        destruct x2; try tauto.
        simpl; sets_unfold.
        exists x; tauto.
      + destruct H as [? [? ?]].
        right; exists x0; exists x1; tauto.
   - repeat rewrite Sets_empty_union.
     assert (For: forall P, False \/ P <-> P) by tauto.
     unfold nrm_err; sets_unfold; split; intros;
     [destruct H | destruct H; destruct H].
     + repeat destruct H as [? H].
       destruct H.
       { 
         exists 0; left; rewrite For.
         exists x; exists x0; tauto.
       }
       repeat destruct H as [? H].
       destruct x1.
       * simpl in H; sets_unfold in H.
         destruct H as [x3 H].
         exists x3; left; rewrite For.
         exists x; exists x0.
         split; try tauto.
         right; exists (inl a2); exists x2; tauto.
       * exists 0; left; right.
         exists x; exists x0; split; tauto. 
    + repeat destruct H as [? H]; tauto.
    + destruct H; try tauto; left.
      repeat destruct H as [? H].
      exists x0; exists x1; split; try tauto.
      destruct H; try tauto.
      repeat destruct H as [? H].
      right; exists x2; exists x3.
      split; try tauto.
      destruct x2; try tauto.
      simpl; sets_unfold.
      exists x; tauto.
    + destruct H; tauto.       
  Qed.

  Lemma while_unfold: forall (cond: (program Σ bool)) (body : program Σ unit), 
  while cond body == (x <- cond ;; 
                      if x then body ;; (while cond body) 
                            else return tt).
  Proof.
    intros.
    unfold while.
    apply (BourbakiWitt_fixpoint (while_f cond body)).
    + apply whilef_mono.
    + apply whilef_continuous.
  Qed.


  Lemma whileret_unfold: forall {A: Type} (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  (a: A), 
    whileret cond body a == (x <- (cond a);; 
                            if x then y <- body a ;; whileret cond body y
                                else return a).
  Proof.
    intros.
    unfold whileret.
    pose proof BourbakiWitt_fixpoint (whileret_f cond body) (whileretf_mono _ _) (whileretf_continuous _ _).
    eapply H.
  Qed.

  Lemma whilebreak_unfold {A B: Type}:
    forall (body: A -> program Σ (A + B)),
    whilebreak body == fun a =>
                        x <- body a;; 
                        match x with
                        | inl a0 => whilebreak body a0
                        | inr b0 => return b0
                        end.
  Proof.
    intros.
    unfold whilebreak.
    apply (BourbakiWitt_fixpoint (whilebreak_f body)).
    + apply whilebreak_f_mono.
    + apply whilebreak_f_continuous.
  Qed.

  Lemma range_iter_unfold_aux:
    forall {A: Type} (hi: Z) (body: Z -> A -> program Σ A),
    (fun lo a => range_iter lo hi body a) ==
    fun lo a => choice
      (test (lo < hi)%Z;;
      b <- body lo a;;
      range_iter (lo + 1)%Z hi body b)
      (test (lo >= hi)%Z;;
      return a).
  Proof.
    intros. unfold range_iter.
    apply (BourbakiWitt_fixpoint (range_iter_f hi body)).
    apply range_iter_f_mono.
    apply range_iter_f_continuous.
  Qed.

  Lemma range_iter_unfold:
    forall {A: Type} (hi: Z) (body: Z -> A -> program Σ A) lo a,
    range_iter lo hi body a ==
    choice
      (test (lo < hi)%Z;;
      b <- body lo a;;
      range_iter (lo + 1)%Z hi body b)
      (test (lo >= hi)%Z;;
      return a).
  Proof.
    intros.
    pose proof (range_iter_unfold_aux hi body).
    unfold Sets.equiv in H; simpl in H.
    unfold Sets.lift_equiv in H.
    specialize (H lo).
    unfold Sets.equiv in H; simpl in H.
    unfold Sets.lift_equiv in H.
    specialize (H a).
    auto.
Qed.

  Lemma range_iter_break_unfold_aux:
    forall {A B: Type} (hi: Z) (body: Z -> A -> program Σ (A+B)),
    (fun lo a => range_iter_break lo hi body a) ==
    fun lo a => choice
      (test (lo < hi)%Z;;
      b <- body lo a;;
      match b with
      | inl al => range_iter_break (lo + 1)%Z hi body al
      | inr br => return inr(br)
      end)
      (test (lo >= hi)%Z;;
      return inl (a)).
  Proof.
    intros. unfold range_iter_break.
    apply (BourbakiWitt_fixpoint (range_iter_break_f hi body)).
    apply range_iter_break_f_mono.
    apply range_iter_break_f_continuous.
  Qed.

  Lemma range_iter_break_unfold:
    forall {A B: Type} (hi: Z) (body: Z -> A -> program Σ (A+B)) lo a,
    range_iter_break lo hi body a ==
    choice
      (test (lo < hi)%Z;;
      b <- body lo a;;
      match b with
      | inl al => range_iter_break (lo + 1)%Z hi body al
      | inr br => return inr(br)
      end)
      (test (lo >= hi)%Z;;
      return inl (a)).
  Proof.
    intros.
    pose proof (range_iter_break_unfold_aux hi body).
    unfold Sets.equiv in H; simpl in H.
    unfold Sets.lift_equiv in H.
    specialize (H lo).
    unfold Sets.equiv in H; simpl in H.
    unfold Sets.lift_equiv in H.
    specialize (H a).
    auto.
  Qed.

End  while_monad.

Ltac unfold_loop H :=
  rewrite (while_unfold _ _ ) in H ||
  rewrite (whilebreak_unfold _ _) in H ||
  rewrite range_iter_unfold in H ||
  rewrite range_iter_break_unfold in H.
