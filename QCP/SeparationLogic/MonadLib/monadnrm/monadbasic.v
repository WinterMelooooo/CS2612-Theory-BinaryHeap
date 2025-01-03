Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
From SetsClass Require Import SetsClass.
From FP Require Import SetsFixedpoints.


Import SetsNotation.
Local Open Scope sets.


Section  stmonad.
  Context {Σ: Type}.
  Definition M (A: Type) : Type := Σ -> A.
  Definition ret {A: Type}(a: A) : M A := fun _ => a.
  Definition rbind {A B: Type}(m: M A)(f: A -> M B): M B :=
    fun s => f (m s) s.
  Definition getst: M Σ := fun s => s.

  Definition program (A: Type): Type := Σ -> A -> Σ -> Prop.

  Coercion M_to_program {A: Type}(m: M A): program A :=
              fun s1 a s2 => a = m s1 /\ s2 = s1.

  Definition step : Type := Σ -> Σ -> Prop.

  Coercion step_to_program (m: step): program unit :=
              fun s1 a s2 => a = tt /\ m s1 s2.

  Definition bind {A B: Type}(m: program A)(f: A -> program B): program B :=
      fun s1 b s2  => exists a s0, m s1 a s0 /\ f a s0 b s2. 
  
  Definition seq  {A B: Type} (m1: program A)(m2: program B) : program B  := bind m1 (fun _ => m2).

  Definition mcompose {A B C:Type}
  (f: A -> program B) (g: B -> program C): (A -> program C) :=
    fun x => bind (f x) g.

  Definition choice {A: Type}
    (f g: program A): program A := f ∪ g.

  Definition test (P: Prop): program unit :=
    fun s1 _ s2 => s1 = s2 /\ P.

  (* do not return anything, encoded by returning the dummy constant tt. *)
  Definition put (s: Σ) : program unit := fun s1 a s2 => a = tt /\ s2 = s.

  Definition Id {A: Type} (a: A) : program A := M_to_program (ret a).

End  stmonad.


Module MonadNotation.

  Declare Scope stmonad_scope.
  Delimit Scope stmonad_scope with stmonad.

  Notation "c >>= f" := (@bind _ _ _  c f) (at level 58, left associativity) : stmonad_scope.
  Notation "f =<< c" := (@bind _ _ _ c f) (at level 61, right associativity) : stmonad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ f g) (at level 61, right associativity) : stmonad_scope.

  Notation "'return' v" := (M_to_program (ret v)) (at level 60, no associativity) : stmonad_scope.
  Notation "'get'" := (M_to_program (getst)) (at level 60, no associativity) : stmonad_scope.

  Notation "e1 ;; e2" := (@seq _ _ _ e1 e2)
    (at level 61, right associativity) : stmonad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _  c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : stmonad_scope.
  
  Notation " x : T <- c1 ;; c2" :=(@bind _ _ _ c1 (fun x : T => c2))
    (at level 61, c1 at next level, right associativity) : stmonad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ _  c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : stmonad_scope.

  Notation "'let*' p ':=' c1 'in' c2" := (@bind _ _ _  c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity) : stmonad_scope.

  Notation "'MONAD' A " := (@program unit A) (at level 60, no associativity) : stmonad_scope.

End MonadNotation.

Arguments program Σ%type_scope A%type_scope: clear implicits.

Section mono_and_continuous_lemmas.

  Definition increasing {A: Type} {_SETS_A : Sets.SETS A} (T : nat -> A):= @sseq_mono A _SETS_A T.
  Definition mono {A: Type} {_SETS_A : Sets.SETS A}  {B: Type} {_SETS_B : Sets.SETS B}  
    (f : A -> B) := Proper (Sets.included ==> Sets.included) f.
  Definition continuous {A: Type} {_SETS_A : Sets.SETS A} {B: Type} {_SETS_B : Sets.SETS B} 
    (f : A -> B) := @sseq_continuous  A _SETS_A B _SETS_B f.
  Context {Σ: Type}.

  Lemma increasing_mono_increasing:
  forall {A B: Type} {_SETS_A : Sets.SETS A}  {_SETS_B : Sets.SETS B}
         (f: A -> B)
         (l: nat -> A),
    increasing l -> mono f -> increasing (fun n => f (l n)).
  Proof.
    intros.
    unfold increasing, sseq_mono. intros.
    apply H0. apply H.
  Qed.


  Lemma increasing_program_plus : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    increasing c -> c n ⊆ c (n + m).
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
    n <= m ->  increasing c -> c n ⊆ c m.
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
    bind c1 (⋃ c2) == ⋃ (fun n => bind c1 (c2 n)).
  Proof.
    intros.
    sets_unfold.
    intros s a s0. split; intros.
    - destruct H as [a0 [? [? [n ?]] ] ].
      exists n. exists a0, x. auto.
    - destruct H as [n [a0 [s1 [? ?]] ] ].
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
    sets_unfold.
    intros s a s0. split; intros.
    - destruct H as [a0 [? [[n ?] ?] ] ].
      exists n. exists a0, x. auto.
    - destruct H as [n [a0 [s1 [? ?]] ] ].
      exists a0, s1. split.
      + exists n. auto.
      + auto.
  Qed.

  Lemma bind_omega_union_distr_r':
  forall
    {A B C: Type}
    (c1: nat -> A -> program Σ B)
    (c2: B -> program Σ C) a,
    bind ((⋃ c1) a) c2  == ⋃ (fun n => bind (c1 n a) c2).
  Proof.
    intros.
    sets_unfold.
    intros s c s0. split; intros.
    - destruct H as [a0 [? [[n ?] ?] ] ].
      exists n. exists a0, x. auto.
    - destruct H as [n [a0 [s1 [? ?]] ] ].
      exists a0, s1. split.
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
    sets_unfold.
    intros a s c s0. split; intros.
    - destruct H as [a0 [? [[n ?] ?] ] ].
      exists n. exists a0, x. auto.
    - destruct H as [n [a0 [s1 [? ?]] ] ].
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
    intros a s c s0. split; intros.
    - destruct H as [b [s1 [[n0 ?] [n1 ?]] ] ].
      assert (n0 <= n1 \/ n1 < n0) as [ | ] by lia.
      { exists n1. exists b, s1. split;auto. 
      eapply increasing_program_le;eauto. }
      exists n0. exists b, s1. split;auto. 
      eapply increasing_program_le with (n := n1);eauto.
      lia.
    - destruct H as [n [a0 [s1 [? ?]] ] ].
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
    intros c1 c1'. 
    sets_unfold.
    unfold bind.
    intros H x b x0 H0.
    destruct H0 as (a & x1 & ? & ?).
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma bind_mono_left':
    forall {A B C D: Type}  (c2: D -> B -> program Σ C) a,
      mono (fun (c1:A -> program Σ B) => (fun d => bind (c1 a) (c2 d))).
  Proof.
    intros.
    unfold mono.
    hnf.
    intros c1 c1'. 
    sets_unfold.
    unfold bind.
    intros H d  x c x0 H0.
    destruct H0 as (b & x1 & ? & ?).
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma bind_mono_right:
    forall {A B: Type}  (c1: program Σ A),
      mono (fun (c2 : A -> program Σ B) => (bind c1 c2)).
  Proof.
    intros.
    unfold mono.
    hnf.
    intros c2 c2'. 
    sets_unfold.
    unfold bind.
    intros H x b x0 H0.
    destruct H0 as (a & x1 & ? & ?).
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma bind_mono_compose_right:
    forall {A B C: Type}  (c1: A -> program Σ B) (f: (A -> program Σ C) -> (B -> program Σ C)),
      mono f ->
      mono (fun (c2 : A -> program Σ C) =>(fun a => (bind (c1 a) (f c2)))).
  Proof.
    intros.
    unfold mono in *.
    hnf.
    intros c2 c2'. 
    sets_unfold.
    unfold bind.
    intros H0 a x b x0 H1.
    destruct H1 as (a0 & x1 & ? & ?).
    do 2 eexists.
    split;eauto.
    eapply H;eauto.
    intros a1 x2.
    sets_unfold.
    intros.
    eapply H0;auto.
  Qed.

  Lemma bind_continuous_left:
    forall {A B: Type}  (c2: A -> program Σ B),
      continuous (fun c1 => (bind c1 c2)).
  Proof.
    intros.
    unfold continuous.
    hnf.
    intros l H x b. 
    sets_unfold.
    unfold bind.
    intros x0.
    split;intros.
    - destruct H0 as (a & x1 & (n & ?) & ?).
      do 3 eexists.
      split;eauto.
    - destruct H0 as (n & a & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
  Qed.

  Lemma bind_continuous_right:
    forall {A B: Type}  (c1: program Σ A),
      continuous (fun (c2: A -> program Σ B)  => (bind c1 c2)).
  Proof.
    intros.
    unfold continuous.
    hnf.
    intros l H x b. 
    sets_unfold.
    unfold bind.
    intros x0.
    split;intros.
    - destruct H0 as (a & x1 & ? & (n & ?)).
      do 3 eexists.
      split;eauto.
    - destruct H0 as (n & a & x1 & ? & ?).
      do 2 eexists.
      split;eauto.
  Qed.
  

  Lemma bind_continuous_compose_right:
    forall {A B C: Type}  (c1: A -> program Σ B) (f: (A -> program Σ C) -> (B -> program Σ C)),
      continuous f ->
      continuous (fun (c2 : A -> program Σ C) => (fun a => (bind (c1 a) (f c2)))).
  Proof.
    intros.
    unfold continuous in *.
    hnf. hnf in H.
    intros l Hl.
    sets_unfold.
    sets_unfold in H.
    specialize (H _ Hl).
    unfold bind.
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
      eauto.
  Qed.

  Lemma  omega_union_introa: forall {A B: Type} (l: nat -> A -> program Σ B) a,
    (⋃ l) a == (⋃ (fun n => l n a)).
  Proof.
    intros.
    sets_unfold.
    split;intros;auto.
  Qed.
  
  Lemma choice_proper: forall {A: Type},
    Proper (Sets.included ==> Sets.included ==> Sets.included) (@choice Σ A).
  Proof.
    unfold Proper, respectful.
    intros.
    unfold choice.
    rewrite H, H0.
    reflexivity.
  Qed.

  Lemma choice_equiv_equiv : forall {A : Type} (c1 c2 c3 c4 : program Σ A), c1 == c2 -> c3 == c4 -> choice c1 c3 == choice c2 c4.
  Proof.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed. 
   
  Lemma choice_mono_right: forall {A: Type} (c1: program Σ A),
    mono (fun c2 => choice c1 c2).
  Proof.
    unfold mono. 
    intros.
    hnf.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma choice_continuous_right: forall {A: Type} (c1: program Σ A),
    continuous (fun c2 => choice c1 c2).
  Proof.
    unfold  continuous,sseq_continuous, sseq_mono,choice.
    intros. 
    sets_unfold.
    intros σ a σ'.
    split.
    + intros [? | [? ?] ].
      - exists O.
        auto.
      - exists x; auto.
    + intros [? [? | ?] ].
      - auto.
      - eauto.
  Qed.

  Lemma choice_mono_compose_right: forall {A B: Type} (c1: program Σ A) (f: program Σ B -> program Σ A),
    mono f ->
    mono (fun c2 => choice c1 (f c2)).
  Proof.
    unfold mono, choice.
    intros.
    hnf. hnf in H.
    intros.
    apply H in H0.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma choice_continuous_compose_right: forall {A B: Type} (c1: program Σ A) (f: program Σ B -> program Σ A),
    continuous f ->
    continuous (fun c2 => choice c1 (f c2)).
  Proof.
    unfold continuous, sseq_continuous, sseq_mono,choice.
    intros.
    apply H in H0.
    rewrite H0.
    sets_unfold.
    intros σ a σ'.
    split.
    + intros [? | [? ?] ].
      - exists O.
        auto.
      - exists x; auto.
    + intros [? [? | ?] ].
      - auto.
      - eauto.
  Qed.

  Lemma choice_omega_union_distr_l:
  forall
    {A: Type}
    (c1: program Σ A)
    (c2: nat -> program Σ A),
    choice c1 (⋃ c2) == ⋃ (fun n => choice c1 (c2 n)).
  Proof.
    intros.
    unfold choice.
    sets_unfold.
    intros.
    split; intros.
    + destruct H as [? | [? ?]].
      * exists 0. auto.
      * exists x. auto.
    + destruct H as [n [? | ?]].
      * tauto.
      * right. exists n. auto.
  Qed.

End mono_and_continuous_lemmas.

Section  while_monad.

  Context {Σ: Type}.
  Import MonadNotation.
  Local Open Scope stmonad.

  Definition while_f (cond:  (program Σ bool))  (body : (program Σ unit)) 
                     (W :  Σ -> unit -> Σ -> Prop) 
                        : Σ -> unit -> Σ -> Prop :=
  (x <- cond ;; (match x with 
  | true =>  seq body (fun (s': Σ ) => W s') 
  | false => M_to_program (ret tt)
  end)).
  
 (* program Σ bool *) (* program Σ unit *)
  Definition while (cond: (program Σ bool)) (body : program Σ unit)  := Lfix (while_f cond body).

  Definition whileret_f {A: Type}  (cond: A -> (program Σ bool)) (body : A -> (program Σ A)) 
                     (W :  A -> program Σ A) 
                        : A -> program Σ A :=
  fun a => (x <- (cond a) ;; match x with 
  | true =>  bind (body a) W
  | false => M_to_program (ret a)
  end).

  Definition whileret {A: Type}  (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  := Lfix (whileret_f cond body).

  Definition whilebreak_f {A B: Type} (body: A -> program Σ (A + B)) (W: A -> program Σ B): A -> program Σ B :=
    fun a =>
      x <- body a;;
      match x with
      | inl a' => W a'
      | inr b => return b
      end.

  Definition whilebreak {A B: Type} (body: A -> program Σ (A + B)): A -> program Σ B :=
    Lfix (whilebreak_f body).

  Definition Repeat_f  (body : (program Σ unit)) 
                      (W :  Σ -> unit -> Σ -> Prop) 
                          : Σ -> unit -> Σ -> Prop :=
    W ;; body.

  Definition Repeat (body : (program Σ unit))  := Lfix (Repeat_f body).

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
    unfold mono. hnf. intros.
    unfold while_f.
    intros.
    sets_unfold.
    unfold seq, bind.
    intros.
    destruct H0 as (b & x0 & ? & H0).
    exists b, x0.
    split;auto.
    destruct (b).
    - 
      destruct H0 as (? & ? & ? & ?).
      do 2 eexists.
      split;eauto.
      apply H;auto.
    - auto.
  Qed.

  Lemma whilef_continuous:
    forall cond body,
    continuous (fun x => while_f cond body x).
  Proof.
    intros.
    unfold continuous, sseq_continuous, sseq_mono.
    intros.
    unfold while_f.
    unfold seq,bind.
    sets_unfold.
    intros a c. split; intros.
    + destruct H0 as (b & x0 & ? & H0).
      destruct b.
      - destruct H0 as [t [x1 [? [n ?] ] ]].
        exists  n, true, x0.
        split; auto.
        exists t, x1.
        split; auto.
      - exists O, false, x0. 
        split;eauto.
    + destruct H0 as [n [b [x0 [? H0] ] ]].
      exists b, x0.
      split;auto.
      destruct b.
      - destruct H0 as [t [x1 [? ?] ] ].
        exists t, x1. split.
        * auto.
        * exists n. auto.
      - auto. 
  Qed.

  Lemma whileretf_mono:
    forall {A: Type}  cond (body : A -> (program Σ A)),
    mono (fun x => whileret_f cond body x).
  Proof.
    intros.
    unfold mono. hnf. 
    unfold whileret_f.
    intros a x.
    sets_unfold.
    unfold seq, bind.
    intros.
    destruct H0 as (b & x0 & ? & H0).
    exists b, x0.
    split;auto.
    destruct (b).
    - 
      destruct H0 as (? & ? & ? & ?).
      do 2 eexists.
      split;eauto.
    - auto.
  Qed.

  Lemma whileretf_continuous:
    forall {A: Type}  cond (body : A -> (program Σ A)),
    continuous (fun x => whileret_f cond body x).
  Proof.
    intros.
    unfold continuous, sseq_continuous, sseq_mono.
    intros l H a x.
    unfold whileret_f.
    unfold seq,bind.
    sets_unfold.
    intros a' x'.
    split; intros.
    + destruct H0 as (b & x0 & ? & H0).
      destruct b.
      - destruct H0 as [t [x1 [? [n ?] ] ]].
        exists  n, true, x0.
        split; auto.
        exists t, x1.
        split; auto.
      - exists O, false, x0. 
        split;eauto.
    + destruct H0 as [n [b [x0 [? H0] ] ]].
      exists b, x0.
      split;auto.
      destruct b.
      - destruct H0 as [t [x1 [? ?] ] ].
        exists t, x1. split.
        * auto.
        * exists n. auto.
      - auto. 
  Qed.

  Lemma whilebreak_f_mono:
    forall {A B} (body: A -> program Σ (A + B)),
      mono (whilebreak_f body).
  Proof.
    intros.
    unfold mono. hnf. intros D1 D2 ?.
    unfold whilebreak_f.
    sets_unfold.
    unfold seq, bind.
    intros a sigma b sigma'.
    intros [ c0 [sigma0 [? ?]]].
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
    unfold continuous, sseq_continuous, sseq_mono.
    intros.
    sets_unfold.
    unfold whilebreak_f.
    unfold seq,bind.
    intros a sigma b sigma'.
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
  Qed.

  Lemma Repeatf_mono:
    forall body,
    mono (fun x => Repeat_f body x).
  Proof.
    intros.
    unfold mono. hnf. intros.
    unfold Repeat_f.
    intros.
    sets_unfold.
    unfold seq, bind.
    intros.
    destruct H0 as (b & x0 & ? & H0).
    exists b, x0.
    split;auto.
    apply H;auto.
  Qed.

  Lemma Repeatf_continuous:
    forall body,
    continuous (fun x => Repeat_f body x).
  Proof.
    intros.
    unfold continuous, sseq_continuous, sseq_mono.
    intros.
    unfold Repeat_f.
    unfold seq,bind.
    sets_unfold.
    intros a c. split; intros.
    + destruct H0 as (b & x0 & ? & ?).
      destruct H0 as  [n ?].
      exists  n, b,  x0.
      split; auto.
    + destruct H0 as [n [b [x0 [? H0] ] ]].
      exists b, x0.
      split;auto.
      exists n. auto.
  Qed.

End  while_monad.

Section monad_equiv_lemmas.

  Context {Σ: Type}.
  Import MonadNotation.
  Local Open Scope stmonad.

  Lemma bind_equiv {A B: Type}: forall (c1 c1': program Σ A) (c2 c2': A -> program Σ B), 
    c1 == c1' -> c2 == c2'  ->
    bind c1 c2  == bind c1' c2'.
  Proof.
    intros.
    split; intros.
    + destruct H1 as (? & ? & ? & ?).
      do 2 eexists.
      split.
      apply H;eauto.
      apply H0;eauto.
    + destruct H1 as (? & ? & ? & ?).
      do 2 eexists.
      split.
      apply H;eauto.
      apply H0;eauto.
  Qed.


  Lemma bindpat_equiv {A B: Type}: forall (c1 c1': program Σ A) (c2 c2': A -> program Σ B), 
    c1 == c1' -> c2 == c2'  ->
    ' pat <- c1 ;; (c2 pat) == ' pat <- c1' ;; (c2' pat).
  Proof.
    intros.
    apply bind_equiv. auto.
    auto.
  Qed.


  Lemma bind_mcompose {A B C: Type}: forall (c1 : program Σ A) (c2: A -> program Σ B) (c3: B -> program Σ C), 
    bind (bind c1 c2) c3  == bind c1 (mcompose c2 c3).
  Proof.
    intros.
    split; intros.
    + destruct H as (? & ? & ? & ?).
      destruct H as (? & ? & ? & ?).
      do 2 eexists.
      split;eauto.
      do 2 eexists.
      split;eauto.
    + destruct H as (? & ? & ? & ?).
      destruct H0 as (? & ? & ? & ?).
      do 2 eexists.
      split;eauto.
      do 2 eexists.
      split;eauto.
  Qed.

  Lemma mcompose_assoc {A B C D: Type}: 
    forall (c1 : A -> program Σ B) (c2: B -> program Σ C) (c3: C -> program Σ D), 
    mcompose (mcompose c1 c2) c3 == mcompose c1 (mcompose c2 c3).
  Proof.
    intros.
    split; intros.
    + destruct H as (? & ? & ? & ?).
      destruct H as (? & ? & ? & ?).
      do 2 eexists.
      split;eauto.
      do 2 eexists.
      split;eauto.
    + destruct H as (? & ? & ? & ?).
      destruct H0 as (? & ? & ? & ?).
      do 2 eexists.
      split;eauto.
      do 2 eexists.
      split;eauto.
  Qed.

  (* Lemma bind_mcompose2 {A B C: Type}: forall (c1 : program Σ A) (c2: A -> program Σ B) (c3: B -> program Σ C), 
     bind c1 (bind c2 c3) == ?.
  Proof. *)

  Lemma while_unfold: forall (cond: (program Σ bool)) (body : program Σ unit), 
    while cond body == (x <- cond ;; 
                      (if x then  body;; while cond body
                       else return tt)).
  Proof.
    intros.
    unfold while.
    apply (Lfix_fixpoint (while_f cond body)).
    + apply whilef_mono.
    + apply whilef_continuous.
  Qed.


  Lemma whileret_unfold: forall {A: Type} (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  (a: A), 
    whileret cond body a == (x <- (cond a);; 
                            if x then y <- body a ;; whileret cond body y
                                else return a).
  Proof.
    intros A cond body.
    assert (whileret cond body == (fun a => (x <- (cond a);; 
    if x then y <- body a ;; whileret cond body y
        else return a))).
    { unfold whileret.
    apply (Lfix_fixpoint (whileret_f cond body)).
    + apply whileretf_mono.
    + apply whileretf_continuous. }
    apply H.
  Qed.

  Lemma whilebreak_unfold:
    forall {A B} (body: A -> program Σ (A + B)),
    whilebreak body == fun a =>
                         x <- body a;; 
                         match x with
                         | inl a0 => whilebreak body a0
                         | inr b0 => return b0
                         end.
  Proof.
    intros.
    unfold whilebreak.
    apply (Lfix_fixpoint (whilebreak_f body)).
    + apply whilebreak_f_mono.
    + apply whilebreak_f_continuous.
  Qed.

  Lemma bind_ID_left : forall {A B : Type} (m : A -> program Σ B),
    Id >=> m == m.
  Proof.
    intros.
    unfold Id.
    intros a.
    sets_unfold.
    intros s b s'.
    unfold mcompose, bind, ret, M_to_program .
    split;intros.
    destruct H as (? & ? & ? & ?).
    destruct H. subst. auto.
    do 2 eexists. eauto.
  Qed.

  Lemma bind_ID_right  : forall {A : Type} (m : program Σ A),
    x <- m ;; Id x == m.
  Proof.
    intros.
    unfold Id.
    sets_unfold.
    intros s a s'.
    unfold  bind, ret, M_to_program .
    split;intros.
    destruct H as (? & ? & ? & ?).
    destruct H0. subst. auto.
    do 2 eexists. eauto.
  Qed.


End monad_equiv_lemmas.

Section Program_trans.
  Context {Σ₁ Σ₂: Type}.

  Definition programcall  {A : Type} (f: Σ₁ -> Σ₂) (g : Σ₂ -> Σ₁) 
                          (c: program Σ₂ A) : program Σ₁ A :=
    fun s1 a s2 => exists s0, c (f s1) a s0 /\ s2 = (g s0).
  
End Program_trans.



#[export] Instance programbind_Proper
  {Σ: Type} {A B: Type}:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv ) (@bind Σ A B).
Proof.
  unfold Proper, respectful.
  intros.
  apply bind_equiv; auto.
Qed.


#[export] Instance programbindpat_Proper
  {Σ: Type}  {A B: Type}:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv )  (fun c1 c2 => (@bind Σ A B  c1 (fun x => match x with pat => c2 end))).
Proof.
  unfold Proper, respectful.
  intros.
  apply bindpat_equiv; auto.
  sets_unfold. intros.
  apply H0.
Qed.

#[export] Instance programbind_included_Proper
  {Σ: Type} {A B: Type}:
  Proper (Sets.included ==> Sets.included  ==> Sets.included ) (@bind Σ A B).
Proof.
  unfold Proper, respectful.
  intros.
  unfold bind.
  sets_unfold.
  sets_unfold in H. sets_unfold in H0.
  intros s b s0.
  intros.
  destruct H1 as (a & s1 & ? & ?).
  exists a, s1.
  split;intuition auto.
Qed.

Definition ATrue {Σ: Type} : Σ -> Prop := fun _ => True.
