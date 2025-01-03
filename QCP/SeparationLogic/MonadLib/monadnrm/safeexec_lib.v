Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From SetsClass Require Import SetsClass.
From StateMonad.monadnrm Require Import monadbasic.

Import SetsNotation.
Local Open Scope sets.

Definition safe {Σ: Type} {A: Type} (σ : Σ) (c:  program Σ A) (X : A -> Σ -> Prop) := 
    forall r σ', c σ r σ' -> (r, σ') ∈ X.  

Definition safeExec {Σ: Type} {A: Type} (P: Σ -> Prop) (c: program Σ A) (X: A -> Σ -> Prop) :=
  exists σₕ, P σₕ /\ safe σₕ c X.


Definition hs_eval {Σ: Type}  {A: Type} (c : program Σ A) (P : Σ -> Prop) (P' : (Σ -> Prop)) (a : A) := 
  forall (σₕ : Σ), P σₕ -> exists (σₕ' : Σ), c σₕ a σₕ' /\ P' σₕ'.

(* ⥅  rightarrowplus *)
Notation " P '-@' s '-⥅' P' '♯' a " := (hs_eval s P P' a) (at level 70, no associativity).

Notation " P '-@' s '-→' P' " := (exists a,  hs_eval s P P' a) (at level 70, no associativity).


Import MonadNotation.
Local Open Scope stmonad.
(**********************************************************************************)
(*    safe exec  rules                                                            *)
(**********************************************************************************)
Ltac splits :=
  match goal with 
  | |- _ /\ _ => split;splits
  | |- _ => idtac end.

Local Ltac my_destruct Σ H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σ => let σ := fresh "σₕ" in destruct H as [σ H];my_destruct Σ H
              | program Σ ?A => let c := fresh "c" in destruct H as [c H];my_destruct Σ H
              | _ => destruct H as [? H];my_destruct Σ H
              end
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              my_destruct Σ H;
              my_destruct Σ H0
  | _ \/ _ => destruct H as [H | H];
              my_destruct Σ H
  | _ => (discriminate || contradiction  || idtac)
  end.

Section  safeexec_rules.
  Context {Σ: Type}.

  Definition asrt : Type :=  Σ -> Prop.

  Ltac destructs H := my_destruct Σ H.

  (* ⟨ True ⟩  x = choice {0,1} ; y = x + choice {0, 1} ≾  x <- choice {0, 1}; y <- x + choice {0, 1}; store (x,y) ⟨ xₗ = ret.1 /\ yₗ = ret.2 ⟩

  { [| safeExec True (x <- choice {0, 1}; y <- x + choice {0, 1}; store (x,y)) X |]   }
  x = choice {0,1} ; y = x + choice {0, 1}

  { (x = 0 \/ x = 1) && (y = x + 0 \/ y = x + 1)  /\ [| safeExec True (x <- choice {0, 1}; y <- x + choice {0, 1}; store (x,y)) X |]   }
 
  { (x = 0 ) && (y = x + 0 \/ y = x + 1)  /\ [| safeExec True (x <- choice {0, 1}; y <- x + choice {0, 1}; store (x,y))) X |]   \/
    (x = 1) && (y = x + 0 \/ y = x + 1)  /\ [| safeExec True (x <- choice {0, 1}; y <- x + choice {0, 1}; store (x,y)) X |]   }

  hs_eval' (x <- choice {0, 1}) True ((fun _ => True) 0) 0

   { (x = 0 ) && (y = x + 0 \/ y = x + 1)  /\ [| safeExec True (y <- 0 + choice {0, 1}; store (0,y)) X |]   \/
    (x = 1) && (y = x + 0 \/ y = x + 1)  /\ [| safeExec True (x <- choice {0, 1}; y = x + choice {0, 1}) X |]   }


  {∃ x' y'. x = x'  /\ y = y'  /\  [| safeExec (x' = x /\ y' = y) (return tt) X |]  } *)

  Lemma return_eq : forall {A : Type} (s: Σ) s0 (a a0: A),
    (return a) s a0 s0 <-> s0 = s /\ a0 = a.
  Proof.
    unfold M_to_program, ret. tauto.
  Qed.


  Lemma highstependret_derive : forall  {A : Type} (c1: program Σ A)  (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P' a) ♯ a ->
  (forall X, safeExec P (c1) X ->  safeExec (P' a) (return a) X).
  Proof.
    intros.
    unfold hs_eval, safeExec, safe in *.
    destructs H0. 
    simpl in *.
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    intros.
    unfold M_to_program,ret in H3.
    destruct H3;subst.
    eapply H1;eauto.
  Qed.


  Lemma highstepend_derive : forall  (c1: program Σ unit)  (P  : Σ -> Prop) P',
  P -@ c1 -→ P' ->
  (forall X, safeExec P (c1) X ->  safeExec P' (return tt) X).
  Proof.
    intros.
    destruct H.
    destruct x.
    pose proof (highstependret_derive c1  P tt ((fun _ => P')) H).
    eapply H1;eauto.
  Qed.

  
  Lemma highstepbind_derive : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P' a) ♯ a ->
  (forall X, safeExec P (x <- c1;; c2 x) X ->  safeExec (P' a) (c2 a) X).
  Proof.
    intros.
    unfold hs_eval, safeExec, safe in *.
    destructs H0. 
    simpl in *.
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    intros.
    unfold bind in H1.
    eapply H1;eauto.
  Qed.

  Lemma highstepseq_derive : forall  {A B: Type} (c1: program Σ A) (c2:  program Σ B) (P P': Σ -> Prop),
    P -@ c1 -→ P'  ->
    (forall X, safeExec P (c1 ;; c2) X ->  safeExec P' c2 X).
  Proof.
    intros.
    destruct H.
    unfold seq in H0.
    pose proof (highstepbind_derive c1 (fun _ => c2) P x ((fun (_ : A) => P')) H).
    eapply H1;eauto.
  Qed. 


  Lemma highret_eval1 : forall {A: Type}  (P  : Σ -> Prop) (a: A), 
    P -@ (return a) -→ P.
  Proof.
    intros. cbv. intros.
    eexists. splits;eauto.
  Qed.

  Lemma highret_eval2 : forall {A: Type}  (P  : Σ -> Prop) (a: A), 
    P -@ (return a) -⥅ P ♯ a.
  Proof.
    intros. cbv. intros.
    eexists. splits;eauto.
  Qed.

  Lemma hsevalbind_derive : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) P' a Q b,
  P -@ c1 -⥅ (P' a) ♯ a ->  (P' a) -@ (c2 a) -⥅ (Q b) ♯ b ->
  P -@ (x  <- c1 ;; c2 x) -⥅ (Q b) ♯ b.
  Proof.
    unfold hs_eval. intros.
    specialize (H _ H1).
    destructs H.
    specialize (H0 _ H2).
    destructs H0.
    eexists.
    splits;eauto.
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma hsevalbind_derive' : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) P' a Q b,
  P -@ c1 -⥅ P' ♯ a ->  P' -@ (c2 a) -⥅ Q ♯ b ->
  P -@ (x  <- c1 ;; c2 x) -⥅ Q ♯ b.
  Proof.
    unfold hs_eval. intros.
    specialize (H _ H1).
    destructs H.
    specialize (H0 _ H2).
    destructs H0.
    eexists.
    splits;eauto.
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma hsevalchoice_left_derive:
    forall {A: Type} (c1 c2: program Σ A) (P  : Σ -> Prop) Q a,
      P -@ c1 -⥅ Q ♯ a ->
      P -@ (choice c1 c2) -⥅ Q ♯ a.
  Proof.
    intros.
    unfold hs_eval.
    intros.
    specialize (H _ H0) as [? [? ?]].
    eexists.
    split; [left; apply H | apply H1].
  Qed.

  Lemma hsevalchoice_right_derive:
    forall {A: Type} (c1 c2: program Σ A) (P: Σ -> Prop) Q a,
      P -@ c2 -⥅ Q ♯ a ->
      P -@ (choice c1 c2) -⥅ Q ♯ a.
  Proof.
    intros.
    unfold hs_eval.
    intros.
    specialize (H _ H0) as [? [? ?]].
    eexists.
    split; [right; apply H | apply H1].
  Qed.

  Lemma hsevaltest_derive:
    forall (P: Σ -> Prop) (Q: Prop) a,
      Q -> P -@ (test Q) -⥅ P ♯ a.
  Proof.
    intros.
    unfold hs_eval, test.
    intros.
    eauto.
  Qed.

  Lemma safeExec_ex : forall {A B: Type} (P: A -> Σ -> Prop) (c:  program Σ B) X,
  (exists a, safeExec (P a) (c) X) <->  safeExec (fun σ => exists a, P a σ) (c) X.
  Proof.
    unfold safeExec;intros;split;intros.
    - destruct H as (? & ? & ? & ?).
      eexists.
      split;eauto.
    - destruct H as (? & (? & ?) & ?).
      do 2 eexists.
      split;eauto.
  Qed. 


  Lemma safeExec_prorefine: forall {A : Type} (c1 c2: program Σ A)  (P  : Σ -> Prop) X,
  c2 ⊆ c1 ->
  safeExec P c1 X -> safeExec P c2 X.
  Proof.
    unfold safeExec. intros.
    destructs H0.
    eexists.
    split;eauto.
    unfold safe in *.
    intros.
    sets_unfold in H.
    eapply H1;eauto.
  Qed.


  Lemma safeExec_proequiv: forall {A : Type} (c1 c2: program Σ A)  (P  : Σ -> Prop) X,
  c1 == c2 ->
  safeExec P c1 X -> safeExec P c2 X.
  Proof.
    unfold safeExec. intros.
    destructs H0.
    eexists.
    split;eauto.
    unfold safe in *.
    intros.
    sets_unfold in H.
    eapply H1;eauto.
    eapply H;eauto.
  Qed.

  Lemma hs_eval_proequiv: forall {A : Type} (c1 c2: program Σ A)  (P  Q: Σ -> Prop) a,
  c1 == c2 ->
  P -@ c1 -⥅ Q ♯ a ->
  P -@ c2 -⥅ Q ♯ a.
  Proof.
    unfold hs_eval. intros.
    specialize (H0 _ H1).
    destructs H0.
    eexists.
    split;eauto.
    eapply H;eauto.
  Qed.

  Lemma safeExec_bind : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) ,
    forall X, safeExec P (x <- c1 ;; c2 x) X ->
    exists X', safeExec P c1 X' /\
    (forall P' a, safeExec (P' a)  (return a) X' -> 
              safeExec (P' a) (c2 a) X).
  Proof.
    intros.
    unfold safeExec in H.
    destructs H.
    unfold safe in H0.
    exists (fun (r : A) (x : Σ) => c1 σₕ r x).
    unfold safeExec.
    splits;eauto.
    { eexists.
      split;eauto.
      unfold safe.
      intros. auto.
    }
    intros.
    destructs H1.
    eexists.
    split;eauto.
    unfold safe, M_to_program, ret in H2.
    specialize (H2 a σₕ0  (ltac:(auto))).
    unfold safe.
    intros.
    eapply H0.
    do 2 eexists.
    split;eauto.
    exact H2.
  Qed. 


  Lemma safeExec_bind' : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) P',
    (forall X, safeExec P c1 X -> exists a, safeExec (P' a)  (return a) X) ->
    (forall X, safeExec P (x <- c1 ;; c2 x) X -> exists a, safeExec (P' a) (c2 a) X).
  Proof.
    intros.
    unfold safeExec in H0.
    destructs H0.
    unfold safe in H1.
    specialize (H (fun r x => c1 σₕ r x)).
    assert (safeExec P c1 (fun (r : A) (x : Σ) => c1 σₕ r x)).
    { unfold safeExec.
      eexists.
      split;eauto.
      unfold safe.
      intros.
      eauto. 
    }
    specialize (H H2). clear H2.
    destruct H as (a & σₕ' & ? & H).
    exists a.
    unfold safeExec.
    eexists.
    split;eauto.
    unfold safe, M_to_program, ret in H.
    specialize (H a σₕ' (ltac:(auto))).
    sets_unfold in H.
    unfold safe.
    intros.
    eapply H1.
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma safeExec_choice_left: forall {A: Type} (c1 c2: program Σ A) P X,
    safeExec P (choice c1 c2) X ->
    safeExec P c1 X.
  Proof.
    unfold safeExec, choice, safe.
    intros.
    destruct H as [σ [? ?]].
    exists σ.
    split; [tauto |].
    intros.
    specialize (H0 r σ' ltac:(left; tauto)).
    tauto.
  Qed.

  Lemma safeExec_choice_right: forall {A: Type} (c1 c2: program Σ A) P X,
    safeExec P (choice c1 c2) X ->
    safeExec P c2 X.
  Proof.
    unfold safeExec, choice, safe.
    intros.
    destruct H as [σ [? ?]].
    exists σ.
    split; [tauto |].
    intros.
    specialize (H0 r σ' ltac:(right; tauto)).
    tauto.
  Qed.

  Lemma safeExec_test_bind: forall {A: Type} (Q: Prop) (c: program Σ A) P X,
    Q ->
    safeExec P (test Q;; c) X ->
    safeExec P c X.
  Proof.
    unfold safeExec, test, safe, seq, bind.
    intros.
    destruct H0 as [σ [? ?]].
    exists σ.
    split; [tauto |].
    intros.
    apply (H1 r σ'); clear H0.
    exists tt, σ.
    tauto.
  Qed.

  Lemma safeExec_bind_rightsubst : forall {A B: Type} (c1: program Σ A) (c2 c2': A -> program Σ B) (P : Σ -> Prop) X X',
    (forall σ a, safe σ (c2 a) X -> safe σ (c2' a) X') ->
    (safeExec P (x <- c1 ;; c2 x) X -> safeExec P (x <- c1 ;; c2' x) X').
  Proof.
    unfold safeExec,safe.
    intros.
    destructs H0.
    eexists.
    split;eauto.
    intros.
    destruct H2 as (a  & σ'' & ? & ?).
    eapply H;eauto.
    intros.
    eapply H1.
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma safeExec_subst : forall {A: Type} (c1 c1': program Σ A)  (P : Σ -> Prop) X X',
    (forall σ, safe σ c1 X -> safe σ c1' X') ->
    (safeExec P (c1) X -> safeExec P (c1') X').
  Proof.
    unfold safeExec,safe.
    intros.
    destructs H0.
    eexists.
    split;eauto.
  Qed.

  Lemma safeExec_monad_Atrue_finnal: forall  {A: Type} (m: MONAD A) ,
    safeExec ATrue m (fun r x => m tt r x).
  Proof.
    intros.
    unfold safeExec, ATrue, safe.
    exists tt.
    splits;auto.
  Qed.

  Lemma safeExec_return_Atrue_finnal: forall  {A: Type}  (m: program Σ A) (l : A) (σ: Σ) ,
    safeExec ATrue (return l) (fun r x => m σ r x) ->
    exists σ', m σ l σ'.
  Proof.
    unfold safeExec,safe, ret, M_to_program.
    intros.
    destructs H.
    specialize (H0 l σₕ (ltac:(auto))).
    exists σₕ.
    auto.
  Qed.

  Lemma safeExec_choice_l {A: Type}:
    forall (c0 c1: program Σ A) X (s: Σ -> Prop),
      safeExec s (choice c0 c1) X -> safeExec s c0 X.
  Proof.
    intros.
    destruct H as [? [? ?]].
    unfold safe in *.
    unfold choice in H0; simpl in H0.
    exists x; split; auto.
    simpl; sets_unfold.
    unfold safe.
    sets_unfold in H0.
    intros; specialize (H0 r σ').
    tauto.
  Qed.
  
  (* same as choice_l *)
  Lemma safeExec_choice_r {A: Type}:
    forall (c0 c1: program Σ A) X (s: Σ -> Prop),
      safeExec s (choice c0 c1) X -> safeExec s c1 X.
  Proof.
    intros.
    destruct H as [? [? ?]].
    unfold safe in *.
    unfold choice in H0; simpl in H0.
    exists x; split; auto.
    simpl;  sets_unfold.
    sets_unfold in H0.
    unfold safe.
    intros; specialize (H0 r σ').
    tauto.
  Qed.

  Lemma safeExec_test {A: Type}:
    forall (s: Σ -> Prop) (P: Prop) (c: program Σ A) X,
      P ->
      safeExec s (test P;; c) X ->
      safeExec s c X.
  Proof.
    intros; unfold safeExec in *.
    destructs H0.
    exists σₕ.
    split; auto.
    unfold safe in *.
    intros.
    specialize (H1 r σ').
    unfold test in H1; simpl in H1.
    sets_unfold in H1.
    apply H1.
    exists tt; exists σₕ; tauto.
  Qed.

  Lemma hseval_stateless_ret: forall  {A: Type}  (m: MONAD A) (a : A),
    m tt a tt ->
    ATrue -@ m -⥅ ATrue ♯ a.
  Proof.
    intros. hnf. 
    exists tt.
    destruct σₕ.
    easy.
  Qed.

End  safeexec_rules.

#[export] Instance safeExec_programrefine_impl_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.included ==> eq ==> (Basics.flip Basics.impl)) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros. subst y0.
  hnf.
  apply safeExec_prorefine;eauto.
Qed.

#[export] Instance safeExec_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.equiv ==> eq ==>  iff) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros. subst y0. split. 
  apply safeExec_proequiv. auto.
  apply safeExec_proequiv. symmetry. auto.
Qed.

#[export] Instance safeExec_programequiv_iff_Proper'
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.equiv ==> eq ==>  iff) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros. subst y0. split. 
  apply safeExec_proequiv. auto.
  apply safeExec_proequiv. symmetry. auto.
Qed.

#[export] Instance hseval_programequiv_Proper
  {Σ: Type} {A: Type}:
  Proper (Sets.equiv ==> eq ==> eq ==> eq ==> iff ) (@hs_eval Σ A).
Proof.
  unfold Proper, respectful.
  intros. subst y0 y1 y2. split.
  apply hs_eval_proequiv. auto.
  apply hs_eval_proequiv. symmetry. auto.
Qed.

#[export] Instance hseval_programequiv_Proper'
  {Σ: Type} {A: Type}:
  Proper (Sets.equiv ==> eq ==> eq ==> eq ==> iff ) (@hs_eval Σ A).
Proof.
  unfold Proper, respectful.
  intros. subst y0 y1 y2. split.
  apply hs_eval_proequiv. auto.
  apply hs_eval_proequiv. symmetry. auto.
Qed.

Lemma  program_para_equiv {Σ: Type} {A B: Type}: forall 
  (f1 f2: A -> program Σ B),
  f1 == f2 -> forall x, f1 x == f2 x.
Proof.
  intros.
  apply H.
Qed.

Arguments program_para_equiv {Σ} {A B}%type_scope [f1] [f2].

Ltac __prove_by_one_abs_step x :=
  match goal with
  | H: safeExec ?P1 (bind ?c11 ?c12) ?X |- safeExec ?P2 ?c2 ?X =>
      unify (c12 x) c2; 
      refine (highstepbind_derive _ _ _ x (fun _ => ATrue) _ X H);
      clear H
  end.

Tactic Notation "prove_by_one_abs_step" uconstr(x) :=
  __prove_by_one_abs_step x.

Ltac abs_choice_left :=
  apply hsevalchoice_left_derive.

Ltac abs_choice_right :=
  apply hsevalchoice_right_derive.

Ltac abs_test_step :=
  match goal with
  | |- hs_eval (test _) _ _ _ => apply hsevaltest_derive
  | |- hs_eval (bind (test _) _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltest_derive | ]
  | |- hs_eval (seq (test _) _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltest_derive | ]
  end.

Ltac abs_return_step :=
  apply highret_eval2.

Ltac safe_step H :=
  match type of H with
  | safeExec _ (seq (test _ ) _) _ => apply safeExec_test in H; [try safe_step H | auto]
  end.

Ltac safe_choice_l H :=
  apply safeExec_choice_l in H; try safe_step H.

Ltac safe_choice_r H :=
  apply safeExec_choice_r in H; try safe_step H.

Ltac safe_equiv :=
  eapply safeExec_proequiv; eauto.  

