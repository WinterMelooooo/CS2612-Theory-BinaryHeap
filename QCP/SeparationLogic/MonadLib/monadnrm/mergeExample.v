Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SetsClass Require Import SetsClass.
From FP Require Import SetsFixedpoints.
From StateMonad.monadnrm Require Import monadbasic safeexec_lib.


Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Export MonadNotation.
Local Open Scope stmonad.




Section  merge_monad.

Definition merge_body:
  list Z * list Z * list Z ->
  MONAD (list Z * list Z * list Z + list Z) :=
  fun '(l1, l2, l3) =>
    match l1, l2 with 
    | nil, _ => return (inr (l3 ++ l2))
    | _, nil => return (inr (l3 ++ l1))
    | x :: l1', y :: l2' =>
        choice
          (test (x <= y);; return (inl (l1', l2, l3 ++ x :: nil)))
          (test (y <= x);; return (inl (l1, l2', l3 ++ y :: nil)))
  end.

  Definition merge_rel l l0 :=
    whilebreak merge_body (l, l0, nil).

  Definition merge_from_mid_rel l1 l2 l3 := 
    whilebreak merge_body (l1, l2, l3).

End  merge_monad.


Section split_rec_rel_monad.

  Definition reversepair : ((list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) :=
    fun '(p,q) => return (q,p).

  Definition split_rec_rel_f  (W : ((list Z) * (list Z) * (list Z)) ->  MONAD ((list Z) * (list Z))) 
                          : ((list Z) * (list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) :=
    fun '(x, p, q) => match x with 
                      | nil => return (p, q)
                      | xh :: x' => x <- W (x', q,  xh::p) ;;
                                    reversepair x
                      end.

  Definition split_rec_rel' : ((list Z) * (list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) := 
    Lfix split_rec_rel_f.

  Definition split_rec_rel l1 l2 l3: MONAD ((list Z) * (list Z)) := 
    split_rec_rel' (l1, l2, l3).

  Definition split_rel x :=
    split_rec_rel' (x, nil, nil).


  Lemma mono_split_rec_rel_f: mono split_rec_rel_f.
  Proof.
    intros.
    unfold split_rec_rel_f.
    unfold mono. hnf.
    intros f1 f2 H x s1.
    destruct x as ((x & p) & q).
    destruct x.
    reflexivity.
    assert ('(p, q) <- f1 (x, q, z :: p) ;; return (q, p) ⊆ '(p, q) <- f2 (x, q, z :: p) ;; return (q, p)).
    { erewrite (H _). reflexivity. } 
    apply H0.
  Qed.
  
  Lemma continuous_split_rec_rel_f: continuous split_rec_rel_f.
  Proof.
    intros.
    unfold split_rec_rel_f.
    unfold continuous, sseq_continuous, sseq_mono.
    intros l Hl.
    sets_unfold.
    intros x s x0 s0.
    destruct x as ((x & p) & q).
    split;intros.
    + destruct x. exists O. auto.
      destruct H as (x1 & s1 & (n & H) & ?).
      do 3 eexists.
      split;eauto.
    + destruct H as (n & H).
      destruct x;auto.
      destruct H as (x1 & s1 & ? & ?).
      do 2 eexists.
      split;eauto.
  Qed.



  Lemma split_rec_rel_unfold: split_rec_rel' == split_rec_rel_f split_rec_rel'.
  Proof.
    intros.
    apply Lfix_fixpoint.
    apply mono_split_rec_rel_f.
    apply continuous_split_rec_rel_f.
  Qed. 


  Lemma split_rec_rel_eval_xnil: forall p q P, 
    P -@ (split_rec_rel' (nil, p, q)) -⥅ 
    P ♯ (p, q).
  Proof.
    intros.
    erewrite (program_para_equiv (split_rec_rel_unfold)).
    unfold split_rec_rel_f.
    apply  highret_eval2.
  Qed.


  Lemma split_rel_eval_xnotnil: forall z x p q,
    forall P X, safeExec P (split_rec_rel' (z::x, p, q)) X ->
                safeExec P (x <- split_rec_rel' (x, q, z::p) ;; reversepair x ) X.
  Proof. 
    unfold split_rel, reversepair. intros.
    erewrite (program_para_equiv (split_rec_rel_unfold)) in H.
    unfold split_rec_rel_f in H.
    apply H.
  Qed.

  Lemma bind_2_reversepair_equiv_Id: 
    (fun p => z <- reversepair p ;; reversepair z) == Id.
  Proof.
    intros [x y].
    unfold reversepair;sets_unfold.
    intros s [u v] s'.
    split;intros.
    - destruct H as ([x' y'] & s'' & ? & ? ).
      apply return_eq with (a:= (y, x)) in H as [? ?].
      apply return_eq with (a:= (y',x')) in H0 as [? ?].
      inversion H1; inversion H2. subst.
      apply return_eq. auto.
    - apply return_eq with (a:= (x, y)) in H as [? ?].
      inversion H0;subst.
      do 3 eexists.
      split;eauto.
      cbn. apply return_eq. auto.
  Qed.

End split_rec_rel_monad.


Section mergesort_monad.
  Definition mergesortrec_f  (W :  (list Z) -> MONAD (list Z) ) 
                        : ((list Z) -> MONAD (list Z)) :=
    fun x => '(p1, q1) <- split_rel x ;; 
                      match q1 with 
                      | nil => return p1
                      | _ :: _  =>  p2 <- W (p1) ;; 
                                    q2 <- W (q1) ;; 
                                    merge_rel p2 q2
                      end.

  Definition mergesortrec := Lfix (mergesortrec_f).

  Definition mergesortrec_loc0: ((list Z) * (list Z)) -> MONAD (list Z) :=
    fun x => match x with
             | (p1, q1) =>
                      match q1 with 
                      | nil => return p1
                      | _ :: _  =>  p2 <- mergesortrec p1 ;; 
                                    q2 <- mergesortrec q1 ;; 
                                    merge_rel p2 q2
                      end
             end.

  Definition mergesortrec_loc1 q1: list Z -> MONAD (list Z) :=
    fun p2 => q2 <- mergesortrec q1 ;; 
              merge_rel p2 q2.

  Definition mergesortrec_loc2 p2: list Z -> MONAD (list Z) :=
    fun q2 => merge_rel p2 q2.

  Lemma mono_mergesortrec_f: mono mergesortrec_f.
  Proof.
    intros.
    unfold mergesortrec_f.
    eapply bind_mono_compose_right.
    unfold mono. hnf.
    intros f1 f2 H x.
    destruct x as (p & q).
    destruct q.
    reflexivity.
    assert (forall x, f1 x ⊆ f2 x). { intros.  sets_unfold. intros. apply H. auto. }
    erewrite H0.
    assert (forall x, @Sets.included (list Z -> MONAD (list Z)) _ (fun p2 => q2 <- f1 x;; merge_rel p2 q2) 
    (fun p2 => (q2 <- f2 x;; merge_rel p2 q2))).
    { intros x0 p2.  
    erewrite H0. reflexivity. }
    erewrite H1.
    reflexivity.
  Qed.
  
  Lemma continuous_mergesortrec_f: continuous mergesortrec_f.
  Proof.
    intros.
    unfold mergesortrec_f.
    eapply bind_continuous_compose_right.
    unfold continuous, sseq_continuous, sseq_mono.
    intros l Hl.
    intros x.
    destruct x as (p & q).
    destruct q.
    + sets_unfold. intros. split;intros. exists 1%nat. auto. destruct H. auto.
    + rewrite (omega_union_introa 
      (fun (n : nat) (x0 : list Z * list Z) =>
      let (p1, q1) := x0 in
      match q1 with
      | nil => return p1
      | _ :: _ =>
          p2 <- l n p1;;
          q2  <- l n q1;;
          merge_rel p2 q2
      end) (p, z :: q)).
      assert (increasing (fun (n:nat) (p2:list Z) => q2 <- l n (z::q) ;; 
      merge_rel p2 q2)) as Hl2. 
      { eapply (increasing_mono_increasing (fun ln => 
          fun p2 => q2 <- ln (z::q);; merge_rel p2 q2 ));eauto.
        eapply bind_mono_left'. }
      pose proof program_para_equiv (bind_omega_union_distr_both l _ Hl Hl2) p.
      clear Hl2.
      rewrite omega_union_introa in H.
      rewrite <- H. clear H.
      eapply bind_equiv;[reflexivity | ].
      intros p2.
      rewrite omega_union_introa.
      erewrite bind_omega_union_distr_r' with (c1 := l) (a:= (z :: q)).
      reflexivity.
  Qed.

  Lemma mergesortrec_unfold: mergesortrec == mergesortrec_f mergesortrec.
  Proof.
    apply Lfix_fixpoint.
    apply mono_mergesortrec_f.
    apply continuous_mergesortrec_f.
  Qed.

End mergesort_monad.

Fixpoint incr_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ incr_aux l0 y
  end.

Definition incr (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => incr_aux l0 x
  end.

Section general_mergesort_monad.

  Definition ext_sort (l: list Z): MONAD (list Z) :=
    fun _ l' _ => Permutation l l' /\ incr l'.

  Definition ext_split (l: list Z): MONAD (list Z * list Z) :=
    fun _ '(l0, l1) _ =>   Permutation l (l0 ++ l1).

  Definition gmergesortrec_f  (W :  (list Z) -> MONAD (list Z) ) 
                        : ((list Z) -> MONAD (list Z)) :=
    fun x => 
      choice
        (ext_sort x)
        (test (Zlength x >= 2)%Z;;
         '(p1, q1) <- ext_split x ;; 
         p2 <- W (p1) ;; 
         q2 <- W (q1) ;; 
         merge_rel p2 q2).

  Definition gmergesortrec := Lfix (gmergesortrec_f).

  Definition gmergesortrec_loc0: ((list Z) * (list Z)) -> MONAD (list Z) :=
    fun x => match x with
             | (p1, q1) =>
                 p2 <- gmergesortrec p1 ;; 
                 q2 <- gmergesortrec q1 ;; 
                 merge_rel p2 q2
             end.

  Definition gmergesortrec_loc1 q1: list Z -> MONAD (list Z) :=
    fun p2 => q2 <- gmergesortrec q1 ;; 
              merge_rel p2 q2.

  Lemma mono_gmergesortrec_f: mono gmergesortrec_f.
  Proof.
    intros.
    unfold gmergesortrec_f.
    unfold mono. hnf.
    intros c c0 H.
    intros x.
    apply choice_proper; [reflexivity | ].
    apply programbind_included_Proper ; [reflexivity | ].
    intros x0.
    apply programbind_included_Proper; [reflexivity | ].
    intros x1.
    destruct x1.
    apply programbind_included_Proper; [apply H | ].
    intros p2.
    apply programbind_included_Proper; [apply H | ].
    intros q2.
    reflexivity.
  Qed.

  Lemma continuous_gmergesortrec_f: continuous gmergesortrec_f.
  Proof.
    intros.
    unfold gmergesortrec_f.
    unfold continuous,sseq_continuous, sseq_mono.
    intros W. intros.
    intros x.
    rewrite (omega_union_introa ((fun n : nat =>  gmergesortrec_f (W n)))).
    unfold gmergesortrec_f.
    rewrite <- choice_omega_union_distr_l.
    apply choice_equiv_equiv ; [reflexivity | ].
    unfold seq.
    rewrite <- bind_omega_union_distr_l.
    apply bind_equiv ; [reflexivity | ].
    intros x0.
    rewrite omega_union_introa.
    rewrite <- bind_omega_union_distr_l.
    apply bind_equiv ; [reflexivity | ].
    intros x1.
    rewrite omega_union_introa.
    destruct x1.
    assert (increasing (fun (n:nat) (p2:list Z) => q2 <- W n l0 ;; 
      merge_rel p2 q2)) as Hl2. 
      { eapply (increasing_mono_increasing (fun ln => 
          fun p2 => q2 <- ln l0;; merge_rel p2 q2 ));eauto.
        eapply bind_mono_left'. }
    pose proof program_para_equiv (bind_omega_union_distr_both W _ H Hl2) l.
    rewrite omega_union_introa in H0.
    rewrite <- H0. clear H0.
    eapply bind_equiv;[reflexivity | ].
    intros p2.
    rewrite omega_union_introa.
    erewrite bind_omega_union_distr_r' with (c1:= W) (a:= l0).
    reflexivity.
  Qed.

  Lemma gmergesortrec_unfold: gmergesortrec == gmergesortrec_f gmergesortrec.
  Proof.
    apply Lfix_fixpoint.
    apply mono_gmergesortrec_f.
    apply continuous_gmergesortrec_f.
  Qed.

End general_mergesort_monad.

Lemma whilebreak_ind' {Σ A B: Type}:
  forall (f: A -> program Σ (A + B)) (P: A -> Σ -> Prop) (Q: B -> Σ -> Prop),
    (forall (a: A) (b: B) (σ1 σ2: Σ),
       P a σ1 -> f a σ1 (inr b) σ2 -> Q b σ2) ->
    (forall (a1 a2: A) (σ1 σ2: Σ),
       P a1 σ1 -> f a1 σ1 (inl a2) σ2 -> P a2 σ2) ->
    (forall (a: A) (b: B) (σ1 σ2: Σ),
       P a σ1 -> whilebreak f a σ1 b σ2 -> Q b σ2).
Proof.
  intros.
  unfold whilebreak in H2.
  destruct H2 as [n ?].
  revert a σ1 H1 H2; induction n; simpl; intros.
  1: { hnf in H2. tauto. }
  unfold whilebreak_f in H2 at 1.
  unfold bind in H2.
  destruct H2 as [ab [σ12 [? ?]]].
  destruct ab as [a12 | b0].
  + revert H3; apply IHn.
    revert H2; apply H0.
    tauto.
  + hnf in H3.
    unfold ret in H3.
    destruct H3; subst b0 σ12.
    revert H2; apply H.
    tauto.
Qed.

Lemma whilebreak_ind {Σ A B: Type}:
  forall (f: A -> program Σ (A + B)) (P: A -> Σ -> Prop) (Q: B -> Σ -> Prop),
    (forall (a: A) (ab: A + B) (σ1 σ2: Σ),
       P a σ1 -> f a σ1 ab σ2 ->
       match ab with | inl a2 => P a2 σ2 | inr b => Q b σ2 end) ->
    (forall (a: A) (b: B) (σ1 σ2: Σ),
       P a σ1 -> whilebreak f a σ1 b σ2 -> Q b σ2).
Proof.
  intros ? ? ? ?.
  apply whilebreak_ind'.
  + intros ? ? ? ?.
    apply H.
  + intros ? ? ? ?.
    apply H.
Qed.

Lemma Lfix_ind {Σ A B: Type}:
  forall (f: (A -> program Σ B) -> (A -> program Σ B))
         (P: A -> Σ -> Prop) (Q: A -> B -> Σ -> Prop),
    (forall W: A -> program Σ B,
       (forall a b σ1 σ2, P a σ1 -> W a σ1 b σ2 -> Q a b σ2) ->
       (forall a b σ1 σ2, P a σ1 -> f W a σ1 b σ2 -> Q a b σ2)) ->
    (forall a b σ1 σ2, P a σ1 -> Lfix f a σ1 b σ2 -> Q a b σ2).
Proof.
  intros.
  destruct H1 as [n ?].
  revert a b σ1 σ2 H0 H1; induction n; simpl.
  1: { intros. hnf in H1. tauto. }
  apply H.
  apply IHn.
Qed.


Lemma incr_app_cons: forall l1 x l2,
  incr (l1 ++ [x]) ->
  incr (x :: l2) ->
  incr (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv1: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv2: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.


Section algorithm_correctness.

Lemma merge_rel_perm:
  forall l1 l2 l3 σ σ',
    merge_rel l1 l2 σ l3 σ' ->
    Permutation (l1 ++ l2) l3.
Proof.
  unfold merge_rel.
  intros l1 l2 l3 ? ?.
  apply (whilebreak_ind _
           (fun L _ => match L with
                       | (l1', l2', l3') => Permutation (l3' ++ l1' ++ l2') (l1 ++ l2)
                       end)
           (fun l _ => Permutation (l1 ++ l2) l)).
  2: { reflexivity. }
  intros [ [l1' l2'] l3'] ? ? ? ? ?.
  unfold merge_body in H0.
  destruct l1' as [ | ? l1']; [ | destruct l2' as [ | ? l2'] ].
  + hnf in H0.
    unfold ret in H0.
    destruct H0; subst.
    rewrite <- H.
    reflexivity.
  + hnf in H0.
    unfold ret in H0.
    destruct H0; subst.
    rewrite <- H.
    rewrite app_nil_r.
    reflexivity.
  + destruct H0.
    - hnf in H0.
      destruct H0 as [? [? [? ?] ] ].
      hnf in H0.
      destruct H0; subst x0.
      hnf in H1.
      destruct H1; subst.
      simpl.
      rewrite <- H.
      rewrite <- app_assoc.
      reflexivity.
    - hnf in H0.
      destruct H0 as [? [? [? ?] ] ].
      hnf in H0.
      destruct H0; subst x0.
      hnf in H1.
      destruct H1; subst.
      simpl.
      rewrite <- H.
      rewrite <- ! app_assoc.
      apply Permutation_app_head.
      rewrite <- (Permutation_middle _ _ z0).
      reflexivity.
Qed.

Lemma merge_rel_incr:
  forall l1 l2 l3 σ σ',
    merge_rel l1 l2 σ l3 σ' ->
    incr l1 ->
    incr l2 ->
    incr l3.
Proof.
  intros.
  revert H; unfold merge_rel.
  apply (whilebreak_ind _
           (fun L _ => match L with
                       | (l1', l2', l3') => incr (l3' ++ l1') /\
                                            incr (l3' ++ l2')
                       end)
           (fun l _ => incr l)).
  2: { simpl. tauto. }
  intros [ [l1' l2'] l3'] ? ? ? ? ?.
  unfold merge_body in H2.
  destruct l1' as [ | ? l1']; [ | destruct l2' as [ | ? l2'] ].
  + hnf in H2; unfold ret in H2.
    destruct H2; subst.
    tauto.
  + hnf in H2; unfold ret in H2.
    destruct H2; subst.
    tauto.
  + destruct H as [INC1 INC2].
    destruct H2.
    - hnf; destruct H as [? [? [? ?] ] ].
      hnf in H; destruct H; subst.
      hnf in H2; unfold ret in H2; destruct H2; subst.
      split; [rewrite <- app_assoc; simpl; tauto | ].
      rewrite <- app_assoc; simpl.
      apply incr_app_cons.
      * apply incr_app_cons_inv1 in INC1.
        tauto.
      * apply incr_app_cons_inv2 in INC2.
        simpl; tauto.
    - hnf; destruct H as [? [? [? ?] ] ].
      hnf in H; destruct H; subst.
      hnf in H2; unfold ret in H2; destruct H2; subst.
      split; [ | rewrite <- app_assoc; simpl; tauto].
      rewrite <- app_assoc; simpl.
      apply incr_app_cons.
      * apply incr_app_cons_inv1 in INC2.
        tauto.
      * apply incr_app_cons_inv2 in INC1.
        simpl; tauto.
Qed.

Lemma split_rel_perm:
  forall l l1 l2 σ σ',
    split_rel l σ (l1, l2) σ' ->
    Permutation l (l1 ++ l2).
Proof.
  intros.
  revert H.
  unfold split_rel.
  apply (Lfix_ind _
           (fun L _ => match L with 
                       | (l', l1', l2') => Permutation l (l' ++ l1' ++ l2')
                       end)
           (fun _ L _ => match L with
                         | (l1', l2') => Permutation l (l1' ++ l2')
                         end)).
  2: { rewrite !app_nil_r. reflexivity. }
  intros W ?.
  clear l1 l2.
  intros [ [l' l1'] l2' ] [l1 l2] ? ? ? ?.
  unfold split_rec_rel_f in H1.
  destruct l'.
  + hnf in H1; unfold ret in H1.
    destruct H1 as [H1 ?]; injection H1 as ? ?; subst.
    exact H0.
  + hnf in H1.
    destruct H1 as [ [l1'' l2''] [σ'' [? ?] ]].
    hnf in H2; unfold ret in H2.
    destruct H2 as [H2 ?]; injection H2 as ? ?; subst.
    rewrite Permutation_app_comm.
    revert H1.
    apply H.
    rewrite H0.
    rewrite (app_assoc l').
    rewrite (Permutation_app_comm (l' ++ l2')).
    rewrite !app_assoc.
    apply Permutation_app_tail.
    simpl.
    apply perm_skip.
    apply Permutation_app_comm.
Qed.

Lemma split_rel_length:
  forall l l1 l2 σ σ',
    split_rel l σ (l1, l2) σ' ->
    (0 <= length l1 - length l2 <= 1)%nat.
Proof.
  intros.
  assert (0 <= length l1 /\
          0 <= length l2 /\
          length l2 - 0 <=
          length l1 - 0 <=
          S (length l2 - 0))%nat; [ | lia].
  revert H.
  unfold split_rel, split_rec_rel'.
  refine (Lfix_ind _
           (fun _ _ => True)
           (fun L L' _ => match L, L' with
                         | (_, l1', l2'), (l1'', l2'') =>
                             (length l1' <= length l1'' /\
                              length l2' <= length l2'' /\
                              length l2'' - length l2' <=
                              length l1'' - length l1' <=
                              S (length l2'' - length l2'))%nat
                         end)
           _ (l, nil, nil) (l1, l2) _ _ I).
  clear l l1 l2.
  intros W ?.
  intros [ [l' l1'] l2' ] [l1 l2] ? ? ? ?.
  unfold split_rec_rel_f in H1.
  destruct l'.
  + hnf in H1; unfold ret in H1.
    destruct H1 as [H1 ?]; injection H1 as ? ?; subst.
    lia.
  + hnf in H1.
    destruct H1 as [ [l1'' l2''] [σ'' [? ?] ]].
    hnf in H2; unfold ret in H2.
    destruct H2 as [H2 ?]; injection H2 as ? ?; subst.
    specialize (H _ _ _ _ I H1).
    simpl in H.
    lia.
Qed.

Lemma split_rel_snd_nil:
  forall l l1 σ σ',
    split_rel l σ (l1, nil) σ' ->
    (length l1 <= 1)%nat.
Proof.
  intros.
  pose proof split_rel_length _ _ _ _ _ H.
  simpl in H0.
  lia.
Qed.

Lemma split_rel_snd_nil':
  forall l l1 σ σ',
    split_rel l σ (l1, nil) σ' ->
    Permutation l l1 /\ incr l1.
Proof.
  intros.
  pose proof split_rel_perm _ _ _ _ _ H.
  pose proof split_rel_snd_nil _ _ _ _ H.
  rewrite app_nil_r in H0.
  split; auto.
  destruct l1 as [ | ? [ | ? ?] ]; simpl; auto.
  simpl in H1; lia.
Qed.

Lemma split_rel_refine_ext_split : 
  forall l, 
    split_rel l ⊆ ext_split l.
Proof.
  intros.
  intros x (l1,l2) x' H.
  unfold ext_split.
  eapply split_rel_perm;eauto.
Qed.

Lemma mergesortrec_perm: forall l l' σ σ',
  mergesortrec l σ l' σ' ->
  Permutation l l'.
Proof.
  intros l l' ? ?.
  unfold mergesortrec.
  apply (Lfix_ind _
           (fun _ _ => True)
           (fun l l' _ => Permutation l l')).
  2: { tauto. }
  intros W ?.
  clear l l'.
  intros l l' ? ? _ ?.
  unfold mergesortrec_f in H0.
  hnf in H0.
  destruct H0 as [ [l1 l2] [σ'' [? ?] ] ].
  pose proof split_rel_perm _ _ _ _ _ H0.
  destruct l2.
  + hnf in H1; unfold ret in H1.
    destruct H1; subst.
    rewrite app_nil_r in H2.
    tauto.
  + hnf in H1; destruct H1 as [l1' [σ''' [? ?] ] ].
    hnf in H3; destruct H3 as [l2' [σ'''' [? ?] ] ].
    pose proof H _ _ _ _ I H1.
    pose proof H _ _ _ _ I H3.
    pose proof merge_rel_perm _ _ _ _ _ H4.
    rewrite H2, H5, H6, H7.
    reflexivity.
Qed.

Lemma mergesortrec_incr: forall l l' σ σ',
  mergesortrec l σ l' σ' ->
  incr l'.
Proof.
  intros l l' ? ?.
  unfold mergesortrec.
  apply (Lfix_ind _
           (fun _ _ => True)
           (fun _ l' _ => incr l')).
  2: { tauto. }
  intros W ?.
  clear l l'.
  intros l l' ? ? _ ?.
  unfold mergesortrec_f in H0.
  hnf in H0.
  destruct H0 as [ [l1 l2] [σ'' [? ?] ] ].
  pose proof split_rel_perm _ _ _ _ _ H0.
  destruct l2.
  + hnf in H1; unfold ret in H1.
    destruct H1; subst.
    pose proof split_rel_snd_nil' _ _ _ _ H0.
    tauto.
  + hnf in H1; destruct H1 as [l1' [σ''' [? ?] ] ].
    hnf in H3; destruct H3 as [l2' [σ'''' [? ?] ] ].
    pose proof H _ _ _ _ I H1.
    pose proof H _ _ _ _ I H3.
    pose proof merge_rel_incr _ _ _ _ _ H4.
    tauto.
Qed.

Lemma gmergesortrec_perm: forall l l' σ σ',
  gmergesortrec l σ l' σ' ->
  Permutation l l'.
Proof.
  intros l l' ? ?.
  unfold gmergesortrec.
  apply (Lfix_ind _
           (fun _ _ => True)
           (fun l l' _ => Permutation l l')).
  2: { tauto. }
  intros W ?.
  clear l l'.
  intros l l' ? ? _ ?.
  unfold gmergesortrec_f in H0.
  hnf in H0.
  destruct H0; [hnf in H0; tauto | ].
  hnf in H0.
  destruct H0 as [σ0 [σ'' [? ?]]].
  hnf in H0.
  destruct H0 as [? _]; subst σ1; clear σ0.
  hnf in H1.
  destruct H1 as [ [l1 l2] [σ''' [? ?] ] ].
  hnf in H0.
  hnf in H1; destruct H1 as [l1' [σ'''' [? ?] ] ].
  hnf in H2; destruct H2 as [l2' [σ''''' [? ?] ] ].
  pose proof H _ _ _ _ I H1.
  pose proof H _ _ _ _ I H2.
  pose proof merge_rel_perm _ _ _ _ _ H3.
  rewrite H0, H4, H5, H6.
  reflexivity.
Qed.

Lemma gmergesortrec_incr: forall l l' σ σ',
  gmergesortrec l σ l' σ' ->
  incr l'.
Proof.
  intros l l' ? ?.
  unfold gmergesortrec.
  apply (Lfix_ind _
           (fun _ _ => True)
           (fun _ l' _ => incr l')).
  2: { tauto. }
  intros W ?.
  clear l l'.
  intros l l' ? ? _ ?.
  unfold gmergesortrec_f in H0.
  hnf in H0.
  destruct H0; [hnf in H0; tauto | ].
  hnf in H0.
  destruct H0 as [σ0 [σ'' [? ?]]].
  hnf in H0.
  destruct H0 as [? _]; subst σ1; clear σ0.
  hnf in H1.
  destruct H1 as [ [l1 l2] [σ''' [? ?] ] ].
  hnf in H0.
  hnf in H1; destruct H1 as [l1' [σ'''' [? ?] ] ].
  hnf in H2; destruct H2 as [l2' [σ''''' [? ?] ] ].
  pose proof H _ _ _ _ I H1.
  pose proof H _ _ _ _ I H2.
  pose proof merge_rel_incr _ _ _ _ _ H3.
  tauto.
Qed.

End algorithm_correctness.
