(**
  This file contains the syntax tree of logical expr we need.
**)
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From compcert.lib Require Import Coqlib Integers.
From SimpleC.ASRT Require Import PolyType DepList.
From SimpleC.ASRTFUN Require Import list_lemma.
Require Import AUXLib.List_lemma.
Require Import AUXLib.Feq.
Require Import AUXLib.Idents.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.Common Require Import Notations.

Local Open Scope string.
Local Open Scope option_monad_scope.
Import Coq.Lists.List.ListNotations.
(* Import EqNotations. *)


Definition var_type_asgn: Type :=
  var_type_name -> Type.

Definition builtin_type_asgn: Type :=
  builtin_type_name -> Type.

Definition const_ptype_asgn: Type :=
  const_ptype_name -> list Type -> Type.


Record type_asgn_list : Type := {
  cpt_list: list (const_ptype_name * (list Type -> Type));
  bt_list:  list (builtin_type_name * Type);
  vt_list:  list (var_type_name * Type)
}.

Definition get_type_names_from_type_asgn_list (l: type_asgn_list) :=
  Build_type_names
    (map fst l.(cpt_list))
    (map fst l.(bt_list))
    (map fst l.(vt_list)).

Definition type_asgn_list_nodup (l: type_asgn_list): Prop :=
  NoDup (map fst l.(cpt_list)) /\
  NoDup (map fst l.(bt_list)) /\
  NoDup (map fst l.(vt_list)).

Definition type_asgn_list_incl (l1 l2: type_asgn_list): Prop :=
  incl l1.(cpt_list) l2.(cpt_list) /\
  incl l1.(bt_list) l2.(bt_list) /\
  incl l1.(vt_list) l2.(vt_list).

(* Record type_asgn : Type := {
  cpt: const_ptype_asgn;
  bt: builtin_type_asgn;
  vt: var_type_asgn
}. *)

Inductive type_asgn : Type :=
  | Build_type_asgn (cpt: const_ptype_asgn) (bt: builtin_type_asgn) (vt: var_type_asgn).

Definition get_cpt_of_type_asgn (t: type_asgn): const_ptype_asgn :=
  match t with
  | Build_type_asgn cpt _ _ => cpt
  end.
Definition get_bt_of_type_asgn (t: type_asgn): builtin_type_asgn :=
  match t with
  | Build_type_asgn _ bt _ => bt
  end.
Definition get_vt_of_type_asgn (t: type_asgn): var_type_asgn :=
  match t with
  | Build_type_asgn _ _ vt => vt
  end.
Notation "n '.(cpt)' " := (get_cpt_of_type_asgn n) (at level 0).
Notation "n '.(bt)' " := (get_bt_of_type_asgn n) (at level 0).
Notation "n '.(vt)' " := (get_vt_of_type_asgn n) (at level 0).



(* Record type_names := {
  const_ptype_names: list const_ptype_name;
  builtin_names: list builtin_type_name;
  var_names: list var_type_name;
}. *)
Definition type_names_in_list (n: type_names) (l: type_asgn_list): Prop :=
  incl n.(const_ptype_names) (map fst l.(cpt_list)) /\
  incl n.(builtin_names)     (map fst l.(bt_list)) /\
  incl n.(var_names)         (map fst l.(vt_list)).


(* Definition const_ptype_asgn_upd
             (cptJ: const_ptype_asgn)
             (i: const_ptype_name)
             (f: list Type -> Type): const_ptype_asgn :=
  fun i0 ts => if const_ptype_name_eq_dec i0 i then f ts else cptJ i0 ts.

Definition const_ptype_asgn_upd_list
             (cptJ: const_ptype_asgn)
             (l: list (const_ptype_name * (list Type -> Type))): const_ptype_asgn :=
  fold_left (fun cptJ0 p => const_ptype_asgn_upd cptJ0 (fst p) (snd p)) l cptJ.

#[export] Instance const_ptype_asgn_upd_congr0 :
  Proper (f_eq ==> eq ==> eq ==> f_eq) const_ptype_asgn_upd.
Proof.
  unfold Proper, respectful, const_ptype_asgn_upd, f_eq.
  intros J1 J2 HJ x y <- f1 f2 <- x0.
  rewrite <- (HJ x0).
  reflexivity.
Qed.

#[export] Instance const_ptype_asgn_upd_list_congr0 :
  Proper (f_eq ==> eq ==> f_eq) const_ptype_asgn_upd_list.
Proof.
  unfold Proper, respectful, f_eq.
  intros J J' HJ l l' <-.
  revert J J' HJ. induction l; intros; simpl.
  - apply HJ.
  - destruct a as [i f]. simpl.
    apply IHl. intros.
    apply const_ptype_asgn_upd_congr0; auto.
Qed.


Lemma const_ptype_asgn_upd_eq: forall cptJ i f,
  const_ptype_asgn_upd cptJ i f i = f.
Proof.
  intros.
  unfold const_ptype_asgn_upd.
  destruct (const_ptype_name_eq_dec i i); try congruence.
  reflexivity.
Qed.

Lemma const_ptype_asgn_upd_neq: forall cptJ x f y,
  x <> y ->
  const_ptype_asgn_upd cptJ x f y = cptJ y.
Proof.
  intros.
  unfold const_ptype_asgn_upd.
  destruct (const_ptype_name_eq_dec _ _); try congruence.
  reflexivity.
Qed.


Lemma const_ptype_asgn_upd_perm : forall cptJ x y f1 f2,
  x <> y ->
  f_eq (const_ptype_asgn_upd (const_ptype_asgn_upd cptJ x f1) y f2)
       (const_ptype_asgn_upd (const_ptype_asgn_upd cptJ y f2) x f1).
Proof.
  intros.
  unfold f_eq, const_ptype_asgn_upd. intros z.
  destruct (const_ptype_name_eq_dec z x), (const_ptype_name_eq_dec z y); try congruence.
Qed.


Lemma const_ptype_asgn_upd_perm_list : forall cptJ x f l,
  ~ In x (map fst l) ->
  f_eq (const_ptype_asgn_upd_list (const_ptype_asgn_upd cptJ x f) l)
       (const_ptype_asgn_upd (const_ptype_asgn_upd_list cptJ l) x f).
Proof.
  intros. revert cptJ.
  induction l; intros; simpl.
  - reflexivity.
  - destruct a as [i f']. simpl.
    assert (x <> i).
    { contradict H. simpl. left. auto. }
    assert (~ In x (map fst l)).
    { contradict H. simpl. right. auto. }
    rewrite const_ptype_asgn_upd_perm by congruence.
    rewrite IHl; auto.
    reflexivity.
Qed.


Lemma const_ptype_asgn_upd_list_no_dup: forall cptJ l,
  NoDup (map fst l) ->
  forall i f, In (i, f) l -> const_ptype_asgn_upd_list cptJ l i = f.
Proof.
  intros.
  revert cptJ H i f H0.
  induction l; intros; simpl in *.
  - destruct H0.
  - destruct a as [i' f']. simpl in *.
    inversion H. subst.
    destruct H0.
    + inversion H0; subst.
      rewrite (const_ptype_asgn_upd_perm_list cptJ i f l H3 i).
      rewrite const_ptype_asgn_upd_eq.
      reflexivity.
    + apply IHl; auto.
Qed. *)


Module Type asgn_update_sig.
  Parameter K: Type.
  Parameter V: Type.
  Parameter K_eq_dec: forall x y: K, {x = y} + {x <> y}.
  Parameter unit: K -> V.
End asgn_update_sig.

Module MakeAsgnUpdate (Import A: asgn_update_sig).
  Definition asgn: Type := K -> V.
  Definition upd (J: asgn) (k: K) (v: V): asgn :=
    fun k' => if K_eq_dec k' k then v else J k'.
  Definition upd_list (J: asgn) (l: list (K * V)): asgn :=
    fold_left (fun J0 p => upd J0 (fst p) (snd p)) l J.
  Definition from_list (l: list (K * V)) := upd_list unit l.
  
  #[export] Instance upd_congr0 :
    Proper (f_eq ==> eq ==> eq ==> f_eq) upd.
  Proof.
    unfold Proper, respectful, upd, f_eq.
    intros J1 J2 HJ x y <- v1 v2 <- x0.
    rewrite <- (HJ x0).
    reflexivity.
  Qed.

  #[export] Instance upd_list_congr0 :
    Proper (f_eq ==> eq ==> f_eq) upd_list.
  Proof.
    unfold Proper, respectful, f_eq.
    intros J J' HJ l l' <-.
    revert J J' HJ. induction l; intros; simpl.
    - apply HJ.
    - destruct a as [i f]. simpl.
      apply IHl. intros.
      apply upd_congr0; auto.
  Qed.

  Lemma upd_eq: forall J i v,
    upd J i v i = v.
  Proof.
    intros.
    unfold upd.
    destruct (K_eq_dec i i); try congruence.
  Qed.

  Lemma upd_neq: forall J x v y,
    x <> y ->
    upd J x v y = J y.
  Proof.
    intros.
    unfold upd.
    destruct (K_eq_dec _ _); try congruence.
  Qed.
  
  Lemma upd_perm : forall J x y v1 v2,
    x <> y ->
    f_eq (upd (upd J x v1) y v2)
         (upd (upd J y v2) x v1).
  Proof.
    intros.
    unfold f_eq, upd. intros z.
    destruct (K_eq_dec z x), (K_eq_dec z y); try congruence.
  Qed.
  
  Lemma upd_perm_list : forall J x v l,
    ~ In x (map fst l) ->
    f_eq (upd_list (upd J x v) l)
         (upd (upd_list J l) x v).
  Proof.
    intros. revert J.
    induction l; intros; simpl.
    - reflexivity.
    - destruct a as [i f]. simpl.
      assert (x <> i).
      { contradict H. simpl. left. auto. }
      assert (~ In x (map fst l)).
      { contradict H. simpl. right. auto. }
      rewrite upd_perm by congruence.
      rewrite IHl; auto.
      reflexivity.
  Qed.

  Lemma upd_list_no_dup: forall J l,
    NoDup (map fst l) ->
    forall i v, In (i, v) l -> upd_list J l i = v.
  Proof.
    intros.
    revert J H i v H0.
    induction l; intros; simpl in *.
    - destruct H0.
    - destruct a as [i' f']. simpl in *.
      inversion H. subst.
      destruct H0.
      + inversion H0; subst.
        rewrite (upd_perm_list J i v l H3 i).
        rewrite upd_eq.
        reflexivity.
      + apply IHl; auto.
  Qed.

  Lemma key_nodup_val_same [K V: Type]: forall (l: list (K * V)),
    NoDup (map fst l) ->
    forall i v1 v2, In (i, v1) l -> In (i, v2) l -> v1 = v2.
  Proof.
    intros l Hnodup i v1 v2 Hin1 Hin2.
    induction l.
    - destruct Hin1.
    - destruct a as [i' v']. simpl in *.
      inversion Hnodup. subst.
      destruct Hin1 as [Heq1 | Hin1], Hin2 as [Heq2 | Hin2].
      + inversion Heq1; inversion Heq2; subst. reflexivity.
      + inversion Heq1; subst.
        exfalso. apply H1. apply in_map_iff. exists (i, v2). auto.
      + inversion Heq2; subst.
        exfalso. apply H1. apply in_map_iff. exists (i, v1). auto.
      + apply IHl; auto.
  Qed.

  (* Lemma upd_list_include: forall J l1 l2,
    NoDup (map fst l1) -> NoDup (map fst l2) ->
    incl (map fst l1) (map fst l2) ->
    forall i v, In (i, v) l1 -> upd_list J l2 i = v.
  Proof.
    intros J l1 l2 Hnodup1 Hnodup2 Hincl i v Hin.
    apply upd_list_no_dup; auto.
    assert (Lem: In (i, v) l1 -> In i (map fst l1)).
    { intros. apply in_map_iff. exists (i, v). auto. }
    apply Lem in Hin. apply Hincl in Hin.
    apply in_map_iff in Hin. destruct Hin as [[i' v'] [Heq Hin]].
    simpl in Heq. subst i'.
    pose proof key_nodup_val_same l2 Hnodup2 i v'.  (l := l2).
    assert (Lem2: NoDup (map fst l2) -> In (i, v') l2 -> In (i, v) l2 -> v = v').
    { intros. induction H.
      
      - destruct H0, H1.
        + inversion H0; inversion H1; subst. reflexivity.
        + inversion H0; subst. apply IHNoDup; auto.
        + inversion H1; subst. apply IHNoDup; auto.
        + apply IHNoDup; auto. }
    
    apply (upd_list_no_dup J l2); auto. } *)
End MakeAsgnUpdate.

Module const_ptype_asgn <: asgn_update_sig.
  Definition K := const_ptype_name.
  Definition V := list Type -> Type.
  Definition unit: K -> V := fun _ _ => unit.
  Definition K_eq_dec := const_ptype_name_eq_dec.
  Include MakeAsgnUpdate.
End const_ptype_asgn.

Module builtin_type_asgn <: asgn_update_sig.
  Definition K := builtin_type_name.
  Definition V := Type.
  Definition unit: K -> V := fun _ => unit.
  Definition K_eq_dec := builtin_type_name_eq_dec.
  Include MakeAsgnUpdate.
End builtin_type_asgn.

Module var_type_asgn <: asgn_update_sig.
  Definition K := var_type_name.
  Definition V := Type.
  Definition unit: K -> V := fun _ => unit.
  Definition K_eq_dec := var_type_name_eq_dec.
  Include MakeAsgnUpdate.
End var_type_asgn.

(* Definition make_type_asgn_from_list (l: type_asgn_list): type_asgn :=
  Build_type_asgn
    (fun i ts =>
      match find (fun p => const_ptype_name_eq_dec (fst p) i) l.(cpt_list) with
      | Some (_, f) => f ts
      | None => unit
      end)
    (fun i =>
      match find (fun p => builtin_type_name_eq_dec (fst p) i) l.(bt_list) with
      | Some (_, f) => f
      | None => unit
      end)
    (fun i =>
      match find (fun p => var_type_name_eq_dec (fst p) i) l.(vt_list) with
      | Some (_, f) => f
      | None => unit
      end). *)

Definition make_type_asgn_from_list (l: type_asgn_list): type_asgn :=
  Build_type_asgn
    (const_ptype_asgn.from_list  l.(cpt_list))
    (builtin_type_asgn.from_list l.(bt_list))
    (var_type_asgn.from_list     l.(vt_list)).



Definition TArrow (t1 t2: type): type := TPolyApp "->" [t1; t2].
#[export] Hint Unfold TArrow : core.

Definition add_builtin_ptype (x : const_ptype_asgn) : const_ptype_asgn :=
  fun i =>
    if const_ptype_name_eq_dec i "->" then
      fun ts =>
        match ts with
        | cons arg1 (cons arg2 nil) =>
            arg1 -> arg2
        | _ => unit
        end
    else x i.

Definition teval (tJ: type_asgn): type -> Type :=
  let cpt := add_builtin_ptype tJ.(cpt) in
  fix teval (t: type): Type :=
    match t with
    | Tunit => unit
    | TBuiltin i => tJ.(bt) i
    | TVar i => tJ.(vt) i
    | TPolyApp i arg =>
      cpt i (map teval arg)
    end.


Definition type_asgn_coincide_on_names (J1 J2: type_asgn) (n: type_names) : Prop :=
  (forall i, In i n.(const_ptype_names) -> J1.(cpt) i = J2.(cpt) i) /\
  (forall i, In i n.(builtin_names) -> J1.(bt) i = J2.(bt) i) /\
  (forall i, In i n.(var_names) -> J1.(vt) i = J2.(vt) i).

Lemma type_names_include_coincide: forall n1 n2 J1 J2,
  type_names_include n1 n2 ->
  type_asgn_coincide_on_names J1 J2 n2 ->
  type_asgn_coincide_on_names J1 J2 n1.
Proof.
  intros.
  destruct H as [Hcpt [Hbt Hvt]].
  destruct H0 as [Hcpt' [Hbt' Hvt']].
  repeat split; intros.
  + apply Hcpt'. auto.
  + apply Hbt'. auto.
  + apply Hvt'. auto.
Qed.

Lemma type_asgn_coincide_app_l: forall J1 J2 n1 n2,
  type_asgn_coincide_on_names J1 J2 (type_names_app n1 n2) ->
  type_asgn_coincide_on_names J1 J2 n1.
Proof.
  intros.
  destruct H as [Hcpt [Hbt Hvt]].
  repeat split; intros.
  + apply Hcpt. simpl. apply in_or_app. left. tauto.
  + apply Hbt. simpl. apply in_or_app. left. tauto.
  + apply Hvt. simpl. apply in_or_app. left. tauto.
Qed.

Lemma type_asgn_coincide_app_r: forall J1 J2 n1 n2,
  type_asgn_coincide_on_names J1 J2 (type_names_app n1 n2) ->
  type_asgn_coincide_on_names J1 J2 n2.
Proof.
  intros.
  destruct H as [Hcpt [Hbt Hvt]].
  repeat split; intros.
  + apply Hcpt. simpl. apply in_or_app. right. tauto.
  + apply Hbt. simpl. apply in_or_app. right. tauto.
  + apply Hvt. simpl. apply in_or_app. right. tauto.
Qed.

Ltac smart_destruct H :=
  match type of H with
  | _ /\ _ =>
    let L := fresh "L" in
    let R := fresh "R" in
    destruct H as [L R]; smart_destruct L; smart_destruct R
  | _ \/ _ =>
    destruct H as [H | H]; smart_destruct H
  | _ => idtac
  end.


Theorem teval_coincide: forall (J1 J2 : type_asgn) t,
  type_asgn_coincide_on_names J1 J2 (get_type_names t) ->
  teval J1 t = teval J2 t.
Proof.
  intros J1 J2 t Hco.
  unfold type_asgn_coincide_on_names in Hco; simpl in Hco; destruct Hco as [Hcpt [Hbt Hvt]].
  revert dependent t.
  induction t using type_nested_ind with (Q := fun ts =>
    forall t, In t ts ->
      type_asgn_coincide_on_names J1 J2 (get_type_names t) ->
      teval J1 t = teval J2 t); simpl in *; intros.
  + reflexivity.
  + apply (Hbt i). left. reflexivity.
  + apply (Hvt i). left. reflexivity.
  + assert (Hmap: map (teval J1) arg = map (teval J2) arg).
    { apply map_ext_in. intros t' Hin. apply (IHt t' Hin). repeat split; intros.
      - apply Hcpt. right. apply in_flat_map. exists t'. auto.
      - apply Hbt. apply in_flat_map. exists t'. auto.
      - apply Hvt. apply in_flat_map. exists t'. auto. }
    rewrite <- Hmap.
    unfold add_builtin_ptype.
    destruct (const_ptype_name_eq_dec i "->"). 1: reflexivity.
    rewrite Hcpt. 1: reflexivity. left. reflexivity.
  + tauto.
  + destruct H; auto.
    subst t0. apply IHt0; apply H0.
Qed.


Theorem type_asgn_include_coincide: forall (l1 l2: type_asgn_list),
  type_asgn_list_nodup l1 -> type_asgn_list_nodup l2 ->
  type_asgn_list_incl l1 l2 ->
  let tJ1 := make_type_asgn_from_list l1 in
  let tJ2 := make_type_asgn_from_list l2 in
  let tn1 := get_type_names_from_type_asgn_list l1 in
  type_asgn_coincide_on_names tJ1 tJ2 tn1.
Proof.
  intros l1 l2 Hnodup1 Hnodup2 Hincl tJ1 tJ2 tn1.
  repeat split; intro;
    unfold tn1; intro Hin1; simpl in Hin1;
    apply in_map_iff in Hin1; destruct Hin1 as [x [Heq Hin1]].
  - destruct Hincl as [Hincl _]. specialize (Hincl x).
    pose proof Hincl Hin1 as Hin2.
    destruct Hnodup1 as [Hnodup1 _].
    destruct Hnodup2 as [Hnodup2 _].
    destruct x as [i' v]. simpl in Heq; subst i'.
    unfold tJ1, tJ2, make_type_asgn_from_list. simpl.
    unfold const_ptype_asgn.from_list.
    rewrite! const_ptype_asgn.upd_list_no_dup with (v := v); auto.
  - destruct Hincl as [_ [Hincl _]]. specialize (Hincl x).
    pose proof Hincl Hin1 as Hin2.
    destruct Hnodup1 as [_ [Hnodup1 _]].
    destruct Hnodup2 as [_ [Hnodup2 _]].
    destruct x as [i' v]. simpl in Heq; subst i'.
    unfold tJ1, tJ2, make_type_asgn_from_list. simpl.
    unfold builtin_type_asgn.from_list.
    rewrite! builtin_type_asgn.upd_list_no_dup with (v := v); auto.
  - destruct Hincl as [_ [_ Hincl]]. specialize (Hincl x).
    pose proof Hincl Hin1 as Hin2.
    destruct Hnodup1 as [_ [_ Hnodup1]].
    destruct Hnodup2 as [_ [_ Hnodup2]].
    destruct x as [i' v]. simpl in Heq; subst i'.
    unfold tJ1, tJ2, make_type_asgn_from_list. simpl.
    unfold var_type_asgn.from_list.
    rewrite! var_type_asgn.upd_list_no_dup with (v := v); auto.
Qed.










Fixpoint Build_vtJ
           (l1: list var_type_name)
           (l2: list Type): var_type_asgn :=
  match l1, l2 with
  | nil, _ =>
      fun _ => unit
  | cons i l1', cons t l2' =>
      var_type_asgn.upd (Build_vtJ l1' l2') i t
  | cons i l1', nil =>
      var_type_asgn.upd (Build_vtJ l1' nil) i unit
  end.

Definition subst_vt (tJ: type_asgn) (l1: list var_type_name) (l2: list type): type_asgn :=
  Build_type_asgn tJ.(cpt) tJ.(bt) (Build_vtJ l1 (map (teval tJ) l2)).


Lemma var_type_subst_nil: forall i l1,
  var_type_subst i l1 nil = Tunit.
Proof.
  intros.
  destruct l1; reflexivity.
Defined.

Lemma Build_vtJ_nil: forall l1 i,
  Build_vtJ l1 nil i = unit.
Proof.
  intros.
  induction l1; simpl.
  + reflexivity.
  + unfold var_type_asgn.upd.
    destruct (var_type_asgn.K_eq_dec _ _).
    - reflexivity.
    - apply IHl1.
Defined.

Lemma var_type_subst_sound
        (tJ: type_asgn)
        (l1: list var_type_name)
        (l2: list type)
        (i: var_type_name):
  (Build_vtJ l1 (map (teval tJ) l2)) i =
  teval tJ (var_type_subst i l1 l2).
Proof.
  intros.
  revert l2; induction l1; intros.
  + simpl.
    reflexivity.
  + destruct l2 as [| t0 l2'].
    - rewrite var_type_subst_nil.
      simpl map.
      rewrite Build_vtJ_nil.
      reflexivity.
    - simpl.
      unfold var_type_asgn.upd.
      rewrite IHl1.
      unfold var_type_asgn.K_eq_dec.
      destruct (var_type_name_eq_dec _ _); reflexivity.
Defined.

Lemma type_subst_sound
        (tJ: type_asgn)
        (l1: list var_type_name)
        (l2: list type)
        (t: type):
  teval (subst_vt tJ l1 l2) t =
  teval tJ (type_subst l1 l2 t).
Proof.
  revert t.
  apply type_nested_ind with (Q := fun ts =>
    map (teval (subst_vt tJ l1 l2)) ts =
    map (teval tJ) (map (type_subst l1 l2) ts)); intros; simpl.
  + reflexivity.
  + reflexivity.
  + apply var_type_subst_sound.
  + rewrite H; reflexivity.
  + reflexivity.
  + rewrite H, H0; reflexivity.
Defined.


Inductive expr: type -> Type :=
  | EVar (i: var_name) (t: type): expr t
  | EConst (val: string) (t_params : list var_type_name) (t_args: list type) (t : type)
      : expr (type_subst t_params t_args t)
  | EApp (arg_type ret_type : type) (f : expr (TArrow arg_type ret_type)) (arg : expr arg_type)
      : expr ret_type
.

(* Record expr_names: Type := Build_expr_names {
  _:> type_names;
  var_names: list var_name;
  const_names: list string
}. *)
Inductive expr_names : Type :=
  Build_expr_names (tn: type_names) (var_names: list var_name) (const_names: list string).
Definition get_type_names_of_expr_names (n: expr_names): type_names :=
  match n with Build_expr_names tn _ _ => tn end.
Coercion get_type_names_of_expr_names: expr_names >-> type_names.
Definition get_var_names_of_expr_names (n: expr_names): list var_name :=
  match n with Build_expr_names _ var_names _ => var_names end.
Definition get_const_names_of_expr_names (n: expr_names): list string :=
  match n with Build_expr_names _ _ const_names => const_names end.
Notation "n .(var_names)" := (get_var_names_of_expr_names n) (at level 0).
Notation "n .(const_names)" := (get_const_names_of_expr_names n) (at level 0).

Definition expr_names_app (n1 n2: expr_names): expr_names :=
  Build_expr_names
    (type_names_app n1 n2)
    (n1.(var_names) ++ n2.(var_names))
    (n1.(const_names) ++ n2.(const_names)).

Fixpoint get_expr_names (t: type) (e: expr t): expr_names :=
  match e with
  | EVar i t =>
    Build_expr_names (get_type_names t) [i] []
  | EConst val t_params t_args t =>
    Build_expr_names (get_type_names (type_subst t_params t_args t)) [] [val]
  | EApp arg_type ret_type f arg =>
    expr_names_app (get_expr_names _ f) (get_expr_names _ arg)
  end.

Lemma type_names_include_refl: forall n,
  type_names_include n n.
Proof.
  intros.
  unfold type_names_include.
  repeat split; apply incl_refl.
Qed.

Lemma incl_trans: forall [A: Type] (l1 l2 l3: list A),
  incl l1 l2 -> incl l2 l3 -> incl l1 l3.
Proof.
  intros ? ? ? ? H12 H23.
  unfold incl in *.
  intros x Hin.
  apply H23, H12, Hin.
Qed.

Lemma type_names_include_trans: forall n1 n2 n3,
  type_names_include n1 n2 ->
  type_names_include n2 n3 ->
  type_names_include n1 n3.
Proof.
  intros ? ? ? H12 H23.
  unfold type_names_include in *.
  destruct H12 as [Ha [Hb Hc]].
  destruct H23 as [Ha' [Hb' Hc']].
  repeat split.
  - apply (incl_trans _ _ _ Ha Ha').
  - apply (incl_trans _ _ _ Hb Hb').
  - apply (incl_trans _ _ _ Hc Hc').
Qed.

Lemma type_names_include_app_l: forall n n1 n2,
  type_names_include n n1 ->
  type_names_include n (type_names_app n1 n2).
Proof.
  intros.
  unfold type_names_include in *.
  repeat split; apply incl_appl; tauto.
Qed.

Lemma type_names_include_app_r: forall n n1 n2,
  type_names_include n n2 ->
  type_names_include n (type_names_app n1 n2).
Proof.
  intros.
  unfold type_names_include in *.
  repeat split; apply incl_appr; tauto.
Qed.

Lemma tpolyapp_names_include: forall i t args,
  In t args -> type_names_include (get_type_names t) (get_type_names (TPolyApp i args)).
Proof.
  intros.
  simpl.
  induction args; simpl.
  + absurd (In t nil); auto.
  + destruct H.
    - subst.
      repeat split; apply incl_appr; simpl; apply incl_appl; apply incl_refl.
    - specialize (IHargs H).
      destruct IHargs as [H1 [H2 H3]]; simpl in *.
      repeat split; simpl.
      2-3: apply incl_appr; simpl; tauto.
      unfold incl. intros x Hin. specialize (H1 x Hin). simpl in *.
      destruct H1; [left; tauto | right].
      apply in_or_app. right. tauto.
Qed.

Lemma tarrow_names_include_arg: forall t1 t2,
  type_names_include (get_type_names t1) (get_type_names (TArrow t1 t2)).
Proof.
  intros.
  apply tpolyapp_names_include.
  simpl. tauto.
Qed.

Lemma tarrow_names_include_ret: forall t1 t2,
  type_names_include (get_type_names t2) (get_type_names (TArrow t1 t2)).
Proof.
  intros.
  apply tpolyapp_names_include.
  simpl. tauto.
Qed.

Lemma expr_names_include_type_names: forall t e,
  type_names_include (get_type_names t) (get_expr_names t e).
Proof.
  intros.
  induction e; simpl.
  + apply type_names_include_refl.
  + apply type_names_include_refl.
  + apply type_names_include_app_l.
    pose proof (tarrow_names_include_ret arg_type ret_type) as H.
    apply (type_names_include_trans _ _ _ H IHe1).
Qed.

Definition var_asgn (tJ: type_asgn): Type :=
  var_name -> forall t: type, option (teval tJ t).

Definition const_asgn (cptJ: const_ptype_asgn) (btJ: builtin_type_asgn): Type :=
  string -> forall (t_params: list var_type_name) (t: type) (t_args: list Type),
            option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t).

Definition vJ_list_type (tJ: type_asgn) : Type :=
  list (var_name * sigT (fun t: type => teval tJ t)).
Definition cJ_list_type (cptJ: const_ptype_asgn) (btJ: builtin_type_asgn) : Type :=
  list (string *
    sigT (fun t_params: list var_type_name =>
    sigT (fun t: type =>
      forall (t_args: list Type),
        option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t)))).

Inductive asgn_list : Type :=
  Build_asgn_list
    (tJ_list: type_asgn_list)
    (vJ_list: vJ_list_type (make_type_asgn_from_list tJ_list))
    (cJ_list: cJ_list_type (const_ptype_asgn.from_list tJ_list.(cpt_list)) (builtin_type_asgn.from_list tJ_list.(bt_list))).
Coercion get_type_asgn_list_of_asgn_list (l: asgn_list): type_asgn_list :=
  match l with Build_asgn_list tJ_list _ _ => tJ_list end.
Definition get_vJ_list_of_asgn_list (l: asgn_list)
    : vJ_list_type (make_type_asgn_from_list l) :=
  match l with Build_asgn_list _ vJ_list _ => vJ_list end.
Notation "l .(vJ_list)" := (get_vJ_list_of_asgn_list l) (at level 0).
Definition get_cJ_list_of_asgn_list (l: asgn_list)
    : cJ_list_type (const_ptype_asgn.from_list l.(cpt_list)) (builtin_type_asgn.from_list l.(bt_list)) :=
  match l with Build_asgn_list _ _ cJ_list => cJ_list end.
Notation "l .(cJ_list)" := (get_cJ_list_of_asgn_list l) (at level 0).


Definition var_asgn_upd [tJ: type_asgn] (J: var_asgn tJ)
    (i: var_name) [t: type] (v: teval tJ t): var_asgn tJ :=
  fun i' t' =>
    if var_name_eq_dec i i' then
      match type.eq_dec t t' with
      | left H => Some (eq_rect _ (teval tJ) v _ H)
      | right _ => J i' t'
      end
    else J i' t'.

Definition var_asgn_upd_list [tJ: type_asgn] (J: var_asgn tJ)
    (l: vJ_list_type tJ): var_asgn tJ :=
  fold_left (fun J0 p => var_asgn_upd J0 (fst p) (projT2 (snd p))) l J.

(* Definition var_asgn (tJ: type_asgn): Type :=
  var_name -> forall t: type, option (teval tJ t). *)
Definition var_asgn_eq [tJ: type_asgn] : Relation_Definitions.relation (var_asgn tJ) :=
  fun J1 J2 => forall i t, J1 i t = J2 i t.

#[export] Instance var_asgn_eq_refl [tJ: type_asgn]: Reflexive (@var_asgn_eq tJ).
Proof.
  unfold Reflexive, var_asgn_eq.
  intros J i t.
  reflexivity.
Qed.

#[export] Instance var_asgn_eq_sym [tJ: type_asgn]: Symmetric (@var_asgn_eq tJ).
Proof.
  unfold Symmetric, var_asgn_eq.
  intros J1 J2 H i t.
  symmetry. apply H.
Qed.

#[export] Instance var_asgn_eq_trans [tJ: type_asgn]: Transitive (@var_asgn_eq tJ).
Proof.
  unfold Transitive, var_asgn_eq.
  intros J1 J2 J3 H12 H23 i t.
  transitivity (J2 i t); auto.
Qed.

#[export] Instance var_asgn_upd_congr0 [tJ: type_asgn] :
  Proper (@var_asgn_eq tJ ==> eq ==>
            forall_relation (fun t: type => @eq (teval tJ t) ==> @var_asgn_eq tJ))
         (@var_asgn_upd tJ).
Proof.
  unfold Proper, respectful, var_asgn_eq, forall_relation.
  intros J1 J2 HJ i ? <- t v1 v2 <- i' t'.
  unfold var_asgn_upd.
  destruct (var_name_eq_dec i i'); simpl.
  + destruct (type.eq_dec t t'); simpl.
    - subst. reflexivity.
    - apply HJ.
  + apply HJ.
Qed.

#[export] Instance var_asgn_upd_list_congr0 [tJ: type_asgn] :
  Proper ((@var_asgn_eq tJ) ==> eq ==> (@var_asgn_eq tJ)) (@var_asgn_upd_list tJ).
Proof.
  unfold Proper, respectful, var_asgn_eq.
  intros J1 J2 HJ l l' <-.
  revert J1 J2 HJ. induction l; intros; simpl.
  + apply HJ.
  + destruct a as [i' [t' v']]. simpl.
    apply IHl. intros.
    apply var_asgn_upd_congr0; auto.
Qed.

Lemma var_asgn_upd_perm: forall [tJ: type_asgn] (J: var_asgn tJ) x y
  [t1] (v1: teval tJ t1) [t2] (v2: teval tJ t2),
  (x, t1) <> (y, t2) ->
  var_asgn_eq (var_asgn_upd (var_asgn_upd J x v1) y v2)
              (var_asgn_upd (var_asgn_upd J y v2) x v1).
Proof.
  intros.
  unfold f_eq, var_asgn_upd.
  intros i t.
  destruct (var_name_eq_dec x i), (var_name_eq_dec y i); try congruence.
  destruct (type.eq_dec t1 t), (type.eq_dec t2 t); try congruence.
Qed.

Definition name_type_In (i: var_name) (t: type) [tJ: type_asgn] (l: vJ_list_type tJ): Prop :=
  In (i, t) (map (fun p => (fst p, projT1 (snd p))) l).

Lemma upd_perm_list: forall [tJ: type_asgn] (J: var_asgn tJ) [t] x (v: teval tJ t) l,
  ~ name_type_In x t l ->
  var_asgn_eq (var_asgn_upd_list (var_asgn_upd J x v) l)
              (var_asgn_upd (var_asgn_upd_list J l) x v).
Proof.
  intros.
  revert J.
  induction l; intros; simpl.
  + reflexivity.
  + destruct a as [i [t' v']]. unfold name_type_In in H.
    simpl in *.
    assert ((x, t) <> (i, t')).
    { contradict H. simpl. left. auto. }
    assert (~ name_type_In x t l).
    { contradict H. simpl. right. auto. }
    rewrite var_asgn_upd_perm by congruence.
    rewrite IHl; auto.
    reflexivity.
Qed.







Definition const_asgn_upd [cptJ: const_ptype_asgn] [btJ: builtin_type_asgn]
    (cJ: const_asgn cptJ btJ) (i: string) (t_params: list var_type_name) (t: type)
    (v: forall t_args : list Type, option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t))
    : const_asgn cptJ btJ.
  intros i0 t_params0 t0 t_args0.
  destruct (string_dec i0 i). 2: exact (cJ i0 t_params0 t0 t_args0).
  destruct (list_eq_dec var_type_name_eq_dec t_params t_params0) as [t_params_eq | _]. 2: exact None.
  destruct (type.eq_dec t t0) as [t_eq | _]. 2: exact None.
  specialize (v t_args0).
  pose (eq_rect _ (fun t_params => option (teval (_ _ _ (Build_vtJ t_params  t_args0)) t)) v   _ t_params_eq) as tmp.
  pose (eq_rect _ (fun t        => option (teval (_ _ _ (Build_vtJ t_params0 t_args0)) t)) tmp _ t_eq) as tmp2.
  exact tmp2.
Defined.
(* Print const_asgn_upd. *)

Definition const_asgn_upd_list [cptJ: const_ptype_asgn] [btJ: builtin_type_asgn]
    (cJ: const_asgn cptJ btJ) (l: cJ_list_type cptJ btJ) : const_asgn cptJ btJ :=
  fold_left (fun cJ0 p =>
    let '(i, (t_params, (t, f))) := p in
    const_asgn_upd cJ0 i t_params t f) l cJ.



Inductive asgn: Type := Build_asgn
  (tJ: type_asgn)
  (vJ: var_asgn tJ)
  (cJ: const_asgn tJ.(cpt) tJ.(bt)).

Definition get_tJ_of_asgn (a: asgn) : type_asgn :=
  match a with
  | Build_asgn tJ _ _ => tJ
  end.
Coercion get_tJ_of_asgn: asgn >-> type_asgn.
Definition get_vJ_of_asgn (a: asgn) : var_asgn a :=
  match a with
  | Build_asgn _ vJ _ => vJ
  end.
Notation "a .(vJ)" := (get_vJ_of_asgn a) (at level 0).
Definition get_cJ_of_asgn (a: asgn) : const_asgn a.(cpt) a.(bt) :=
  match a with
  | Build_asgn _ _ cJ => cJ
  end.
Notation "a .(cJ)" := (get_cJ_of_asgn a) (at level 0).


(* Record asgn_list : Type := {
  tJ:> type_asgn_list;
  vJ_list: list (var_name * forall t: type, option (teval (make_type_asgn_from_list tJ) t));
  cJ_list: list (string * forall (t_params: list var_type_name) (t: type) (t_args: list Type),
                          option (teval (make_type_asgn_from_list tJ) t))
}. *)




Definition make_var_asgn_from_list [tJ_list] (vJ_list: vJ_list_type tJ_list)
    : var_asgn (make_type_asgn_from_list tJ_list) :=
  fun i t =>
    match find (fun p => var_name_eq_dec (fst p) i) vJ_list with
    | Some (_, v) =>
      match type.eq_dec (projT1 v) t with
      | left H => Some (eq_rect _ (fun t => teval (make_type_asgn_from_list tJ_list) t) (projT2 v) _ H)
      | right _ => None
      end
    | None => None
    end.

Definition make_const_asgn_from_list [tJ_list] (cJ_list: cJ_list_type tJ_list)
    : const_asgn (make_type_asgn_from_list tJ_list).(cpt)
                 (make_type_asgn_from_list tJ_list).(bt) :=
  fun i t_params t t_args =>
    match find (fun p => string_dec (fst p) i) cJ_list with
    | Some (_, f) => f t_params t t_args
    | None => None
    end.

Definition make_asgn_from_list (l: asgn_list): asgn :=
  Build_asgn
    (make_type_asgn_from_list l)
    (make_var_asgn_from_list l.(vJ_list))
    (make_const_asgn_from_list l.(cJ_list)).

Definition asgn_list_nodup (l: asgn_list): Prop :=
  type_asgn_list_nodup l /\
  NoDup (map fst l.(vJ_list)) /\
  NoDup (map fst l.(cJ_list)).

Definition vJ_list_incl [tl1 tl2: type_asgn_list]
    (vl1: vJ_list_type tl1) (vl2: vJ_list_type tl2): Prop :=
  forall i v1, In (i, v1) vl1 ->
    exists v2, eq_dep _ (fun x => x) _ v1 _ v2 /\
               In (i, v2) vl2.

Definition cJ_list_incl [tl1 tl2: type_asgn_list]
    (cl1: cJ_list_type tl1) (cl2: cJ_list_type tl2): Prop :=
  forall i v1, In (i, v1) cl1 ->
    exists v2, eq_dep _ (fun x => x) _ v1 _ v2 /\
               In (i, v2) cl2.

Definition asgn_list_incl (l1 l2: asgn_list): Prop :=
  type_asgn_list_incl l1 l2 /\
  vJ_list_incl l1.(vJ_list) l2.(vJ_list) /\
  cJ_list_incl l1.(cJ_list) l2.(cJ_list).

Definition get_names_from_asgn_list (l: asgn_list): expr_names :=
  Build_expr_names
    (get_type_names_from_type_asgn_list l)
    (map fst l.(vJ_list)) (map fst l.(cJ_list)).


Definition eeval (J: asgn)
    : forall t: type, expr t -> option (teval J t) :=
  fix eeval (t: type) (e: expr t) :=
    match e as e0 in expr t0 return option (teval J t0) with
    | EVar i t1 => J.(vJ) i t1
    | EConst val t_params t_args t1 =>
        let t_args_val := map (teval J) t_args in
        do res <- J.(cJ) val t_params t1 t_args_val;
        Some (eq_rect _ (fun x => x) res _ (type_subst_sound _ _ _ _))
    | EApp arg_type ret_type f arg_expr =>
        do f_val <- eeval (TArrow arg_type ret_type) f;
        do arg_val <- eeval arg_type arg_expr;
        Some (f_val arg_val)
    end.




Definition asgn_coincide_on_names (J1 J2: asgn) (n: expr_names) : Prop :=
  type_asgn_coincide_on_names J1 J2 n /\
  (forall i t,
    type_names_include (get_type_names t) n ->
    In i n.(var_names) ->
    eq_dep _ (fun x => x) _ (J1.(vJ) i t) _ (J2.(vJ) i t)) /\
  (forall i t_params t t_args,
    type_names_include (get_type_names (type_subst t_params t_args t)) n ->
    In i n.(const_names) ->
    let t_args_val1 := map (teval J1) t_args in
    let t_args_val2 := map (teval J2) t_args in
    eq_dep _ (fun x => x)
           _ (J1.(cJ) i t_params t t_args_val1) _ (J2.(cJ) i t_params t t_args_val2)).

Lemma eapp_asgn_coincide_on_subexpr: forall [J1 J2 arg_type ret_type f arg],
  asgn_coincide_on_names J1 J2 (get_expr_names _ (EApp arg_type ret_type f arg)) ->
  asgn_coincide_on_names J1 J2 (get_expr_names _ f) /\
  asgn_coincide_on_names J1 J2 (get_expr_names _ arg).
Proof.
  intros.
  unfold asgn_coincide_on_names in *.
  destruct H as [Ht [Hv Hc]].
  split.
  + repeat split; intros.
    1-3: apply Ht; simpl; apply in_or_app; left; tauto.
    - apply Hv.
      ++ apply type_names_include_app_l. tauto.
      ++ simpl. apply in_or_app. left. tauto.
    - apply Hc.
      ++ apply type_names_include_app_l. tauto.
      ++ simpl. apply in_or_app. left. tauto.
  + repeat split; intros.
    1-3: apply Ht; simpl; apply in_or_app; right; tauto.
    - apply Hv.
      ++ apply type_names_include_app_r. tauto.
      ++ simpl. apply in_or_app. right. tauto.
    - apply Hc.
      ++ apply type_names_include_app_r. tauto.
      ++ simpl. apply in_or_app. right. tauto.
Qed.

(* Reference From StdLib: *)
(* Lemma f_eq_dep :
  forall U (P:U->Type) R p q x y (f:forall p, P p -> R p),
    eq_dep U P p x q y -> eq_dep U R p (f p x) q (f q y).
Proof.
  intros *.
  intros [].
  reflexivity.
Qed. *)

Lemma f2_eq_dep :
  forall [U] [P1 P2: U -> Type] [R p q x1 x2 y1 y2] (f: forall p, P1 p -> P2 p -> R p),
    eq_dep U P1 p x1 q y1 -> eq_dep U P2 p x2 q y2 -> eq_dep U R p (f p x1 x2) q (f q y1 y2).
Proof.
  intros *.
  intros H1 H2.
  destruct H1.
  apply eq_dep_eq in H2.
  rewrite H2.
  reflexivity.
Qed.





Lemma eq_dep_lem1 A B A' B' x y (HA: A = A') (HB: B = B'):
  eq_dep Type (fun x => x) (option A) x (option B) y ->
  eq_dep Type (fun x => x)
         (option A') (do a <- x; Some (eq_rect A (fun x => x) a A' HA))
         (option B') (do b <- y; Some (eq_rect B (fun x => x) b B' HB)).
Proof.
  intro H.
  subst A' B'.
  destruct x, y; assumption.
Qed.




Lemma eq_dep_lem3 [A B C D] (H1: A = B) (H2: C = D)
    (f: option (A -> C)) (g: option (B -> D))
    (x: option A) (y: option B):
  let func := fun [A C] (f: option(A -> C)) (x: option A) =>
    do fv <- f; do a <- x; Some (fv a) in
  eq_dep Type (fun x => x) _ f _ g ->
  eq_dep Type (fun x => x) _ x _ y ->
  eq_dep Type (fun x => x)
         _ (func f x) _ (func g y).
Proof.
  subst.
  intros * H1 H2.
  generalize (@func B D). clear func.
  revert f g x y H1 H2.
  generalize (option (B -> D)).
  generalize (option B).
  generalize (option D).
  clear B D.
  intros.
  apply eq_dep_eq in H1, H2.
  rewrite H1, H2. reflexivity.
Qed.

Lemma eeval_coincide_aux: forall (J1 J2 : asgn) t (e: expr t),
  asgn_coincide_on_names J1 J2 (get_expr_names _ e) ->
  teval J1 t = teval J2 t.
Proof.
  intros.
  apply teval_coincide with (J1 := J1) (J2 := J2).
  unfold asgn_coincide_on_names in H. simpl in H. destruct H as [H _].
  induction e; simpl in *; try tauto.
  + apply type_names_include_coincide with (n2 := get_expr_names _ e1).
    - pose proof tarrow_names_include_ret arg_type ret_type as Ht.
      apply (type_names_include_trans _ _ _ Ht).
      apply expr_names_include_type_names.
    - apply type_asgn_coincide_app_l in H. apply H.
Qed.

Theorem eeval_coincide: forall (J1 J2 : asgn) t (e: expr t),
  asgn_coincide_on_names J1 J2 (get_expr_names _ e) ->
  eq_dep _ (fun x => x)
         _ (eeval J1 t e) _ (eeval J2 t e).
Proof.
  intros.
  induction e; simpl.
  + destruct H as [Ht [Hv Hc]].
    apply Hv; simpl; auto.
    apply type_names_include_refl.
  + destruct H as [Ht [Hv Hc]].
    specialize (Hc val t_params t t_args (type_names_include_refl _)).
    assert (Htmp: val = val \/ False) by auto. specialize (Hc Htmp). clear Htmp.
    apply eq_dep_lem1. exact Hc.
  + destruct (eapp_asgn_coincide_on_subexpr H) as [He1_co He2_co].
    specialize (IHe1 He1_co).
    specialize (IHe2 He2_co).
    (* pose proof eeval_coincide_aux _ _ _ e1 He1_co as Ht1eq. *)
    pose proof eeval_coincide_aux _ _ _ e2 He2_co as Ht2eq.
    pose proof eeval_coincide_aux _ _ _ (EApp _ _ e1 e2) H as Hteq.
    apply (eq_dep_lem3 Ht2eq Hteq); auto.
Qed.




Theorem asgn_include_coincide: forall (l1 l2: asgn_list),
  asgn_list_nodup l1 -> asgn_list_nodup l2 ->
  asgn_list_incl l1 l2 ->
  let tJ1 := make_asgn_from_list l1 in
  let tJ2 := make_asgn_from_list l2 in
  let tn1 := get_names_from_asgn_list l1 in
  asgn_coincide_on_names tJ1 tJ2 tn1.
Proof.
  intros l1 l2 Hnodup1 Hnodup2 Hinc J1 J2 n1.
  repeat split.
  1-3: destruct Hnodup1 as [Hnodup1 _], Hnodup2 as [Hnodup2 _];
       destruct Hinc as [Hinc _];
       apply type_asgn_include_coincide with (l1 := l1) (l2 := l2); auto.
  + intros i t Ht Hin.
    destruct Hinc as [_ [Hinc _]]. specialize (Hinc i).
    destruct Hnodup1 as [_ [Hnodup1 _]], Hnodup2 as [_ [Hnodup2 _]].
  












(* Definition asgn_coincide_on_names (J1 J2: asgn) (n: expr_names) : Prop.
  refine (type_asgn_coincide_on_names J1 J2 n /\ (forall Het: type_asgn_coincide_on_names J1 J2 n, _ /\ _) : Prop).
  + refine (forall i t (Ht_incl: type_names_include (get_type_names t) n), In i n.(var_names) ->
                   (eq_rect _ (fun x => x) (J1.(vJ) i t) _ _) = J2.(vJ) i t).
    f_equal.
    apply teval_coincide.
    apply (type_names_include_coincide _ _ _ _ Ht_incl Het).
  + refine (forall i t_params t t_args (Ht_incl: type_names_include (get_type_names t) n), In i n.(const_names) ->
                   (eq_rect _ (fun x => x) (J1.(cJ) i t_params t t_args) _ _) = J2.(cJ) i t_params t t_args).
    f_equal.
    apply teval'_coincide with
      (J1 := Build_type_asgn J1.(cpt) J1.(bt) (Build_vtJ t_params t_args))
      (J2 := Build_type_asgn J2.(cpt) J2.(bt) (Build_vtJ t_params t_args)).
    unfold type_asgn_coincide_on_names in *.
    destruct Het as [Hcpt [Hbt Hvt]].
    destruct Ht_incl as [Hcpt' [Hbt' Hvt']].
    repeat split; intro; simpl; auto.
Defined.

(* Print asgn_coincide_on_names. *)


Lemma eeval'_coincide_aux: forall (J1 J2 : asgn) t (e: expr t),
  asgn_coincide_on_names J1 J2 (get_expr_names _ e) ->
  teval' J1 t = teval' J2 t.
Proof.
  intros.
  apply teval'_coincide with (J1 := J1) (J2 := J2).
  unfold asgn_coincide_on_names in H. simpl in H. destruct H as [H _].
  induction e; simpl in *; try tauto.
  + apply type_names_include_coincide with (n2 := get_expr_names _ e1).
    - pose proof tarrow_names_include_ret arg_type ret_type as Ht.
      apply (type_names_include_trans _ _ _ Ht).
      apply expr_names_include_type_names.
    - apply type_asgn_coincide_app_l in H. apply H.
Defined.

Lemma eeval'_coincide_aux2: forall (J1 J2 : asgn) t (e: expr t),
  asgn_coincide_on_names J1 J2 (get_expr_names _ e) ->
  option (teval' J1 t) = option (teval' J2 t).
Proof.
  intros.
  apply f_equal.
  apply (eeval'_coincide_aux J1 J2 t e H).
Defined.

Theorem eeval'_coincide: forall (J1 J2 : asgn) t (e: expr t)
  (pf: asgn_coincide_on_names J1 J2 (get_expr_names _ e)),
  forall (Heq: option (teval' J1 t) = option (teval' J2 t)),
  eq_dep _ (fun x => x) _ (eeval' J1 t e) _ (eeval' J2 t e).
  (* eq_rect _ (fun x => x) (eeval' J1 _ e) _ (Heq) = eeval' J2 _ e. *)
  (* eq_rect _ (fun x => x) (eeval' J1 _ e) _ (eeval'_coincide_aux2 J1 J2 t e pf) = eeval' J2 _ e. *)
Proof.
  intros.
  induction e; simpl in *.
  + destruct pf as [Ht Ha]. pose proof (Ha Ht) as Ha'. destruct Ha' as [Hv _].
    specialize (Hv i t). simpl in Hv.
    Admitted. *)



(* Definition asgn_subset (a1 a2: asgn): Prop :=
  const_ptype_asgn_subset a1.(cptJ) a2.(cptJ) /\
  builtin_type_asgn_subset a1.(btJ) a2.(btJ) /\
  var_type_asgn_subset a1.(vtJ) a2.(vtJ) /\
  (forall i t, a1.(vJ) i t <> None -> a1.(vJ) i t = a2.(vJ) i t) /\
  (forall i t_params t t_args, a1.(cJ) i t_params t t_args <> None -> a1.(cJ) i t_params t t_args = a2.(cJ) i t_params t t_args). *)








Notation "'wrap_const_ptype_1' f" :=
  (fun ts : list Type => match ts return Type with
                        | cons A nil => f A
                        | _ => unit
                        end)
  (at level 200).
Notation "'wrap_const_ptype_2' f" :=
  (fun ts : list Type => match ts return Type with
                        | cons A1 (cons A2 nil) => f A1 A2
                        | _ => unit
                        end)
  (at level 200).

Example empty_cptJ: const_ptype_asgn := fun _ _ => unit.
Example cpt_list1: list (const_ptype_name * (list Type -> Type)) :=
  [("list", wrap_const_ptype_1 list)].
Lemma cpt_list1_no_dup: NoDup (map fst cpt_list1).
Proof.
  simpl. apply NoDup_cons; auto. constructor.
Qed.
Example cpt_list2 :=
  app cpt_list1 [
    ("prod", wrap_const_ptype_2 prod);
    ("a", fun _ => unit : Type);
    ("b", fun _ => unit : Type)
  ].
Lemma cpt_list2_no_dup: NoDup (map fst cpt_list2).
Proof.
  simpl.
  repeat constructor; simpl; auto.
  all: assert (Hfalse: forall P : Prop, P \/ False <-> P) by tauto; rewrite Hfalse.
  all: intro H; smart_destruct H; congruence.
Qed.
Example cptJ_builtin: const_ptype_asgn := const_ptype_asgn_upd_list empty_cptJ cpt_list1.
Example cptJ: const_ptype_asgn := const_ptype_asgn_upd_list empty_cptJ cpt_list2.
Lemma cptJ_include_builtin: forall i f, In (i, f) cpt_list1 -> cptJ i = f.
Proof.
  intros.
  assert (Hin: In (i, f) cpt_list2).
  { unfold cpt_list2. apply in_or_app. left. tauto. }
  unfold cptJ_builtin.
  apply const_ptype_asgn_upd_list_no_dup; auto.
  apply cpt_list2_no_dup.
Qed.


Example btJ: builtin_type_asgn := fun i =>
  match i with
  | "Z" => Z
  | _ => unit
  end.

Example tJ := Build_type_asgn cptJ btJ (fun _ => unit).
Example tJ_builtin := Build_type_asgn cptJ_builtin btJ (fun _ => unit).

Example list_A := TPolyApp "list" [TVar "A"].
Example nil_type := list_A.
Example cons_type := (TArrow (TVar "A") (TArrow list_A list_A)).


Notation "'wrap_poly_fn_0' f" :=
  (fun ts : list Type => match ts with
                        | nil => Some f
                        | _ => None
                        end)
  (at level 200).
Notation "'wrap_poly_fn_1' f" :=
  (fun ts : list Type => match ts with
                        | cons A nil => Some (f A)
                        | _ => None
                        end)
  (at level 200).
Notation "'wrap_poly_fn_2' f" :=
  (fun ts : list Type => match ts with
                        | cons A1 (cons A2 nil) => Some (f A1 A2)
                        | _ => None
                        end)
  (at level 200).

Example empty_cJ: const_asgn cptJ btJ := fun _ _ _ _ => None.
Example cJ' := const_asgn_upd _ _ empty_cJ
    "nil" ["A"] nil_type (wrap_poly_fn_1 @nil).
Example cJ := const_asgn_upd _ _ cJ'
    "cons" ["A"] cons_type (wrap_poly_fn_1 @cons).
Example empty_cJ_builtin: const_asgn cptJ_builtin btJ := fun _ _ _ _ => None.
Example cJ_builtin :=
    const_asgn_upd _ _ empty_cJ_builtin
    "cons" ["A"] cons_type (wrap_poly_fn_1 @cons).
(* Example cJ :=
    let Z_type := TBuiltin "Z" in
    const_asgn_upd _ _ cJ2
    "Z.add" nil (TArrow Z_type (TArrow Z_type Z_type)) (wrap_poly_fn_0 Z.add). *)

Example J_builtin := Build_asgn tJ_builtin (fun _ _ => None) cJ_builtin.
Example J := Build_asgn tJ (fun _ _ => None) cJ.

Example cons_expr := EConst "cons" ["A"] [TBuiltin "Z"] cons_type.
Lemma cons_expr_eval_correct : forall vtJ vJ,
  eeval (Build_asgn (Build_type_asgn cptJ btJ vtJ) vJ cJ) _ cons_expr = Some (@cons Z).
Proof.
  simpl. intros. rewrite <- !EqdepTheory.eq_rect_eq. reflexivity.
Qed.

Example nil_expr := EConst "nil" ["A"] [TBuiltin "Z"] nil_type.
Lemma nil_expr_eval_correct : forall vtJ vJ,
  eeval (Build_asgn (Build_type_asgn cptJ btJ vtJ) vJ cJ) _ nil_expr = Some (@nil Z).
Proof.
  simpl. intros. rewrite <- !EqdepTheory.eq_rect_eq. reflexivity.
Qed.

Example x_expr := EVar "x" (TBuiltin "Z").
Example a_list_expr := EApp _ _ (EApp _ _ cons_expr x_expr) nil_expr.

Example builtin_expr_names : expr_names :=
  Build_expr_names (Build_type_names ["list"] [] [])
                   []
                   ["nil"; "cons"].

Lemma J_J_builtin_coincide: asgn_coincide_on_names J J_builtin (get_expr_names _ cons_expr).
Proof.
  unfold asgn_coincide_on_names.
  assert (Htmp: forall P Q: Prop, P /\ (P -> Q) -> P /\ Q) by tauto.
  apply Htmp; clear Htmp.
  split.
  + repeat split; intros.
    simpl in H.
    smart_destruct H; subst; simpl; auto.
    destruct H.
  + repeat split; intros; simpl in *.
    - easy.
    - destruct H1; [| easy]. subst.
      pose proof type_names_include_coincide _ _ _ _ H0 H.
      pose proof teval_coincide _ _ _ H1.
      rewrite <- !type_subst_sound in H2.
      (* assert (Hteq: option (teval (subst_vt tJ t_params t_args) t) =
                    option (teval (subst_vt tJ_builtin t_params t_args) t)).
      { f_equal.
        rewrite !type_subst_sound. apply teval_coincide.
        apply (type_names_include_coincide _ _ _ _ H0 H). } *)
      (* apply eq_dep1_dep. apply eq_dep1_intro with (h := Hteq). *)
      unfold cJ, cJ_builtin, const_asgn_upd.
      destruct (string_dec "cons" "cons"); [| easy].
      destruct (list_eq_dec var_type_name_eq_dec ["A"] t_params).
      destruct (type.eq_dec cons_type t).
      all: subst; simpl; try reflexivity.
      all: unfold add_builtin_ptype; simpl.
    reflexivity.
    - reflexivity.

Lemma expr_coincide: forall J t (e: expr t),
  asgn_coincide_on_names J J_builtin (get_expr_names _ e) ->
  (* eeval' J _ e = eeval' J_builtin _ e. *)
  eq_dep _ (fun x => x) _ (eeval' J _ e) _ (eeval' J_builtin _ e).
Proof.
  intros J t e Hco.
  pose proof eeval'_coincide_aux2 J J_builtin _ e Hco as Hteq.
  apply (eeval'_coincide J J_builtin _ e Hco Hteq).
Defined.

Lemma cons_expr_coincide: forall J (x: Z),
  asgn_coincide_on_names J J_builtin (get_expr_names _ cons_expr) ->
  eq_dep _ (fun x => x) _ (eeval' J _ cons_expr) _ (Some (@cons Z)).
Proof.
  intros J x Hco.
  pose proof (expr_coincide J _ cons_expr Hco).
  apply (eq_dep_trans _ _ _ _ _ _ _ _ H).
  simpl.
  rewrite <- !EqdepTheory.eq_rect_eq. reflexivity.
Qed.


Lemma a_list_expr_eval_correct : forall vtJ vJ x,
  let J := Build_asgn (Build_type_asgn cptJ btJ vtJ) vJ cJ in
  eeval' J _ x_expr = Some x ->
  eeval' J _ a_list_expr = Some (@cons Z x nil).
Proof.
  simpl.
  intros.
  rewrite <- !EqdepTheory.eq_rect_eq.
  rewrite H.
  reflexivity.
Qed.



(* Inductive unary_operation : Type :=
  | Oneg : unary_operation              (**r opposite (unary [-]) *)
  | Onint : unary_operation             (**r unary [~] *)
  | Onot : unary_operation              (**r unary [!] *)
.

Definition get_unary_op_ident (op : unary_operation) : ident :=
  match op with
  | Oneg  => 10001%positive
  | Onint => 10002%positive
  | Onot  => 10003%positive
  end.

Inductive binary_operation : Type :=
  | Oadd : binary_operation             (**r addition (binary [+]) *)
  | Osub : binary_operation             (**r subtraction (binary [-]) *)
  | Omul : binary_operation             (**r multiplication (binary [*]) *)
  | Odiv : binary_operation             (**r division ([/]) *)
  | Omod : binary_operation             (**r remainder ([%]) *)
  | Oand : binary_operation             (**r bitwise and ([&]) *)
  | Oor : binary_operation              (**r bitwise or ([|]) *)
  | Oxor : binary_operation             (**r bitwise xor ([^]) *)
  | Oshl : binary_operation             (**r left shift ([<<]) *)
  | Oshr : binary_operation             (**r right shift ([>>]) *)
.

Definition get_binary_op_ident (op : binary_operation) : ident :=
  match op with
  | Oadd => 20001%positive
  | Osub => 20002%positive
  | Omul => 20003%positive
  | Odiv => 20004%positive
  | Omod => 20005%positive
  | Oand => 20006%positive
  | Oor  => 20007%positive
  | Oxor => 20008%positive
  | Oshl => 20009%positive
  | Oshr => 20010%positive
  end.



(* Use Z to represent the type of the expression. *)
(* 0 : Z, 1 : string, 2 : bool *)

Definition Ctype_to_expr_type (t : SimpleCtype) : Z :=
  match t with
  | CT_basic _ => 0
  | CT_pointer _ => 0
  | CT_array _ _ => 0
  | _ => -1
  end.

Inductive FuncSig : Type :=
| FSig (args : list Z) (ret : Z)
.

Module FuncSig <: UsualBoolEq.
  Definition t := FuncSig.
  Definition eq := @Logic.eq FuncSig.
  Definition eqb (x y : t) : bool :=
    match x, y with
    | FSig args1 ret1, FSig args2 ret2 =>
        andb (list_eqb Z.eqb args1 args2) (Z.eqb ret1 ret2)
    end.
  Lemma eqb_eq : forall x y : t, eqb x y = true <-> x = y.
  Proof.
    intros x y.
    destruct x as [args1 ret1], y as [args2 ret2]; simpl.
    rewrite andb_true_iff.
    rewrite list_eqb_eq with (eqb_eq := Z.eqb_eq).
    rewrite Z.eqb_eq.
    split; intros.
    - destruct H as [? ?]. subst; reflexivity.
    - injection H. tauto.
  Qed.
  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.
End FuncSig.

Inductive PredSig : Type :=
| PSig (args : list Z)
.

Module PredSig <: UsualBoolEq.
  Definition t := PredSig.
  Definition eq := @Logic.eq PredSig.
  Definition eqb (x y : t) : bool :=
    match x, y with
    | PSig args1, PSig args2 =>
        list_eqb Z.eqb args1 args2
    end.
  Lemma eqb_eq : forall x y : t, eqb x y = true <-> x = y.
  Proof.
    intros x y.
    destruct x as [args1], y as [args2]; simpl.
    rewrite list_eqb_eq with (eqb_eq := Z.eqb_eq).
    split; intros.
    - subst; reflexivity.
    - injection H; tauto.
  Qed.
  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.
End PredSig.

Definition get_func_sig_args (f : FuncSig) :=
  match f with
  | FSig args _ => args
  end.

Definition get_func_sig_ret (f : FuncSig) :=
  match f with
  | FSig _ ret => ret
  end.

Definition get_pred_sig_args (f : PredSig) :=
  match f with
  | PSig args => args
  end.

Definition FuncSig_eqb (s1 s2 : FuncSig) : bool :=
  match s1, s2 with
  | FSig args1 ret1, FSig args2 ret2 =>
      andb (list_eqb Z.eqb args1 args2) (Z.eqb ret1 ret2)
  end.


Inductive expr_val : Z -> Type :=
  | EConstZ (val : Z) : expr_val 0  (** const *)
  | EVar (var_id : ident) (type : Z) : expr_val type
  | EField (addr : expr_val 0) (struct_id field_id : ident) : expr_val 0
  | EFunc (f : ident) (sig : FuncSig) (args : Induct.dlist expr_val (get_func_sig_args sig))
      : expr_val (get_func_sig_ret sig)
.

Definition expr_val_ind2
    (P : forall ty, expr_val ty -> Prop)
    (Q : forall l, Induct.dlist expr_val l -> Prop)
    (H_EVar : forall x ty, P ty (EVar x ty))
    (H_EConstZ : forall val, P 0%Z (EConstZ val))
    (H_EField : forall addr struct_id field_id, P 0%Z addr -> P 0%Z (EField addr struct_id field_id))
    (H_EFunc : forall f sig args, Q _ args -> P _ (EFunc f sig args))
    (H_dnil : Q _ (Induct.dnil _))
    (H_dcons : forall x xs Px Pxs, P x Px -> Q xs Pxs -> Q _ (Induct.dcons _ x Px Pxs)) :
    forall ty e, P ty e :=
  fix expr_val_ind2 ty e : P ty e :=
  match e as e0 in expr_val ty0 return P ty0 e0 with
  | EVar x ty => H_EVar x ty
  | EConstZ val => H_EConstZ val
  | EField addr struct_id field_id =>
      H_EField addr struct_id field_id (expr_val_ind2 0%Z addr)
  | EFunc f sig args =>
      H_EFunc f sig args
          ((fix dlist_ind l d : Q l d :=
              match d as d0 in @Induct.dlist _ _ l0 return Q l0 d0 with
              | Induct.dnil => H_dnil
              | Induct.dcons x Px xs Pxs => H_dcons x xs Px Pxs (expr_val_ind2 x Px) (dlist_ind xs Pxs)
              end) _ args)
  end.

Definition expr_val_cast {ty : Z}
    (e : expr_val ty) {new_ty : Z} (pf : ty = new_ty) : expr_val new_ty :=
  eq_rect ty (fun ty => expr_val ty) e new_ty pf.

Definition expr_val_list : list Z -> Type := Induct.dlist expr_val.
Definition expr_val_list_nil : expr_val_list nil := Induct.dnil expr_val.
Definition expr_val_list_cons
    {t: Z} (v: expr_val t) {ts: list Z} (vs: expr_val_list ts) : expr_val_list (t :: ts) :=
  Induct.dcons expr_val t v vs.

Definition expr_val_list_cast {l : list Z}
    (dl : expr_val_list l) {new_l : list Z} (pf : l = new_l) : expr_val_list new_l :=
  eq_rect l (fun l => expr_val_list l) dl new_l pf.

Definition nullptr := EConstZ 0.
Definition Vtrue := EConstZ 1.
Definition Vfalse := EConstZ 0.

Definition unary_op_sig : FuncSig := FSig (cons 0 nil) 0.
Definition binary_op_sig : FuncSig := FSig (cons 0 (cons 0 nil)) 0.
Definition unary_op_expr (op : unary_operation) (a : expr_val 0) : expr_val 0 :=
  EFunc (get_unary_op_ident op) unary_op_sig
    (expr_val_list_cons a expr_val_list_nil).
Definition binary_op_expr (op : binary_operation) (a b : expr_val 0) : expr_val 0 :=
  EFunc (get_binary_op_ident op) binary_op_sig
    (expr_val_list_cons a (expr_val_list_cons b expr_val_list_nil)).

(** Below is an example of using the above definitions. *)
(** [age; name] is an expr_val_list of type [0; 1], i.e., [Z; string]. *)

(* Section expr_val_list_example.
Import ListNotations.
Definition age :  expr_val 0 := EConstZ 18.
Definition name : expr_val 1 := EVar 10032%positive 1.
Check expr_val_list_cons age (
      expr_val_list_cons name expr_val_list_nil)
  : expr_val_list [0; 1].
End expr_val_list_example. *)


Fixpoint expr_val_eqb {ty1 ty2 : Z} (e1 : expr_val ty1) (e2 : expr_val ty2) : bool :=
  Z.eqb ty1 ty2 &&
  match e1, e2 with
  | EVar x1 ty1, EVar x2 ty2 => ident_eqb x1 x2
  | EConstZ val1, EConstZ val2 => Z.eqb val1 val2
  | EField addr1 struct_id1 field_id1, EField addr2 struct_id2 field_id2 =>
      ident_eqb struct_id1 struct_id2 && ident_eqb field_id1 field_id2 && expr_val_eqb addr1 addr2
  | EFunc f1 sig1 args1, EFunc f2 sig2 args2 =>
      ident_eqb f1 f2 && FuncSig_eqb sig1 sig2 &&
      Induct.dlist_eqb Z.eqb (@expr_val_eqb) args1 args2
  | _, _ => false
  end.

Definition expr_val_list_eqb {l1 l2 : list Z}
  (dl1 : expr_val_list l1) (dl2 : expr_val_list l2) : bool :=
  Induct.dlist_eqb Z.eqb (@expr_val_eqb) dl1 dl2.

Lemma expr_val_eqb_refl :
  forall ty (e : expr_val ty), expr_val_eqb e e = true.
  intros.
  pose (Q := (fun l1 (dl1: Induct.dlist _ l1) =>
    expr_val_list_eqb dl1 dl1 = true)).
  induction e using expr_val_ind2 with (Q := Q).
  all: simpl.
  all: repeat (try apply andb_true_iff; try split).
  all: try apply ident_eqb_refl; try apply Z.eqb_refl.
  all: try tauto.
  apply FuncSig.eqb_refl.
Qed.

Lemma expr_val_eqb_true :
  forall ty1 ty2 (e1 : expr_val ty1) (e2 : expr_val ty2),
      expr_val_eqb e1 e2 = true ->
      (forall (pf : ty1 = ty2), eq_rect _ _ e1 _ pf = e2).
  pose (Q := (fun l1 dl1 => forall l2 dl2,
    expr_val_list_eqb dl1 dl2 = true ->
    (forall (pf : l1 = l2), eq_rect _ _ dl1 _ pf = dl2))).
  intros ty1 ty2 e1.
  revert dependent ty2.
  induction e1 using expr_val_ind2 with (Q := Q).
  all: intros; try destruct e2; try simpl in H; try discriminate.
  all: try rewrite! andb_true_iff in H; try (destruct H; discriminate).
  all: try rewrite! Z.eqb_eq in *; try rewrite! ident_eqb_eq in *.
  - destruct H. subst.
    rewrite <- EqdepTheory.eq_rect_eq. reflexivity.
  - subst.
    rewrite <- EqdepTheory.eq_rect_eq; reflexivity.
  - destruct H as [[? ?] H]. subst.
    rewrite <- EqdepTheory.eq_rect_eq.
    specialize (IHe1 _ _ H eq_refl).
    subst.
    rewrite <- EqdepTheory.eq_rect_eq.
    reflexivity.
  - destruct H as [H1 [[H2 H3] H4]]. subst.
    apply FuncSig.eqb_eq in H3.
    subst.
    rewrite <- EqdepTheory.eq_rect_eq.
    unfold Q in IHe1.
    specialize (IHe1 _ _ H4 eq_refl).
    rewrite <- EqdepTheory.eq_rect_eq in IHe1.
    subst. reflexivity.
  - unfold Q; intros.
    destruct dl2; try discriminate.
    rewrite <- EqdepTheory.eq_rect_eq.
    reflexivity.
  - unfold Q; intros.
    destruct dl2; try discriminate.
    injection pf as ?; subst.
    rewrite <- EqdepTheory.eq_rect_eq.
    simpl in H.
    rewrite! andb_true_iff in H. destruct H. destruct H.
    specialize (IHe1 _ x0 H1 eq_refl).
    rewrite <- EqdepTheory.eq_rect_eq in IHe1.
    subst.
    unfold Q in IHe0.
    specialize (IHe0 _ _ H0 eq_refl).
    rewrite <- EqdepTheory.eq_rect_eq in IHe0.
    subst; reflexivity.
Qed. *)
