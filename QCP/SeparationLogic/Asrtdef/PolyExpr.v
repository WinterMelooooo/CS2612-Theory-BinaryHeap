Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Structures.Equalities.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Require Import Coq.Logic.Eqdep.
From SimpleC.ASRTFUN Require Import list_lemma.

Require Import AUXLib.List_lemma.
Require Import AUXLib.Feq.

From SimpleC.CoreLang Require Import CTypes.
From SimpleC.Common Require Import Notations.

Local Open Scope string.
Local Open Scope option_monad_scope.
Import Coq.Lists.List.ListNotations.



Definition const_ptype_name: Type := string.
Definition const_ptype_name_eq_dec:
  forall t1 t2: const_ptype_name,
    {t1 = t2} + {t1 <> t2} := string_dec.

Definition builtin_type_name: Type := string.
Definition builtin_type_name_eq_dec:
  forall t1 t2: builtin_type_name,
    {t1 = t2} + {t1 <> t2} := string_dec.

Definition var_type_name: Type := string.
Definition var_type_name_eq_dec:
  forall t1 t2: var_type_name,
    {t1 = t2} + {t1 <> t2} := string_dec.

Definition var_name: Type := string.
Definition var_name_eq_dec:
  forall v1 v2: var_name,
    {v1 = v2} + {v1 <> v2} := string_dec.

Definition const_name: Type := string.
Definition const_name_eq_dec:
  forall c1 c2: const_name,
    {c1 = c2} + {c1 <> c2} := string_dec.

Definition func_name: Type := string.
Definition func_name_eq_dec:
  forall f1 f2: func_name,
    {f1 = f2} + {f1 <> f2} := string_dec.

Inductive type: Type :=
  | Tunit: type (* used as the default type for type computation *)
  | TBuiltin (i: builtin_type_name): type
  | TVar (i: var_type_name): type
  | TPolyApp (i: const_ptype_name) (arg: list type).

Definition type_nested_ind
             (P: type -> Prop)
             (Q: list type -> Prop)
             (H_Tunit: P Tunit)
             (H_TBuiltin: forall i, P (TBuiltin i))
             (H_TVar: forall i, P (TVar i))
             (H_TPolyApp: forall i arg, Q arg -> P (TPolyApp i arg))
             (H_nil: Q nil)
             (H_cons: forall t ts, Q ts -> P t -> Q (cons t ts)):
  forall t, P t :=
  fix type_nested_ind (t: type): P t :=
    match t as t0 return P t0 with
    | Tunit => H_Tunit
    | TBuiltin i => H_TBuiltin i
    | TVar i => H_TVar i
    | TPolyApp i arg =>
        H_TPolyApp i arg
          ((fix type_list_nested_ind (ts: list type): Q ts :=
              match ts as ts0 return Q ts0 with
              | nil => H_nil
              | cons t1 ts1 =>
                  H_cons t1 ts1
                    (type_list_nested_ind ts1)
                    (type_nested_ind t1)
              end) arg)
    end.


Record type_names := Build_type_names {
  const_ptype_names: list const_ptype_name;
  builtin_names: list builtin_type_name;
  var_names: list var_type_name;
}.

Definition type_names_app (tn1 tn2: type_names): type_names :=
  {| const_ptype_names := app (const_ptype_names tn1) (const_ptype_names tn2);
     builtin_names := app (builtin_names tn1) (builtin_names tn2);
     var_names := app (var_names tn1) (var_names tn2) |}.

Definition type_names_include (tn1 tn2: type_names): Prop :=
  incl (const_ptype_names tn1) (const_ptype_names tn2) /\
  incl (builtin_names tn1) (builtin_names tn2) /\
  incl (var_names tn1) (var_names tn2).

Local Definition get_type_names_list_aux
    (get_type_names: type -> type_names) (l: list type): type_names :=
  {|
    const_ptype_names := (flat_map (fun x => const_ptype_names (get_type_names x)) l);
    builtin_names := flat_map (fun x => builtin_names (get_type_names x)) l;
    var_names := flat_map (fun x => var_names (get_type_names x)) l
  |}.

Fixpoint get_type_names (t: type): type_names :=
  match t with
  | Tunit => Build_type_names [] [] []
  | TBuiltin i => Build_type_names [] [i] []
  | TVar i => Build_type_names [] [] [i]
  | TPolyApp i arg =>
    type_names_app (Build_type_names [i] [] []) (get_type_names_list_aux get_type_names arg)
  end
.

Definition get_type_names_list: list type -> type_names :=
  get_type_names_list_aux get_type_names.

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

Lemma type_names_list_include: forall l1 l2,
  incl l1 l2 -> type_names_include (get_type_names_list l1) (get_type_names_list l2).
Proof.
  intros.
  unfold type_names_include, incl.
  repeat split; simpl; intros i Hin.
  all: apply in_flat_map in Hin; destruct Hin as [x [Hin1 Hin2]];
       specialize (H x Hin1);
       apply in_flat_map; exists x; split; assumption.
Qed.

Lemma type_names_list_in_include: forall t l,
  In t l -> type_names_include (get_type_names t) (get_type_names_list l).
Proof.
  intros.
  apply (type_names_include_trans
    (get_type_names t) (get_type_names_list [t]) (get_type_names_list l)).
  - unfold get_type_names_list, get_type_names_list_aux. simpl.
    rewrite !app_nil_r. unfold type_names_include. simpl.
    repeat split; apply incl_refl.
  - apply type_names_list_include.
    unfold incl. intros x Hin. simpl in Hin. destruct Hin; try tauto.
    subst. assumption.
Qed.

Module type <: UsualDecidableType.
  Definition t := type.
  Definition eq := @Logic.eq type.
  Fixpoint eqb (x y : t) : bool :=
    match x, y with
    | Tunit, Tunit => true
    | TBuiltin i1, TBuiltin i2 => String.eqb i1 i2
    | TVar i1, TVar i2 => String.eqb i1 i2
    | TPolyApp i1 arg1, TPolyApp i2 arg2 =>
        andb (String.eqb i1 i2)
             (list_eqb eqb arg1 arg2)
    | _, _ => false
    end.
  Lemma eqb_eq : forall x y : t, eqb x y = true <-> x = y.
  Proof.
    intros x.
    pose (Q := fun l1 : list type => forall l2,
      list_eqb eqb l1 l2 = true <-> l1 = l2).
    induction x using type_nested_ind with (Q := Q); intros y.
    all: destruct y; simpl; split; intros; try congruence; try tauto.
    all: try (rewrite andb_true_iff in *); try split.
    all: try rewrite String.eqb_eq in *.
    all: unfold Q in *.
    - subst. reflexivity.
    - injection H. tauto.
    - subst. reflexivity.
    - injection H. tauto.
    - destruct H as [? H0].
      rewrite IHx in H0. subst. reflexivity.
    - injection H. tauto.
    - injection H. intros H_arg H_i.
      apply IHx. subst. reflexivity.
    - destruct H as [H H0].
      rewrite IHx in H0. rewrite IHx0 in H. subst. reflexivity.
    - rewrite IHx0. injection H. tauto.
    - rewrite IHx. injection H. tauto.
  Qed.
  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.
End type.




Fixpoint var_type_subst
          (i: var_type_name)
          (l1: list var_type_name)
          (l2: list type): type :=
  match l1, l2 with
  | cons i0 l1', cons t0 l2' =>
      if var_type_name_eq_dec i i0
      then t0
      else var_type_subst i l1' l2'
  | _, _ => Tunit
  end.

Definition type_subst
             (l1: list var_type_name)
             (l2: list type): type -> type :=
  fix type_subst (t: type) :=
    match t with
    | Tunit => Tunit
    | TBuiltin i => TBuiltin i
    | TVar i => var_type_subst i l1 l2
    | TPolyApp i arg => TPolyApp i (map type_subst arg)
    end.




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




Definition type_names_in_list (n: type_names) (l: type_asgn_list): Prop :=
  incl n.(const_ptype_names) (map fst l.(cpt_list)) /\
  incl n.(builtin_names)     (map fst l.(bt_list)) /\
  incl n.(var_names)         (map fst l.(vt_list)).





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



Inductive expr_names : Type :=
  Build_expr_names
    (tn: type_names)
    (var_names: list (var_name * type))
    (const_names: list (const_name * list var_type_name * type)).
Definition get_type_names_of_expr_names (n: expr_names): type_names :=
  match n with Build_expr_names tn _ _ => tn end.
Coercion get_type_names_of_expr_names: expr_names >-> type_names.
Definition get_var_names_of_expr_names (n: expr_names): list (var_name * type) :=
  match n with Build_expr_names _ var_names _ => var_names end.
Definition get_const_names_of_expr_names (n: expr_names): list (const_name * list var_type_name * type) :=
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
    Build_expr_names (get_type_names t) [(i, t)] []
  | EConst val t_params t_args t =>
    let t_args_names := get_type_names_list t_args in
    let t_res_names := get_type_names (type_subst t_params t_args t) in
    Build_expr_names (type_names_app t_args_names t_res_names) [] [(val, t_params, t)]
  | EApp arg_type ret_type f arg =>
    expr_names_app (get_expr_names _ f) (get_expr_names _ arg)
  end.


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
  + apply type_names_include_app_r.
    apply type_names_include_refl.
  + apply type_names_include_app_l.
    pose proof (tarrow_names_include_ret arg_type ret_type) as H.
    apply (type_names_include_trans _ _ _ H IHe1).
Qed.



Definition var_asgn (tJ: type_asgn): Type :=
  var_name -> forall t: type, option (teval tJ t).

Definition const_asgn (cptJ: const_ptype_asgn) (btJ: builtin_type_asgn): Type :=
  const_name -> forall (t_params: list var_type_name) (t: type) (t_args: list Type),
    option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t).

Definition vJ_list_type (tJ: type_asgn) : Type :=
  list (var_name * sigT (fun t: type => teval tJ t)).
Definition cJ_list_type (cptJ: const_ptype_asgn) (btJ: builtin_type_asgn) : Type :=
  list (const_name *
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

Definition vJ_list_get_decl [tJ] (l: vJ_list_type tJ)
    : list (var_name * type) :=
  map (fun '(i, existT t _) => (i, t)) l.
Definition cJ_list_get_decl [cptJ btJ] (l: cJ_list_type cptJ btJ)
    : list (const_name * list var_type_name * type) :=
  map (fun '(i, existT t_params (existT t _)) => (i, t_params, t)) l.
Definition vJ_list_nodup [tJ] (l: vJ_list_type tJ): Prop :=
  NoDup (vJ_list_get_decl l).
Definition cJ_list_nodup [cptJ btJ] (l: cJ_list_type cptJ btJ): Prop :=
  NoDup (cJ_list_get_decl l).

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

Definition asgn_list_nodup (l: asgn_list): Prop :=
  type_asgn_list_nodup l /\
  vJ_list_nodup l.(vJ_list) /\
  cJ_list_nodup l.(cJ_list).


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



Lemma var_asgn_upd_eq: forall [tJ: type_asgn] (J: var_asgn tJ) i [t] (v: teval tJ t),
  var_asgn_upd J i v i t = Some v.
Proof.
  intros.
  unfold var_asgn_eq, var_asgn_upd.
  destruct (var_name_eq_dec _ _); try congruence.
  destruct (type.eq_dec _ _); try congruence.
  rewrite <- Eqdep_dec.eq_rect_eq_dec.
  - reflexivity.
  - apply type.eq_dec.
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



Lemma var_asgn_upd_perm_list: forall [tJ: type_asgn] [J: var_asgn tJ] [t]
  x (v: teval tJ t) l,
  ~ In (x, t) (vJ_list_get_decl l) ->
  var_asgn_eq (var_asgn_upd_list (var_asgn_upd J x v) l)
              (var_asgn_upd (var_asgn_upd_list J l) x v).
Proof.
  intros.
  revert J.
  induction l; intros; simpl.
  + reflexivity.
  + destruct a as [i [t' v']].
    simpl in *.
    assert ((x, t) <> (i, t')).
    { contradict H. simpl. left. auto. }
    assert (~ In (x, t) (vJ_list_get_decl l)).
    { contradict H. simpl. right. auto. }
    rewrite var_asgn_upd_perm by congruence.
    rewrite IHl; auto.
    reflexivity.
Qed.


Lemma var_asgn_upd_list_no_dup: forall [tJ: type_asgn] (J: var_asgn tJ) l,
  vJ_list_nodup l ->
  forall i t v, In (i, existT _ t v) l ->
  var_asgn_upd_list J l i t = Some v.
Proof.
  intros tJ J l.
  revert J.
  induction l; intros J Hnodup i t v Hin; simpl.
  + destruct Hin.
  + destruct a as [i' [t' v']]. simpl in *.
    inversion Hnodup as [| ? ? Hnotin Hnodup']; subst.
    destruct Hin as [Heq | Hin].
    - injection Heq. intros Heq1 Heq2 Heq3. subst.
      apply inj_pair2 in Heq1. subst.
      rewrite var_asgn_upd_perm_list. 2: auto.
      rewrite var_asgn_upd_eq. reflexivity.
    - apply IHl; auto.
Qed.






Lemma pair_equal_lemma {A B} (a1 a2: A) (b1 b2: B):
  a1 = a2 -> b1 = b2 -> (a1, b1) = (a2, b2).
Proof.
  intros. subst. reflexivity.
Qed.
Definition const_asgn_upd [cptJ: const_ptype_asgn] [btJ: builtin_type_asgn]
    (cJ: const_asgn cptJ btJ) (i: const_name) (t_params: list var_type_name) (t: type)
    (v: forall t_args : list Type, option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t))
    : const_asgn cptJ btJ.
  intros i0 t_params0 t0 t_args0.
  pose (cJ i0 t_params0 t0 t_args0) as fallback.
  destruct (const_name_eq_dec i i0). 2: exact fallback.
  destruct (list_eq_dec var_type_name_eq_dec t_params t_params0) as [t_params_eq | _]. 2: exact fallback.
  destruct (type.eq_dec t t0) as [t_eq | _]. 2: exact fallback.
  pose proof (pair_equal_lemma _ _ _ _ t_params_eq t_eq) as t_params_and_t_eq.
  specialize (v t_args0).
  exact (eq_rect
    (t_params, t)
    (fun '(t_params, t) => option (teval (_ _ _ (Build_vtJ t_params t_args0)) t))
    v (t_params0, t0) t_params_and_t_eq).
Defined.



Definition const_asgn_upd_list [cptJ: const_ptype_asgn] [btJ: builtin_type_asgn]
    (cJ: const_asgn cptJ btJ) (l: cJ_list_type cptJ btJ) : const_asgn cptJ btJ :=
  fold_left (fun cJ0 (p: const_name *
      sigT (fun t_params: list var_type_name =>
      sigT (fun t: type =>
        forall t_args: list Type,
          option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t)))) =>
    let '(i, v) := p in
    let t_params := (projT1 v) in
    let t := projT1 (projT2 v) in
    let f := projT2 (projT2 v) in
    const_asgn_upd cJ0 i t_params t f) l cJ.


(* Definition const_asgn (cptJ: const_ptype_asgn) (btJ: builtin_type_asgn): Type :=
  const_name -> forall (t_params: list var_type_name) (t: type) (t_args: list Type),
            option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t). *)
Definition const_asgn_eq' [cptJ btJ] : Relation_Definitions.relation (const_asgn cptJ btJ) :=
  fun J1 J2 => forall i t_params t, J1 i t_params t = J2 i t_params t.
Definition const_asgn_eq [cptJ btJ] : Relation_Definitions.relation (const_asgn cptJ btJ) :=
  fun J1 J2 => forall i t_params t t_args, J1 i t_params t t_args = J2 i t_params t t_args.

#[export] Instance const_asgn_eq_refl [cptJ btJ]: Reflexive (@const_asgn_eq cptJ btJ).
Proof.
  unfold Reflexive, const_asgn_eq.
  intros.
  reflexivity.
Qed.

#[export] Instance const_asgn_eq_sym [cptJ btJ]: Symmetric (@const_asgn_eq cptJ btJ).
Proof.
  unfold Symmetric, const_asgn_eq.
  intros J1 J2 H **.
  symmetry. apply H.
Qed.

#[export] Instance const_asgn_eq_trans [cptJ btJ]: Transitive (@const_asgn_eq cptJ btJ).
Proof.
  unfold Transitive, const_asgn_eq.
  intros J1 J2 J3 H12 H23 i t_params t t_args.
  transitivity (J2 i t_params t t_args); auto.
Qed.

#[export] Instance const_asgn_upd_congr0 [cptJ btJ] :
  Proper (@const_asgn_eq cptJ btJ ==> eq ==>
    forall_relation (fun t_params: list var_type_name =>
      forall_relation (fun t: type => @eq (forall t_args : list Type,
        option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t)) ==>
          @const_asgn_eq cptJ btJ)))
  (@const_asgn_upd cptJ btJ).
Proof.
  unfold Proper, respectful, const_asgn_eq, forall_relation.
  intros J1 J2 HJ i ? <- t_params t v1 v2 <- i' t_params' t'.
  unfold const_asgn_upd.
  destruct (const_name_eq_dec _ _); simpl.
  + destruct (list_eq_dec _ _ _); simpl.
    - destruct (type.eq_dec _ _); simpl.
      * subst. reflexivity.
      * apply HJ.
    - apply HJ.
  + apply HJ.
Qed.

#[export] Instance const_asgn_upd_list_congr0 [cptJ btJ] :
  Proper ((@const_asgn_eq cptJ btJ) ==> eq ==> (@const_asgn_eq cptJ btJ))
         (@const_asgn_upd_list cptJ btJ).
Proof.
  unfold Proper, respectful, const_asgn_eq.
  intros J1 J2 HJ l l' <-.
  revert J1 J2 HJ. induction l; intros; simpl.
  + apply HJ.
  + destruct a as [i' [t_params' [t' v']]]. simpl.
    apply IHl. intros.
    apply const_asgn_upd_congr0; auto.
Qed.




Lemma pair_eq_dec: forall (A B: Type),
  (forall (x y: A), {x = y} + {x <> y}) ->
  (forall (x y: B), {x = y} + {x <> y}) ->
  forall (x y: A * B), {x = y} + {x <> y}.
Proof.
  intros.
  decide equality.
Qed.

Definition type_params_pair_eq_dec: forall (x y: list var_type_name * type),
  {x = y} + {x <> y}.
  exact (pair_eq_dec _ _ (list_eq_dec var_name_eq_dec) type.eq_dec).
Defined.

Lemma const_asgn_upd_eq: forall [cptJ btJ] (J: const_asgn cptJ btJ) i t_params t v,
  const_asgn_upd J i t_params t v i t_params t = v.
Proof.
  intros.
  unfold const_asgn_eq, const_asgn_upd.
  destruct (const_name_eq_dec _ _); try congruence.
  destruct (list_eq_dec _ _ _); try congruence.
  destruct (type.eq_dec _ _); try congruence.
  generalize (pair_equal_lemma _ _ _ _ e0 e1).
  intro e2.
  pose proof Eqdep_dec.UIP_dec type_params_pair_eq_dec e2 eq_refl. subst.
  simpl. reflexivity.
Qed.


Lemma const_asgn_upd_perm: forall [cptJ btJ] (J: const_asgn cptJ btJ) x y
  [t_params1 t1] v1 [t_params2 t2] v2,
  (x, t_params1, t1) <> (y, t_params2, t2) ->
  const_asgn_eq (const_asgn_upd (const_asgn_upd J x t_params1 t1 v1) y t_params2 t2 v2)
                (const_asgn_upd (const_asgn_upd J y t_params2 t2 v2) x t_params1 t1 v1).
Proof.
  intros.
  unfold const_asgn_upd.
  intros i t_params t.
  destruct (const_name_eq_dec x i), (const_name_eq_dec y i); try congruence.
  destruct (list_eq_dec _ t_params1 t_params), (list_eq_dec _ t_params2 t_params); simpl; try congruence.
  destruct (type.eq_dec t1 t), (type.eq_dec t2 t); try congruence.
Qed.



Lemma const_asgn_upd_perm_list: forall [cptJ btJ] [J: const_asgn cptJ btJ]
  x [t_params t] v l,
  ~ In (x, t_params, t) (cJ_list_get_decl l) ->
  const_asgn_eq (const_asgn_upd_list (const_asgn_upd J x t_params t v) l)
                (const_asgn_upd (const_asgn_upd_list J l) x t_params t v).
Proof.
  intros.
  revert J.
  induction l; intros; simpl.
  + reflexivity.
  + destruct a as [i [t_params' [t' v']]].
    simpl in *.
    assert ((x, t_params, t) <> (i, t_params', t')).
    { contradict H. simpl. left. auto. }
    assert (~ In (x, t_params, t) (cJ_list_get_decl l)).
    { contradict H. simpl. right. auto. }
    rewrite const_asgn_upd_perm by congruence.
    rewrite IHl; auto.
    reflexivity.
Qed.


Lemma const_asgn_upd_list_no_dup: forall [cptJ btJ]
  (J: const_asgn cptJ btJ) (l: cJ_list_type cptJ btJ),
  cJ_list_nodup l ->
  forall i t_params t v t_args, In (i, existT _ t_params (existT _ t v)) l ->
  const_asgn_upd_list J l i t_params t t_args = v t_args.
Proof.
  intros cptJ btJ J l.
  revert J.
  induction l; intros J Hnodup i t_params t v t_args Hin; simpl.
  + destruct Hin.
  + destruct a as [i' [t_params' [t' v']]]. simpl in *.
    inversion Hnodup as [| ? ? Hnotin Hnodup']; subst.
    destruct Hin as [Heq | Hin].
    - injection Heq. intros Heq1 Heq2 Heq3 Heq4. subst.
      apply inj_pair2 in Heq1. apply inj_pair2 in Heq1. subst.
      rewrite const_asgn_upd_perm_list. 2: auto.
      rewrite const_asgn_upd_eq. reflexivity.
    - apply IHl; auto.
Qed.



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



Definition empty_vJ {tJ} : var_asgn tJ :=
  fun _ _ => None.
Definition make_var_asgn_from_list [tJ] (vJ_list: vJ_list_type tJ) : var_asgn tJ :=
  var_asgn_upd_list empty_vJ vJ_list.

Definition empty_cJ {cptJ btJ} : const_asgn cptJ btJ :=
  fun _ _ _ _ => None.
Definition make_const_asgn_from_list [cptJ btJ] (cJ_list: cJ_list_type cptJ btJ)
    : const_asgn cptJ btJ :=
  const_asgn_upd_list empty_cJ cJ_list.


Definition make_asgn_from_list (l: asgn_list): asgn :=
  Build_asgn
    (make_type_asgn_from_list l)
    (make_var_asgn_from_list l.(vJ_list))
    (make_const_asgn_from_list l.(cJ_list)).


Definition vJ_list_incl [tJ1 tJ2: type_asgn]
    (vl1: vJ_list_type tJ1) (vl2: vJ_list_type tJ2): Prop :=
  forall i t v1, In (i, existT _ t v1) vl1 ->
    exists v2, eq_dep _ (fun x => x) _ v1 _ v2 /\
               In (i, existT _ t v2) vl2.




Definition cJ_list_incl' [cptJ1 btJ1 cptJ2 btJ2]
    (cl1: cJ_list_type cptJ1 btJ1) (cl2: cJ_list_type cptJ2 btJ2): Prop :=
  forall i t_params t v1, In (i, existT _ t_params (existT _ t v1)) cl1 ->
    exists v2, eq_dep _ (fun x => x) _ v1 _ v2 /\
               In (i, existT _ t_params (existT _ t v2)) cl2.

Definition cJ_list_incl [cptJ1 btJ1 cptJ2 btJ2]
    (cl1: cJ_list_type cptJ1 btJ1) (cl2: cJ_list_type cptJ2 btJ2): Prop :=
  forall i t_params t v1, In (i, existT _ t_params (existT _ t v1)) cl1 ->
    exists v2, (forall t_args, eq_dep _ (fun x => x) _ (v1 t_args) _ (v2 t_args)) /\
               In (i, existT _ t_params (existT _ t v2)) cl2.

Definition asgn_list_incl (l1 l2: asgn_list): Prop :=
  type_asgn_list_incl l1 l2 /\
  vJ_list_incl l1.(vJ_list) l2.(vJ_list) /\
  cJ_list_incl l1.(cJ_list) l2.(cJ_list).

Definition get_names_from_asgn_list (l: asgn_list): expr_names :=
  Build_expr_names
    (get_type_names_from_type_asgn_list l)
    (map (fun p => (fst p, projT1 (snd p))) l.(vJ_list))
    (map (fun p => (fst p, projT1 (snd p), projT1 (projT2 (snd p)))) l.(cJ_list)).


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
    In (i, t) n.(var_names) ->
    eq_dep _ (fun x => x) _ (J1.(vJ) i t) _ (J2.(vJ) i t)) /\
  (forall i t_params t t_args,
    (forall t_arg, In t_arg t_args -> type_names_include (get_type_names t_arg) n) ->
    type_names_include (get_type_names (type_subst t_params t_args t)) n ->
    In (i, t_params, t) n.(const_names) ->
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
      ++ intros t_arg Ht_arg_in. specialize (H t_arg Ht_arg_in).
         apply type_names_include_app_l. tauto.
      ++ apply type_names_include_app_l. tauto.
      ++ simpl. apply in_or_app. left. tauto.
  + repeat split; intros.
    1-3: apply Ht; simpl; apply in_or_app; right; tauto.
    - apply Hv.
      ++ apply type_names_include_app_r. tauto.
      ++ simpl. apply in_or_app. right. tauto.
    - apply Hc.
      ++ intros t_arg Ht_arg_in. specialize (H t_arg Ht_arg_in).
         apply type_names_include_app_r. tauto.
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
  + apply type_asgn_coincide_app_r in H. assumption.
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
    specialize (Hc val t_params t t_args). simpl in Hc.
    assert (Hctmp: (forall t_arg : type,
    In t_arg t_args ->
    type_names_include (get_type_names t_arg)
      (type_names_app (get_type_names_list t_args)
         (get_type_names (type_subst t_params t_args t))))).
    { intros t_arg Htin.
      apply type_names_include_app_l.
      apply type_names_list_in_include. assumption. }
    specialize (Hc Hctmp). clear Hctmp.
    assert (Hctmp: type_names_include (get_type_names (type_subst t_params t_args t))
      (type_names_app (get_type_names_list t_args)
         (get_type_names (type_subst t_params t_args t)))).
    { apply type_names_include_app_r. apply type_names_include_refl. }
    specialize (Hc Hctmp). clear Hctmp.
    assert (Htmp: (val, t_params, t) = (val, t_params, t) \/ False) by auto.
    specialize (Hc Htmp). clear Htmp.
    apply eq_dep_lem1. exact Hc.
  + destruct (eapp_asgn_coincide_on_subexpr H) as [He1_co He2_co].
    specialize (IHe1 He1_co).
    specialize (IHe2 He2_co).
    (* pose proof eeval_coincide_aux _ _ _ e1 He1_co as Ht1eq. *)
    pose proof eeval_coincide_aux _ _ _ e2 He2_co as Ht2eq.
    pose proof eeval_coincide_aux _ _ _ (EApp _ _ e1 e2) H as Hteq.
    apply (eq_dep_lem3 Ht2eq Hteq); auto.
Qed.


Lemma eq_dep_lem4: forall [A B: Type] (a: A) (b: B),
  eq_dep Type (fun x => x) A a B b ->
  eq_dep Type (fun x => x) (option A) (Some a) (option B) (Some b).
Proof.
  intros.
  destruct H.
  reflexivity.
Qed.



Theorem asgn_include_coincide: forall (l1 l2: asgn_list),
  asgn_list_nodup l1 -> asgn_list_nodup l2 ->
  asgn_list_incl l1 l2 ->
  let J1 := make_asgn_from_list l1 in
  let J2 := make_asgn_from_list l2 in
  let n1 := get_names_from_asgn_list l1 in
  asgn_coincide_on_names J1 J2 n1.
Proof.
  intros l1 l2 Hnodup1 Hnodup2 Hinc J1 J2 n1.
  repeat split.
  1-3: destruct Hnodup1 as [Hnodup1 _], Hnodup2 as [Hnodup2 _];
       destruct Hinc as [Hinc _];
       apply type_asgn_include_coincide with (l1 := l1) (l2 := l2); auto.
  + intros i t Ht Hin1.
    simpl in Hin1.
    apply in_map_iff in Hin1. destruct Hin1 as [[i' [t' v1]] [Heq Hin1]]; simpl in *.
    injection Heq as Heq1 Heq2. subst.

    destruct Hinc as [_ [Hinc _]]. specialize (Hinc i t v1 Hin1).
    destruct Hinc as [v2 [Hveq Hin2]].

    destruct Hnodup1 as [_ [Hnodup1 _]], Hnodup2 as [_ [Hnodup2 _]].
    unfold make_var_asgn_from_list.
    rewrite (var_asgn_upd_list_no_dup empty_vJ l1.(vJ_list) Hnodup1 i t v1 Hin1).
    rewrite (var_asgn_upd_list_no_dup empty_vJ l2.(vJ_list) Hnodup2 i t v2 Hin2).
    apply eq_dep_lem4. auto.
  + intros i t_params t t_args Ht_args_incl Ht_incl Hin1.

    assert (Ht_args_eq: (map (teval (make_type_asgn_from_list l1)) t_args) =
                        (map (teval (make_type_asgn_from_list l2)) t_args)).
    { apply map_ext_in. intros t_arg Htin.
      specialize (Ht_args_incl t_arg Htin).
      destruct Hnodup1 as [Hnodup1 _], Hnodup2 as [Hnodup2 _].
      destruct Hinc as [Hinc _].
      pose proof type_asgn_include_coincide l1 l2 Hnodup1 Hnodup2 Hinc as H.
      pose proof type_names_include_coincide _ _ _ _ Ht_args_incl H as H'.
      apply teval_coincide. exact H'. }

    simpl in Hin1.
    apply in_map_iff in Hin1.
    destruct Hin1 as [[i' [t_params' [t' v]]] [Heq Hin1]]; simpl in *.
    injection Heq as Heq1 Heq2 Heq3; subst.

    destruct Hinc as [_ [_ Hinc]]. specialize (Hinc i t_params t v Hin1).
    destruct Hinc as [v2 [Hveq Hin2]].
    destruct Hnodup1 as [_ [_ Hnodup1]], Hnodup2 as [_ [_ Hnodup2]].
    unfold make_const_asgn_from_list.
    rewrite (const_asgn_upd_list_no_dup empty_cJ l1.(cJ_list) Hnodup1 i t_params t v _ Hin1).
    rewrite (const_asgn_upd_list_no_dup empty_cJ l2.(cJ_list) Hnodup2 i t_params t v2 _ Hin2).
    clear Hnodup1 Hnodup2 Hin1 Hin2.

    rewrite Ht_args_eq.
    apply Hveq.
Qed.















(* Example *)

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

Ltac auto_prove_no_dup :=
  repeat constructor; simpl; auto;
  assert (Hfalse: forall P : Prop, P \/ False <-> P) by tauto; rewrite Hfalse;
  intros H; smart_destruct H; congruence.

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

(* Record type_asgn_list : Type := {
  cpt_list: list (const_ptype_name * (list Type -> Type));
  bt_list:  list (builtin_type_name * Type);
  vt_list:  list (var_type_name * Type)
}. *)

Example core_type_asgn_list :=
  Build_type_asgn_list
    [("list", wrap_const_ptype_1 list)]
    [("Z", Z: Type)]
    [].

Example core_tJ := make_type_asgn_from_list core_type_asgn_list.

Lemma core_tJ_list_no_dup: type_asgn_list_nodup core_type_asgn_list.
Proof.
  auto_prove_no_dup.
Qed.


(* The 'cptJ' and 'btJ' type parameters are necessary for Coq type inference. *)
(* The type cast of (fun ts : list Type => ...) is necessary for Coq type unification. *)
Notation "'wrap_poly_fn_0' cptJ ; btJ ; t_params ; t ; f" :=
  (existT _ t_params (existT _ t (
    (fun ts : list Type => match ts with
                           | nil => Some f
                           | _ => None
                           end)
    : forall t_args: list Type, option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t))))
  (at level 200).
Notation "'wrap_poly_fn_1' cptJ ; btJ ; t_params ; t ; f" :=
  (existT _ t_params (existT _ t (
    (fun ts : list Type => match ts with
                           | cons A nil => Some (f A)
                           | _ => None
                           end)
    : forall t_args: list Type, option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t))))
  (at level 200).
Notation "'wrap_poly_fn_2' cptJ ; btJ ; t_params ; t ; f" :=
  (existT _ t_params (existT _ t (
    (fun ts : list Type => match ts with
                           | cons A1 (cons A2 nil) => Some (f A1 A2)
                           | _ => None
                           end)
    : forall t_args: list Type, option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t))))
  (at level 200).



Example list_A := TPolyApp "list" [TVar "A"].
Example cons_A := TArrow (TVar "A") (TArrow list_A list_A).
Example core_cJ_list : cJ_list_type core_tJ.(cpt) core_tJ.(bt) :=
  [("nil",  wrap_poly_fn_1 core_tJ.(cpt); core_tJ.(bt); ["A"]; list_A; @nil) ;
   ("cons", wrap_poly_fn_1 core_tJ.(cpt); core_tJ.(bt); ["A"]; cons_A; @cons)].

Example core_asgn_list :=
  Build_asgn_list
    core_type_asgn_list
    []
    core_cJ_list.

Example core_J := make_asgn_from_list core_asgn_list.

Lemma core_J_list_no_dup: asgn_list_nodup core_asgn_list.
Proof.
  auto_prove_no_dup.
Qed.

Example Z_type := TBuiltin "Z".
Example nil_Z_expr := EConst "nil" ["A"] [Z_type] list_A.
Example cons_Z_expr := EConst "cons" ["A"] [Z_type] cons_A.
Example x_expr := EVar "x" Z_type.
Example a_list_expr := EApp _ _ (EApp _ _ cons_Z_expr x_expr) nil_Z_expr.


Lemma nil_Z_expr_eval_correct: eeval core_J _ nil_Z_expr = Some (@nil Z).
Proof.
  simpl.
  unfold make_const_asgn_from_list, const_asgn_upd_list, const_asgn_upd.
  simpl. rewrite <- !(Eqdep_dec.eq_rect_eq_dec type_params_pair_eq_dec).
  reflexivity.
Qed.

Lemma a_list_expr_eval_correct: forall vJ v,
  let J := Build_asgn core_tJ vJ core_J.(cJ) in
  eeval J _ x_expr = Some v ->
  eeval J _ a_list_expr = Some (cons v (@nil Z)).
Proof.
  intros.
  simpl.
  unfold make_const_asgn_from_list, const_asgn_upd_list, const_asgn_upd.
  simpl. rewrite <- !(Eqdep_dec.eq_rect_eq_dec type_params_pair_eq_dec).
  simpl in H. rewrite H. reflexivity.
Qed.



Example extended_type_asgn_list :=
  Build_type_asgn_list
    [("list", wrap_const_ptype_1 list);
     ("prod", wrap_const_ptype_2 prod)]
    [("Z", Z: Type);
     ("nat", nat: Type)]
    [].
Example extended_tJ := make_type_asgn_from_list extended_type_asgn_list.

Lemma extended_tJ_list_no_dup: type_asgn_list_nodup extended_type_asgn_list.
Proof.
  auto_prove_no_dup.
Qed.

Lemma extended_tJ_include_core: type_asgn_list_incl core_type_asgn_list extended_type_asgn_list.
Proof.
  repeat split; simpl;
  intros [i v] Hin; simpl in *; tauto.
Qed.

Lemma extended_tJ_coincide_core_tJ: type_asgn_coincide_on_names
  core_J extended_tJ (get_type_names_from_type_asgn_list core_type_asgn_list).
Proof.
  apply type_asgn_include_coincide.
  + apply core_tJ_list_no_dup.
  + apply extended_tJ_list_no_dup.
  + apply extended_tJ_include_core.
Qed.

Example Z_add_type := TArrow Z_type (TArrow Z_type Z_type).
Example extended_cJ_list : cJ_list_type extended_tJ.(cpt) extended_tJ.(bt) :=
  [
    ("nil", wrap_poly_fn_1 extended_tJ.(cpt); extended_tJ.(bt); ["A"]; list_A; @nil);
    ("cons", wrap_poly_fn_1 extended_tJ.(cpt); extended_tJ.(bt); ["A"]; cons_A; @cons);
    ("add", wrap_poly_fn_0 extended_tJ.(cpt); extended_tJ.(bt); nil; Z_add_type; Z.add)
  ].

Definition find_in_cJ_list [cptJ btJ] (i: const_name) (t_params: list var_type_name) (t: type) :=
  fix find_in_cJ_list (cl: cJ_list_type cptJ btJ) : option (forall t_args, option (
      teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t)) :=
  match cl with
  | [] => None
  | (i', existT t_params' (existT t' v)) :: cl' =>
    if const_name_eq_dec i' i then
      match list_eq_dec var_type_name_eq_dec t_params' t_params with
      | left Ht_params_eq =>
        match type.eq_dec t' t with
        | left Ht_eq =>
          Some (eq_rect
            (t_params', t')
            (fun '(t_params, t) => forall t_args, option (teval (Build_type_asgn cptJ btJ (Build_vtJ t_params t_args)) t))
            v _ (pair_equal_lemma _ _ _ _ Ht_params_eq Ht_eq))
        | right _ => find_in_cJ_list cl'
        end
      | right _ => find_in_cJ_list cl'
      end
    else find_in_cJ_list cl'
  end.

(* Set implicit arguments to make the printing more readable *)
Arguments eq_rect {_ _ _} _ {_ _}.
Arguments existT {_ _} _ _.
Arguments teval {_} _.
Lemma extended_cJ_include_core_cJ: cJ_list_incl core_cJ_list extended_cJ_list.
Proof.
  unfold cJ_list_incl. intros i t_params t v1 Hin.
  unfold core_cJ_list in Hin.
  unfold In in Hin.
  smart_destruct Hin; try tauto;
  apply pair_equal_spec in Hin; destruct Hin as [Hi_eq Hv_eq].

  {
    inversion_sigma.

    remember (find_in_cJ_list i t_params t core_cJ_list) as find.
    subst i t_params t.
    simpl in Heqfind.
    destruct find as [find|]; [|congruence].
    injection Heqfind as Heqfind.
    exists find. subst.
    split.
    + intro t_args. simpl.
      rewrite <- (Eqdep_dec.eq_rect_eq_dec type_params_pair_eq_dec).
      reflexivity.
    + simpl.
      rewrite <- (Eqdep_dec.eq_rect_eq_dec type_params_pair_eq_dec).
      tauto.
  }

  {
    inversion_sigma.

    remember (find_in_cJ_list i t_params t core_cJ_list) as find.
    subst i t_params t.
    simpl in Heqfind.
    destruct find as [find|]; [|congruence].
    injection Heqfind as Heqfind.
    exists find. subst.
    split.
    + intro t_args. simpl.
      rewrite <- (Eqdep_dec.eq_rect_eq_dec type_params_pair_eq_dec).
      reflexivity.
    + simpl.
      rewrite <- (Eqdep_dec.eq_rect_eq_dec type_params_pair_eq_dec).
      tauto.
  }
Qed.

Example extended_asgn_list :=
  Build_asgn_list
    extended_type_asgn_list
    []
    extended_cJ_list.

Example extended_J := make_asgn_from_list extended_asgn_list.

Lemma extended_J_list_no_dup: asgn_list_nodup extended_asgn_list.
Proof.
  auto_prove_no_dup.
Qed.

Lemma extended_J_include_core_J: asgn_list_incl core_asgn_list extended_asgn_list.
Proof.
  split. apply extended_tJ_include_core.
  repeat split.
  + simpl. unfold vJ_list_incl. intros i t v1 Hin.
    simpl in Hin. tauto.
  + apply extended_cJ_include_core_cJ.
Qed.

Lemma extended_J_coincide_core_J: asgn_coincide_on_names core_J extended_J
  (get_names_from_asgn_list core_asgn_list).
Proof.
  apply asgn_include_coincide.
  + apply core_J_list_no_dup.
  + apply extended_J_list_no_dup.
  + apply extended_J_include_core_J.
Qed.
