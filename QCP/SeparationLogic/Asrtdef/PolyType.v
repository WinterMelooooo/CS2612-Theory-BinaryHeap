Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Structures.Equalities.
Require Import AUXLib.List_lemma.
Local Open Scope string.
Import Coq.Lists.List.ListNotations.

(* Polymorphic type constructor *)
Definition const_ptype_name: Type := string.
Definition const_ptype_name_eq_dec:
  forall t1 t2: const_ptype_name,
    {t1 = t2} + {t1 <> t2} := string_dec.
Definition default_ptype_name: const_ptype_name := "".

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
#[export] Hint Unfold get_type_names_list_aux : core.

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

(* Definition arg_type (sig : PolyFuncSig) (type_arg: list type): list type :=
  map
    (type_subst (type_arg_name_of_sig sig) type_arg)
    (arg_type_of_sig sig).

Definition ret_type (sig : PolyFuncSig) (type_arg: list type): type :=
  type_subst
    (type_arg_name_of_sig sig)
    type_arg
    (ret_type_of_sig sig). *)
