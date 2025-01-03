Require Import Coq.Structures.Equalities.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import SimpleC.Common.CTypes.
Require Import AUXLib.List_lemma.

Inductive FieldName: Type :=
  | CFN_named (s: string): FieldName
  | CFN_unnamed (i: Z): FieldName.
  (** A struct/union field can be named or unnamed.
      Every unnamed field has a distinct id. *)

Inductive TypeName: Type :=
  | CTN_named (s: string): TypeName
  | CTN_unnamed (i: Z): TypeName.
  (** A struct/union/enum type can be named or unnamed.
      Every unnamed type has a distinct id. *)

Inductive SimpleCtype : Type :=
  | CT_basic (t: CBasicType): SimpleCtype 
      (** basic types *)
  | CT_pointer (t: SimpleCtype): SimpleCtype 
      (** pointer types ( * t ) *)
  | CT_array (t: SimpleCtype) (n: option Z): SimpleCtype
      (** array types
          - normal array, CT_array t (Some n) for t[n]
          - dynamic array, CT_array t None for t[] *)
  | CT_function (t0: SimpleCtype) (ts: list SimpleCtype): SimpleCtype
      (** function types *)
  | CT_struct (i: TypeName) (lvl: nat): SimpleCtype   (** struct types *)
  | CT_union (i: TypeName) (lvl: nat): SimpleCtype    (** union types *)
  | CT_enum (i: TypeName) (lvl: nat): SimpleCtype     (** enum types *)
  | CT_alias (s: string) (lvl: nat): SimpleCtype      (** typedef types *)
.

Inductive TypeDecl: Type :=
  | CTDecl_struct (i: string): TypeDecl
  | CTDecl_union (i: string): TypeDecl
  | CTDecl_enum (i: string): TypeDecl.

Record FieldDecl: Type :=
  {
    field_name: FieldName;
    field_type: SimpleCtype;
  }.

Record Enumerator: Type :=
  {
    enumerator_name: string;
    enumerator_value: Z;
  }.

Inductive TypeDef: Type :=
  | CTDef_struct (i: TypeName) (m: list FieldDecl)
  | CTDef_union (i: TypeName) (m: list FieldDecl)
  | CTDef_enum (i: TypeName) (m: list Enumerator)
  | CTDef_typedef (i: string) (t: SimpleCtype).

Definition SimpleCtype_full_ind
             (P: SimpleCtype -> Prop)
             (Q: list SimpleCtype -> Prop)
             (H_basic: forall t: CBasicType, P (CT_basic t))
             (H_pointer: forall t (IHt: P t), P (CT_pointer t))
             (H_array: forall t (IHt: P t) (len: option Z), P (CT_array t len))
             (H_function: forall t0 (IHt0: P t0) ts (IHts: Q ts),
                          P (CT_function t0 ts))
             (H_struct: forall i lvl, P (CT_struct i lvl))
             (H_union: forall i lvl, P (CT_union i lvl))
             (H_enum: forall i lvl, P (CT_enum i lvl))
             (H_alias: forall s lvl, P (CT_alias s lvl))
             (H_nil: Q nil)
             (H_cons: forall t (IHt: P t) ts (IHts: Q ts), Q (cons t ts)):
  forall t, P t :=
  (fix ind (t: SimpleCtype): P t :=
     match t with
     | CT_basic t0 => H_basic t0
     | CT_pointer t0 => H_pointer t0 (ind t0)
     | CT_array t0 len => H_array t0 (ind t0) len
     | CT_function t0 ts =>
         H_function t0 (ind t0) ts
           ((fix list_ind (ts: list SimpleCtype): Q ts :=
              match ts with
              | nil => H_nil
              | cons t ts0 => H_cons t (ind t) ts0 (list_ind ts0)
              end) ts)
     | CT_struct i lvl => H_struct i lvl
     | CT_union i lvl => H_union i lvl
     | CT_enum i lvl => H_enum i lvl
     | CT_alias s lvl => H_alias s lvl
     end).

Module FieldName <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := FieldName.
  Definition eq := @Logic.eq FieldName.
  Definition eqb (t1 t2: FieldName): bool :=
    match t1, t2 with
    | CFN_named s1, CFN_named s2 => String.eqb s1 s2
    | CFN_unnamed i1, CFN_unnamed i2 => Z.eqb i1 i2
    | _, _ => false
    end.
  Lemma eqb_eq:
    forall t1 t2: FieldName, eqb t1 t2 = true <-> t1 = t2.
  Proof.
    intros.
    destruct t1, t2; simpl.
    + rewrite String.eqb_eq.
      split; intros; congruence.
    + split; intros; congruence.
    + split; intros; congruence.
    + rewrite Z.eqb_eq.
      split; intros; congruence.
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End FieldName.

Module TypeName <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := TypeName.
  Definition eq := @Logic.eq TypeName.
  Definition eqb (t1 t2: TypeName): bool :=
    match t1, t2 with
    | CTN_named s1, CTN_named s2 => String.eqb s1 s2
    | CTN_unnamed i1, CTN_unnamed i2 => Z.eqb i1 i2
    | _, _ => false
    end.
  Lemma eqb_eq:
    forall t1 t2: TypeName, eqb t1 t2 = true <-> t1 = t2.
  Proof.
    intros.
    destruct t1, t2; simpl.
    + rewrite String.eqb_eq.
      split; intros; congruence.
    + split; intros; congruence.
    + split; intros; congruence.
    + rewrite Z.eqb_eq.
      split; intros; congruence.
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End TypeName.

Module SimpleCtype <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := SimpleCtype.
  Definition eq := @Logic.eq SimpleCtype.
  Fixpoint eqb (t1 t2: SimpleCtype): bool :=
    match t1, t2 with
    | CT_basic t1, CT_basic t2 =>
        CBasicType.eqb t1 t2
    | CT_pointer ty1, CT_pointer ty2 =>
        eqb ty1 ty2 
    | CT_array ty1 len1, CT_array ty2 len2 =>
        eqb ty1 ty2 && option_eqb Z.eqb len1 len2
    | CT_function ty1 tys1, CT_function ty2 tys2 =>
        eqb ty1 ty2 && list_eqb eqb tys1 tys2
    | CT_struct i1 lvl1, CT_struct i2 lvl2 =>
        TypeName.eqb i1 i2 && Nat.eqb lvl1 lvl2
    | CT_union i1 lvl1, CT_union i2 lvl2 =>
        TypeName.eqb i1 i2 && Nat.eqb lvl1 lvl2
    | CT_enum i1 lvl1, CT_enum i2 lvl2 =>
        TypeName.eqb i1 i2 && Nat.eqb lvl1 lvl2
    | CT_alias s1 lvl1, CT_alias s2 lvl2 =>
        String.eqb s1 s2 && Nat.eqb lvl1 lvl2
    | _ , _ => false
    end.

  Lemma eqb_eq:
    forall t1 t2: SimpleCtype, eqb t1 t2 = true <-> t1 = t2.
  Proof.
    apply
      (SimpleCtype_full_ind
        (fun t1 => forall t2, eqb t1 t2 = true <-> t1 = t2)
        (fun ts1 => forall ts2, list_eqb eqb ts1 ts2 = true <-> ts1 = ts2)).
    + intros t1 t2.
      destruct t2 as [t2 | | | | | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite CBasicType.eqb_eq.
      split; intros; congruence.
    + intros t1 IHt1 t2.
      destruct t2 as [| t2 | | | | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite IHt1.
      split; intros; congruence.
    + intros t1 IHt1 len1 t2.
      destruct t2 as [| | t2 len2 | | | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite option_eqb_eq by apply Z.eqb_eq.
      rewrite IHt1.
      split; [intros [? ?] | intros; split]; congruence.
    + intros t1 IHt1 ts1 IHts1 t2.
      destruct t2 as [| | | t2 ts2 | | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite IHt1, IHts1.
      split; [intros [? ?] | intros; split]; congruence.
    + intros i1 lvl1 t2.
      destruct t2 as [| | | | i2 lvl2 | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite TypeName.eqb_eq, Nat.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
    + intros i1 lvl1 t2.
      destruct t2 as [| | | | | i2 lvl2 | |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite TypeName.eqb_eq, Nat.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
    + intros i1 lvl1 t2.
      destruct t2 as [| | | | | | i2 lvl2 |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite TypeName.eqb_eq, Nat.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
    + intros s1 lvl1 t2.
      destruct t2 as [| | | | | | | s2 lvl2]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite String.eqb_eq, Nat.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
    + apply list_eqb_eq_nil.
    + intros t IHt ts IHts.
      apply list_eqb_eq_cons; auto.
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End SimpleCtype.

