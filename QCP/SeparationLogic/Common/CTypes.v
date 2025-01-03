Require Import Coq.Structures.Equalities.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Inductive Signedness: Type :=
  | Signed: Signedness
  | Unsigned: Signedness.

Inductive IntSize: Type :=
  | I8: IntSize
  | I16: IntSize
  | I32: IntSize
  | I64: IntSize.

Inductive CBasicType: Type :=
  | CT_void: CBasicType
  | CT_int (s: Signedness) (i: IntSize): CBasicType.

Module Signedness <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := Signedness.
  Definition eq := @Logic.eq Signedness.
  Definition eqb (s1 s2: Signedness): bool :=
    match s1, s2 with
    | Signed, Signed
    | Unsigned, Unsigned => true
    | _, _ => false
    end.
  Lemma eqb_eq:
    forall s1 s2: Signedness, eqb s1 s2 = true <-> s1 = s2.
  Proof.
    intros.
    destruct s1, s2; simpl; first [tauto | split; intros; congruence].
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End Signedness.

Module IntSize <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := IntSize.
  Definition eq := @Logic.eq IntSize.
  Definition eqb (i1 i2: IntSize): bool :=
    match i1, i2 with
    | I8, I8
    | I16, I16
    | I32, I32
    | I64, I64 => true
    | _, _ => false
    end.
  Lemma eqb_eq:
    forall i1 i2: IntSize, eqb i1 i2 = true <-> i1 = i2.
  Proof.
    intros.
    destruct i1, i2; simpl; first [tauto | split; intros; congruence].
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End IntSize.

Module CBasicType <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := CBasicType.
  Definition eq := @Logic.eq CBasicType.
  Definition eqb (t1 t2: CBasicType): bool :=
    match t1, t2 with
    | CT_void, CT_void => true
    | CT_int s1 i1, CT_int s2 i2 => Signedness.eqb s1 s2 && IntSize.eqb i1 i2
    | _, _ => false
    end.
  Lemma eqb_eq:
    forall t1 t2: CBasicType, eqb t1 t2 = true <-> t1 = t2.
  Proof.
    intros.
    destruct t1, t2; simpl.
    + tauto.
    + split; intros; congruence.
    + split; intros; congruence.
    + rewrite andb_true_iff.
      rewrite Signedness.eqb_eq.
      rewrite IntSize.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End CBasicType.

Definition max_int (s: Signedness) (i: IntSize): Z :=
  match s, i with
  | Signed, I8 => 2^7 - 1
  | Unsigned, I8 => 2^8 - 1
  | Signed, I16 => 2^15 - 1
  | Unsigned, I16 => 2^16 - 1
  | Signed, I32 => 2^31 - 1
  | Unsigned, I32 => 2^32 - 1
  | Signed, I64 => 2^63 - 1
  | Unsigned, I64 => 2^64 - 1
  end.

Definition min_int (s: Signedness) (i: IntSize): Z :=
  match s, i with
  | Signed, I8 => - 2^7
  | Signed, I16 => - 2^15
  | Signed, I32 => - 2^31
  | Signed, I64 => - 2^63
  | Unsigned, _ => 0
  end.
