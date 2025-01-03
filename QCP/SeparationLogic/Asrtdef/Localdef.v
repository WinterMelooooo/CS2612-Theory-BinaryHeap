(* This file contains the syntax tree and some related functions of Local *)

From SimpleC.ASRTFUN Require Import list_lemma.
From SimpleC.ASRT Require Import ExprDef.
Require Import AUXLib.List_lemma.
From compcert.lib Require Import Coqlib.

Definition var_name : Type := ident * nat.

Definition var_name_eqb (a b : var_name) : bool := Pos.eqb (fst a) (fst b) && (Nat.eqb (snd a) (snd b)).

Inductive local : Type :=
  | Avar : var_name -> expr_val 0 -> local   (* addressable variable  [[&x]] = v *)
.

Definition local_eqb (l1 l2 : local) : bool :=
  match l1, l2 with
  | Avar id v, Avar id1 v1 => var_name_eqb id id1 && expr_val_eqb v v1
  end.

Definition local_list_eqb (L1 L2 : list local) : bool :=
  list_eqb local_eqb L1 L2.

Fixpoint eval_tmpval (l : list local) (x : var_name) : option (expr_val 0) :=
  match l with
  | nil => None
  | Avar x1 y1 :: l' => if var_name_eqb x1 x then Some y1 else eval_tmpval l' x
  end.

Fixpoint Change_local (l : list local) (x : var_name) (v : expr_val 0) : list local :=
  match l with
  | nil => nil
  | Avar x1 y1 :: l' =>
    if var_name_eqb x1 x then (Avar x1 v) :: l' else Avar x1 y1 :: Change_local l' x v
  end.

Definition Insert_local (l : list local) (x : var_name) (v : expr_val 0) : list local :=
  Avar x v :: l.
