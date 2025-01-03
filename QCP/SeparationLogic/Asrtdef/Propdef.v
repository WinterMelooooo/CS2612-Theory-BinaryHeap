(* This file contains the syntax tree and some related functions of Proposition *)

From SimpleC.ASRTFUN Require Import list_lemma.
From SimpleC.ASRT Require Import DepList ExprDef LocalDef.
From compcert.lib Require Import Coqlib.
Require Import AUXLib.List_lemma.

Inductive Unary_prop_op : Type :=
  | Pnot : Unary_prop_op       (**r ! a *)
.

Inductive Binary_prop_op : Type :=
  | Por : Binary_prop_op  (**r a || b *)
  | Pand : Binary_prop_op (**r a && b *)
  | Pimply : Binary_prop_op (**r a -> b *)
  | Piff : Binary_prop_op (**r a <-> b *)
.

Inductive Unary_expr_op : Type :=
  | Pisptr : Unary_expr_op
  | Pis_pointer_or_null : Unary_expr_op
.

Inductive Binary_expr_op : Type :=
  | Pvle : Binary_expr_op  (**r a <=v b *)
  | Pvge : Binary_expr_op  (**r a >=v b *)
  | Pvlt : Binary_expr_op  (**r a <v b *)
  | Pvgt : Binary_expr_op  (**r a >v b *)
  | Pvequal : Binary_expr_op  (**r a =v b *)
.

Inductive Quantifier : Type :=
  | PForall : Quantifier  (**r Forall x , P x *)
  | PExists : Quantifier  (**r Exists x , P x *)
.

Inductive Proposition : Type :=
  | TT : Proposition (** True Proposition *)
  | FF : Proposition (** False Proposition*)
  | Up : Unary_prop_op -> Proposition -> Proposition
  | Bp : Binary_prop_op -> Proposition -> Proposition -> Proposition
  | Ue : Unary_expr_op -> expr_val 0 -> Proposition
  | Be : Binary_expr_op -> expr_val 0 -> expr_val 0 -> Proposition
  | Fn (f : ident) (sig : PredSig) (args : Induct.dlist expr_val (get_pred_sig_args sig))
  | Qf : Quantifier -> ident -> Proposition -> Proposition
.


Definition Up_eqb (x y : Unary_prop_op) : bool :=
  match x , y with
    | Pnot , Pnot => true
  end.

Definition Bp_eqb (x y : Binary_prop_op) : bool :=
  match x , y with
    | Por , Por => true
    | Pand , Pand => true
    | Pimply , Pimply => true
    | Piff , Piff => true
    | _ , _ => false
  end.

Definition Ue_eqb (x y : Unary_expr_op) : bool :=
  match x , y with
    | Pisptr , Pisptr => true
    | Pis_pointer_or_null , Pis_pointer_or_null => true
    | _ , _ => false
  end.

Definition Be_eqb (x y : Binary_expr_op) : bool :=
  match x , y with
    | Pvle , Pvle => true
    | Pvge , Pvge => true
    | Pvlt , Pvlt => true
    | Pvgt , Pvgt => true
    | Pvequal , Pvequal => true
    | _ , _ => false
  end.

Fixpoint Proposition_eqb (p1 p2 : Proposition) : bool :=
  match p1, p2 with
    | TT , TT => true
    | FF , FF => true
    | Up op P , Up op' P' => Up_eqb op op' && Proposition_eqb P P'
    | Bp op P P1, Bp op' P' P1' => Bp_eqb op op' && Proposition_eqb P P' && Proposition_eqb P1 P1'
    | Ue op e , Ue op' e' => Ue_eqb op op' && expr_val_eqb e e'
    | Be op e e1 , Be op' e' e1' => Be_eqb op op' && expr_val_eqb e e' && expr_val_eqb e1 e1'
    | _ , _ => false
  end.

Definition Prop_list_eqb (P1 P2 : list Proposition) : bool :=
  list_eqb Proposition_eqb P1 P2.

Definition eval_Prop (P : list Proposition) (p: Proposition) : option bool :=
  let occur := Find Proposition_eqb P p in
  if occur then Some true else
  let neg_p := Up Pnot p in
  let neg_occur := Find Proposition_eqb P neg_p in
  if neg_occur then Some false else None.

Definition eval_Prop_list (P : list Proposition) (ps: list Proposition) : bool :=
  let res := map (eval_Prop P) ps in
  All_Some_true res.
