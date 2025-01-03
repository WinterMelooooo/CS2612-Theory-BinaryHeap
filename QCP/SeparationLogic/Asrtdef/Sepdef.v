(* This file contains the syntax tree and some related functions of Separation *)
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.ASRTFUN Require Import list_lemma.
From SimpleC.ASRT Require Import ExprDef LocalDef PropDef Error.
From compcert.lib Require Import Coqlib.
Require Import AUXLib.List_lemma.

Inductive Separation : Type :=
  | DataAt (addr : expr_val 0) (ty : SimpleCtype) (val : expr_val (Ctype_to_expr_type ty))
  | UndefDataAt (addr : expr_val 0) (ty : SimpleCtype)
  | SepPred (f : ident) (sig : PredSig) (args : expr_val_list (get_pred_sig_args sig))
.


Definition Separation_eqb (s1 s2: Separation) : bool :=
  match s1, s2 with
  | DataAt e1 t1 e1', DataAt e2 t2 e2' =>
    (expr_val_eqb e1 e2) && (expr_val_eqb e1' e2') && (SimpleCtype.eqb t1 t2)
  | UndefDataAt e t , UndefDataAt e1 t1 =>
    (expr_val_eqb e e1) && (SimpleCtype.eqb t t1)
  | SepPred id1 _ arg_list1 , SepPred id2 _ arg_list2 =>
    Pos.eqb id1 id2 && expr_val_list_eqb arg_list1 arg_list2
  | _ , _ => false
  end.

Definition Sep_list_eqb (S1 S2 : list Separation) : bool :=
  list_eqb Separation_eqb S1 S2.

Fixpoint eval_val (s : list Separation) (addr : expr_val 0) (ty : Z): option (expr_val ty) :=
  match s with
  | nil => None
  | h :: s' =>
    match h with
    | DataAt x t v =>
      if expr_val_eqb x addr then
        match Z.eq_dec (Ctype_to_expr_type t) ty with
        | left pf => Some (expr_val_cast v pf)
        | right _ => None
        end
      else eval_val s' addr ty
    | _ => eval_val s' addr ty
    end
  end.

Fixpoint Change_sep (s : list Separation) (addr : expr_val 0) {ty : Z} (val : expr_val ty)
 : list Separation :=
  match s with
  | nil => nil
  | h :: s' =>
    match h with
    | DataAt a t v =>
      if (expr_val_eqb a addr) then
        match Z.eq_dec ty (Ctype_to_expr_type t) with
        | left pf => (DataAt a t (expr_val_cast val pf)) :: s'
        | right _ => h :: Change_sep s' addr val
        end
      else h :: Change_sep s' addr val
    | UndefDataAt e t =>
      if (expr_val_eqb e addr) then
        match Z.eq_dec ty (Ctype_to_expr_type t) with
        | left pf => (DataAt e t (expr_val_cast val pf)) :: s'
        | right _ => h :: Change_sep s' addr val
        end
      else h :: Change_sep s' addr val
    | _ => h :: Change_sep s' addr val
    end
  end.
