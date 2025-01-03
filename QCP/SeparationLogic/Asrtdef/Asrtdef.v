(* This file contains the syntax tree and some related functions of assertions *)

From SimpleC.ASRTFUN Require Import list_lemma.
From SimpleC.ASRT Require Import ExprDef LocalDef PropDef SepDef Error.
From compcert.lib Require Import Coqlib.
Require Import AUXLib.List_lemma.

Record assertion := mk_A {
  Prop_list : list Proposition;
  Local_list : list local;
  Sep_list : list Separation;
  Exist_list : list ident;
}.

Record Prod_ret := mk_ret {
  Assert_r : assertion ;
  Return : option (expr_val 0);
}.

Record Prod_error := mk_error {
  Assert_e : assertion;
  Errorm : Error;
}.

Definition Assertion := list assertion.

Record funcdes := mk_func {
   Args : list var_name; (* function argument list *)
   With_clause : list ident; (* logical variable list *)
   Precon : assertion ;
   Postcon : Prod_ret;
}.

Definition funcspec : Type := ident * list funcdes.

(* Inductive Self_Rec : Type :=
  | Selfrec : list expr_val -> Self_Rec
.

Record SepDef_input : Type := mkSDef {
  Sname : ident ;
  Svar : list ident ;
  Scondition : list (list Proposition * list (Separation + Self_Rec) * list ident);
}.

Record FuncDef_input : Type := mkFDef {
  Fname : ident ;
  Fvar : list ident ;
  Fcondition : list (list Proposition);
}. *)



Definition asrt_to_error  (P : list assertion) :=
  map (fun a => mk_error a ok) P.

Definition Exist_list_eqb (E1 E2 : list ident) : bool :=
  list_eqb Pos.eqb E1 E2.

Definition assertion_eqb  (Ass1 Ass2 : assertion) : bool :=
  Prop_list_eqb (Prop_list Ass1) (Prop_list Ass2) &&
  local_list_eqb (Local_list Ass1) (Local_list Ass2) &&
  Sep_list_eqb (Sep_list Ass1) (Sep_list Ass2) &&
  Exist_list_eqb (Exist_list Ass1) (Exist_list Ass2).

Definition Prod_ret_eqb  (Ass1 Ass2 : Prod_ret) : bool :=
  assertion_eqb (Assert_r Ass1) (Assert_r Ass2) &&
  option_eqb expr_val_eqb (Return Ass1) (Return Ass2).

Definition Prod_error_eqb  (Ass1 Ass2 : Prod_error) : bool :=
  assertion_eqb (Assert_e Ass1) (Assert_e Ass2) &&
  error_eqb (Errorm Ass1) (Errorm Ass2).

Definition assertion_list_eqb  (Ass1 Ass2 : list assertion) : bool :=
  list_eqb assertion_eqb Ass1 Ass2.

Definition Prod_ret_list_eqb (Ret1 Ret2 : list Prod_ret) : bool :=
  list_eqb Prod_ret_eqb Ret1 Ret2.

Definition Prop_add  (P : Proposition) (asrt : assertion) : assertion :=
  mk_A (P :: Prop_list asrt) (Local_list asrt) (Sep_list asrt) (Exist_list asrt).

Definition eval_Ctmpval (asrt : assertion) (id : var_name) : option (expr_val 0) :=
  eval_tmpval (Local_list asrt) id.

Definition Change_local_in_asrt  (asrt : assertion) (id : var_name) (v : expr_val 0) : assertion :=
  mk_A (Prop_list asrt) (Change_local (Local_list asrt) id v) (Sep_list asrt) (Exist_list asrt).

Definition Insert_local_in_asrt  (asrt : assertion) (id : var_name) (v : expr_val 0) : assertion :=
  mk_A (Prop_list asrt) (Insert_local (Local_list asrt) id v) (Sep_list asrt) (Exist_list asrt).

Definition Change_sep_in_asrt  (asrt : assertion) (x y: expr_val 0) : assertion :=
  mk_A (Prop_list asrt) (Local_list  asrt) (Change_sep (Sep_list asrt) x y) (Exist_list asrt).

Definition Insert_prop_in_asrt  (asrt : assertion) (P : Proposition) : assertion :=
  mk_A (P :: Prop_list asrt) (Local_list asrt) (Sep_list asrt) (Exist_list asrt).

Definition Gen_Pre  (func : funcspec) : list assertion :=
  map (fun a => Precon a) (snd func).

Definition Gen_Posts  (func : funcspec) : list Prod_ret :=
  map (fun a => (Postcon a)) (snd func).