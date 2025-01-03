Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import SimpleC.Frontend.CTypes.
Require Import SimpleC.Common.COps.
Require Import SimpleC.Frontend.CExprs.

Inductive Designator : Type :=
  | Desig_index : CExpr -> Designator
  | Desig_field : string -> Designator
.

Definition Designation := list Designator.

Inductive Initializer : Type :=
  | Init_single: CExpr -> Initializer
  | Init_list: list (Designation * Initializer) -> Initializer
.

Record VarDecl: Type :=
  {
    var_expr: RightExpr;
    init_val: option Initializer;
  }.

Record VarsDecl :=
  {
    var_type: LeftType;
    declared_vars: list VarDecl;
  }.
