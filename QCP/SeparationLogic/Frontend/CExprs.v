Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import SimpleC.Frontend.CTypes.
Require Import SimpleC.Common.COps.

Inductive CExpr :=
  | CE_const : Z -> CExpr (* n *)
  | CE_var: string -> CExpr (* x *)
  | CE_deref: CExpr -> CExpr (* *se *)
  | CE_addrof: CExpr -> CExpr (* &se *)
  | CE_unop: CUop -> CExpr -> CExpr (* op se *)
  | CE_binop: CBinop -> CExpr -> CExpr -> CExpr (* se1 op se2 *)
  | CE_cast: LeftType -> RightExpr -> CExpr -> CExpr (* (T)se *)
  | CE_field: CExpr -> string -> CExpr (* se.field *)
  | CE_efield: CExpr -> string -> CExpr (* se->field *)
  | CE_sizeof: LeftType -> RightExpr -> CExpr (* sizeof(T) *)
  | CE_index: CExpr -> CExpr -> CExpr (* a[se] *)
  | CE_call : CExpr -> list CExpr -> CExpr (* f(e1, e2, ...) *)
.
