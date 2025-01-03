
From SimpleC.Common Require Import COps.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.ASRT Require Import DefFiles.
From compcert.lib Require Import Coqlib.
Require Import AUXLib.List_lemma.

Record AsrtProof := mk_AsrtProof {
  prop_pf : assertion -> Proposition -> option (* TODO: some proof type *) unit;
  entail_pf : assertion -> Assertion -> option (* TODO: some proof type *) unit;
  return_pf : list Prod_ret -> list Prod_ret -> option (* TODO: some proof type *) unit;
}.

Record FunCallWitness : Type := mk_FunCallWitness {
  arg_types: list Z;
  ret_type: Z;
  pre_call : list (expr_val ret_type * expr_val_list arg_types * assertion); (* fun_val, list of arg vals, pre condition *)
  post_call : list (option (expr_val ret_type) * assertion);
}.

Definition fun_pre_call_eqb {t1 t2 : Z} {types1 types2 : list Z}
    (l1 : list (expr_val t1 * expr_val_list types1 * assertion))
    (l2 : list (expr_val t2 * expr_val_list types2 * assertion)) : bool :=
  (* Check if l1 = l2 *)
  match list_eq_dec Z.eq_dec types1 types2 with
  | left eq_pf =>
    list_eqb (fun '(f1, args1, asrt1) '(f2, args2, asrt2) =>
      let args1' := expr_val_list_cast args1 eq_pf in
      expr_val_eqb f1 f2 && expr_val_list_eqb args1' args2 && assertion_eqb asrt1 asrt2) l1 l2
  | right _ => false
  end.

Inductive AsrtInfo : Type :=
  | AsrtInfo_Single : Assertion -> AsrtProof -> AsrtInfo
  | AsrtInfo_FunCall : Assertion -> Assertion -> AsrtProof -> FunCallWitness -> AsrtInfo
  | AsrtInfo_Empty : AsrtInfo.

Inductive ACexpr :=
  | AC_const : AsrtInfo -> Z -> SimpleCtype -> ACexpr
  | AC_var: AsrtInfo -> var_name -> SimpleCtype -> ACexpr
  | AC_deref: AsrtInfo -> ACexpr -> SimpleCtype -> ACexpr (* Assertion should contain the needed Sep info. *)
  | AC_addrof: AsrtInfo -> ACexpr -> SimpleCtype -> ACexpr
  | AC_unop: AsrtInfo -> CUop -> ACexpr -> SimpleCtype -> ACexpr
  | AC_binop: AsrtInfo -> CBinop -> ACexpr -> ACexpr -> SimpleCtype -> ACexpr
  | AC_cast: AsrtInfo -> ACexpr -> SimpleCtype -> ACexpr
  | AC_structfield: AsrtInfo -> ACexpr -> ident -> ident -> SimpleCtype -> ACexpr
  | AC_unionfield: AsrtInfo -> ACexpr -> ident -> ident -> SimpleCtype -> ACexpr
  | AC_sizeof: AsrtInfo -> SimpleCtype -> SimpleCtype -> ACexpr
  | AC_index: AsrtInfo -> ACexpr -> ACexpr -> SimpleCtype -> ACexpr
  | AC_call : AsrtInfo -> ACexpr -> list ACexpr -> SimpleCtype -> ACexpr
    (* After evaluating the arguments, the function is called, which transforms current Assertion to another Assertion. *)
.

Definition get_asrt_info (a : ACexpr) : AsrtInfo :=
  match a with
  | AC_const ai _ _ => ai
  | AC_var ai _ _ => ai
  | AC_deref ai _ _ => ai
  | AC_addrof ai _ _ => ai
  | AC_unop ai _ _ _ => ai
  | AC_binop ai _ _ _ _ => ai
  | AC_cast ai _ _ => ai
  | AC_structfield ai _ _ _ _ => ai
  | AC_unionfield ai _ _ _ _ => ai
  | AC_sizeof ai _ _ => ai
  | AC_index ai _ _ _ => ai
  | AC_call ai _ _ _ => ai
  end.

Inductive Cexpr :=
  | C_const : Z -> SimpleCtype -> Cexpr       (**r integer literal *)
  | C_var: var_name -> SimpleCtype -> Cexpr  (**r variable *)
  | C_deref: Cexpr -> SimpleCtype -> Cexpr    (**r pointer dereference (unary [*]) *)
  | C_addrof: Cexpr -> SimpleCtype -> Cexpr   (**r address-of operator ([&]) *)
  | C_unop: CUop -> Cexpr -> SimpleCtype -> Cexpr  (**r unary operation *)
  | C_binop: CBinop -> Cexpr -> Cexpr -> SimpleCtype -> Cexpr (**r binary operation *)
  | C_cast: Cexpr -> SimpleCtype -> Cexpr   (**r type cast ([(ty) e]) *)
  | C_structfield: Cexpr -> ident -> ident -> SimpleCtype -> Cexpr (**r access to a member of a struct, struct name, field name*)
  | C_unionfield: Cexpr -> ident -> ident -> SimpleCtype -> Cexpr (**r access to a member of a union, union name, field name*)
  | C_sizeof: SimpleCtype -> SimpleCtype -> Cexpr         (**r size of a type *)
  | C_index: Cexpr -> Cexpr -> SimpleCtype -> Cexpr (**r access to a member of a array*)
  | C_call : Cexpr -> list Cexpr -> SimpleCtype -> Cexpr (**r function call expr *)
.

Definition type_of_ACexpr (a : ACexpr) : SimpleCtype :=
  match a with
  | AC_const _ _ t => t
  | AC_var _ _ t => t
  | AC_deref _ _ t => t
  | AC_addrof _ _ t => t
  | AC_unop _ _ _ t => t
  | AC_binop _ _ _ _ t => t
  | AC_cast _ _ t => t
  | AC_structfield _ _ _ _ t => t
  | AC_unionfield _ _ _ _ t => t
  | AC_sizeof _ t _ => t
  | AC_index _ _ _ t => t
  | AC_call _ _ _ t => t
  end.

Definition type_of (c : Cexpr) : SimpleCtype :=
  match c with
  | C_const _ t => t
  | C_var _ t => t
  | C_deref _ t => t
  | C_addrof _ t => t
  | C_unop _ _ t => t
  | C_binop _ _ _ t => t
  | C_cast _ t => t
  | C_structfield _ _ _ t => t
  | C_unionfield _ _ _ t => t
  | C_sizeof _ t => t
  | C_index _ _ t => t
  | C_call _ _ t => t
  end.

Inductive ACsimplecommand :=
  | AC_skip : ACsimplecommand
  | AC_assign : CAssignType -> ACexpr -> ACexpr -> ACsimplecommand
  | AC_incdec : CIncDecType -> ACexpr -> ACsimplecommand
  | AC_compute : ACexpr -> ACsimplecommand
.

Inductive Csimplecommand :=
  | C_skip : Csimplecommand
  | C_assign : CAssignType -> Cexpr -> Cexpr -> Csimplecommand
  | C_incdec : CIncDecType -> Cexpr -> Csimplecommand
  | C_compute : Cexpr -> Csimplecommand
.

Inductive ACstatement  :=
  | AC_simple : ACsimplecommand -> ACstatement
  | AC_seq : ACstatement -> ACstatement -> ACstatement
  | AC_if : ACexpr -> ACstatement -> ACstatement -> ACstatement
  | AC_while (cond: ACexpr) (inv: Assertion) (pf: AsrtProof) (body: ACstatement)
  | AC_dowhile (cond: ACexpr) (inv: Assertion) (pf: AsrtProof) (body: ACstatement)
  | AC_for (init: ACsimplecommand) (cond: ACexpr) (incr: ACsimplecommand) (body: ACstatement)
           (inv: Assertion) (pf: AsrtProof)
  | AC_break : ACstatement
  | AC_continue : ACstatement
  | AC_switch : ACexpr -> list (ACexpr * ACstatement) -> ACstatement -> ACstatement
    (* This defnition does not support switch (cond) { int a; case ... } *)
  | AC_return : option ACexpr -> ACstatement
  | AC_assert : Assertion -> AsrtProof -> ACstatement
  | AC_block : ACstatement -> ACstatement
  | AC_vardef : list (var_name * option ACexpr * SimpleCtype) -> ACstatement
.

Inductive Cstatement :=
  | C_simple : Csimplecommand -> Cstatement
  | C_seq : Cstatement -> Cstatement -> Cstatement
  | C_if : Cexpr -> Cstatement -> Cstatement -> Cstatement
  | C_while : Cexpr -> Cstatement -> Cstatement
  | C_dowhile : Cexpr -> Cstatement -> Cstatement
  | C_for : Csimplecommand -> Cexpr -> Csimplecommand -> Cstatement -> Cstatement
  | C_break : Cstatement
  | C_continue : Cstatement
  | C_switch : Cexpr -> list (Cexpr * Cstatement) -> Cstatement -> Cstatement
    (* This defnition does not support switch (cond) { int a; case ... } *)
  | C_return : option Cexpr -> Cstatement
  | C_block : Cstatement -> Cstatement
  | C_vardef : list (var_name * option Cexpr * SimpleCtype) -> Cstatement
.

Inductive partial_statement : Type :=
  | PS_simple : ACsimplecommand -> partial_statement
  | PS_break : partial_statement                       (* [break] statement *)
  | PS_continue : partial_statement                    (* [continue] statement *)
  | PS_return : option ACexpr -> partial_statement     (* [return] statement *)
  | PS_while (cond: ACexpr) (inv: Assertion) (pf: AsrtProof)  (* while (b) { **)
  | PS_if : ACexpr -> partial_statement                 (* if (b) { *)
  | PS_else : partial_statement                         (* } else { *)
  (* | PS_while_for_do : ACexpr -> partial_statement *)  (* } while (b)*)
  | PS_block_begin : partial_statement
  | PS_block_end : partial_statement
  (* We transform 'do { body } while (b)' to 'body; while (b) { body }', so we no longer need PS_do *)
  (* | PS_do (body: list partial_statement) (inv: Assertion) (pf: AsrtProof) *)  (* do { *)
  | PS_for (init: ACsimplecommand) (cond: ACexpr) (incr: ACsimplecommand)
           (inv: Assertion) (pf: AsrtProof)  (* for (c1;e2;c3) {*)
  | PS_switch : ACexpr -> partial_statement  (* switch (b) { *)
  | PS_case : ACexpr -> partial_statement  (* case b : *)
  | PS_default : partial_statement  (* default : *)
  | PS_assert : Assertion -> AsrtProof -> partial_statement
  | PS_vardef : list (var_name * option ACexpr * SimpleCtype) -> partial_statement
.

Record program : Type := mk_program {
  P_func : list (funcspec * option ACstatement);
  (* P_funpred : list FuncDef_input; *)
  (* P_seppred : list SepDef_input; *)
  P_vardef : list (var_name * option ACexpr * SimpleCtype);
  P_structdef : list (ident * (list (ident * SimpleCtype)));
  P_uniondef : list (ident * (list (ident * SimpleCtype)));
  P_enumdef : list (ident * option nat * list ident);
}.

Inductive partial_program : Type :=
  | PP_funcdecl : funcspec -> partial_program (** type fname (arg_list) funcspecs ; *)
  | PP_funcdef : funcspec -> partial_program  (** type fname (arg_list) funcspecs { *)
  (* | PP_funpred : FuncDef_input -> partial_program *)
  (* | PP_seppred : SepDef_input -> partial_program *)
  | PP_vardef : list (var_name * option ACexpr * SimpleCtype) -> partial_program
  | PP_structdef : ident -> list (ident * SimpleCtype) -> partial_program  (** name { vardef_list }*)
  | PP_uniondef : ident -> list (ident * SimpleCtype)  -> partial_program (** name { vardef_list }*)
  | PP_enumdef : ident -> option nat -> list ident -> partial_program  (** name { name_list }*)
  | PP_statement : partial_statement -> partial_program
  | PP_block_end : partial_program
.


Fixpoint ACexpr_to_Cexpr (a : ACexpr) : Cexpr :=
  match a with
  | AC_const _ z t => C_const z t
  | AC_var _ v t => C_var v t
  | AC_deref _ e t => C_deref (ACexpr_to_Cexpr e) t
  | AC_addrof _ e t => C_addrof (ACexpr_to_Cexpr e) t
  | AC_unop _ op e t => C_unop op (ACexpr_to_Cexpr e) t
  | AC_binop _ op a1 a2 t => C_binop op (ACexpr_to_Cexpr a1) (ACexpr_to_Cexpr a2) t
  | AC_cast _ e t => C_cast (ACexpr_to_Cexpr e) t
  | AC_structfield _ e id1 id2 t => C_structfield (ACexpr_to_Cexpr e) id1 id2 t
  | AC_unionfield _ e id1 id2 t => C_unionfield (ACexpr_to_Cexpr e) id1 id2 t
  | AC_sizeof _ t1 t2 => C_sizeof t1 t2
  | AC_index _ a1 a2 t => C_index (ACexpr_to_Cexpr a1) (ACexpr_to_Cexpr a2) t
  | AC_call _ f args t => C_call (ACexpr_to_Cexpr f) (map ACexpr_to_Cexpr args) t
  end.

Definition option_ACexpr_to_option_Cexpr (a : option ACexpr) : option Cexpr :=
  match a with
  | None => None
  | Some a0 => Some (ACexpr_to_Cexpr a0)
  end.

Fixpoint ACStmt_to_ps  (stmt : ACstatement) : list partial_statement :=
  match stmt with
  | AC_simple scmd => PS_simple scmd :: nil
  | AC_seq c1 c2 => (ACStmt_to_ps c1) ++ (ACStmt_to_ps c2)
  | AC_if cond THEN ELSE =>
    PS_if cond :: (ACStmt_to_ps THEN) ++
    PS_else :: (ACStmt_to_ps ELSE) ++ PS_block_end :: nil
  | AC_while cond inv pf body =>
    PS_while cond inv pf :: (ACStmt_to_ps body) ++ PS_block_end :: nil
  | AC_dowhile cond inv pf body =>
    (* We transform 'do { body } while (b)' to 'body; while (b) { body }' *)
    (ACStmt_to_ps body) ++ PS_while cond inv pf :: (ACStmt_to_ps body) ++ PS_block_end :: nil
  | AC_for init cond Incr body inv pf =>
    PS_for init cond Incr inv pf :: (ACStmt_to_ps body) ++ PS_block_end :: nil
  | AC_break => PS_break :: nil
  | AC_continue => PS_continue :: nil
  | AC_switch cond cases default =>
    PS_switch cond :: nil ++
    concat (map (fun a => PS_case (fst a) :: ACStmt_to_ps (snd a)) cases) ++
    PS_default :: (ACStmt_to_ps default) ++ PS_block_end :: PS_block_end :: nil
  | AC_return x => PS_return x :: nil
  | AC_assert asrts pf => PS_assert asrts pf :: nil
  | AC_block body =>
    PS_block_begin :: (ACStmt_to_ps body) ++ PS_block_end :: nil
  | AC_vardef var_list => PS_vardef var_list :: nil
  end.


Definition ACsimplecommand_to_Csimplecommand (scmd : ACsimplecommand) : Csimplecommand :=
  match scmd with
  | AC_skip => C_skip
  | AC_assign asgn x y => C_assign asgn (ACexpr_to_Cexpr x) (ACexpr_to_Cexpr y)
  | AC_incdec IncDec x => C_incdec IncDec (ACexpr_to_Cexpr x)
  | AC_compute x => C_compute (ACexpr_to_Cexpr x)
  end.

Fixpoint ACStmt_to_CStmt (stmt : ACstatement) : Cstatement :=
  match stmt with
  | AC_simple scmd => C_simple (ACsimplecommand_to_Csimplecommand scmd)
  | AC_seq c1 c2 =>
    C_seq (ACStmt_to_CStmt c1) (ACStmt_to_CStmt c2)
  | AC_if cond THEN ELSE =>
    C_if (ACexpr_to_Cexpr cond) (ACStmt_to_CStmt THEN) (ACStmt_to_CStmt ELSE)
  | AC_while cond _ _ body =>
    C_while (ACexpr_to_Cexpr cond) (ACStmt_to_CStmt body)
  | AC_dowhile cond _ _ body =>
    C_dowhile (ACexpr_to_Cexpr cond) (ACStmt_to_CStmt body)
  | AC_for init cond Incr body _ _ =>
    C_for
      (ACsimplecommand_to_Csimplecommand init)
      (ACexpr_to_Cexpr cond)
      (ACsimplecommand_to_Csimplecommand Incr)
      (ACStmt_to_CStmt body)
  | AC_break => C_break
  | AC_continue => C_continue
  | AC_switch cond cases default =>
    C_switch (ACexpr_to_Cexpr cond)
      (concat (map (fun a => (ACexpr_to_Cexpr (fst a), ACStmt_to_CStmt (snd a)) :: nil) cases))
      (ACStmt_to_CStmt default)
  | AC_return x => C_return (option_ACexpr_to_option_Cexpr x)
  | AC_assert _ _ => C_simple C_skip
  | AC_block body =>
    C_block (ACStmt_to_CStmt body)
  | AC_vardef var_list =>
    C_vardef (map (fun a: var_name * option ACexpr * SimpleCtype => match a with (v, e, t) =>
      (v, option_ACexpr_to_option_Cexpr e, t) end) var_list)
  end.

Section Remove_skip_Case.
  Variable Remove_skip : Cstatement -> Cstatement.
  Definition Remove_skip_case (stmt : list (Cexpr * Cstatement)) : list (Cexpr * Cstatement) :=
    map (fun a => (fst a, Remove_skip (snd a))) stmt.
End Remove_skip_Case.

Fixpoint Remove_skip (c : Cstatement) : Cstatement :=
  match c with
  | C_seq c1 c2 =>
    match Remove_skip c1, Remove_skip c2 with
    | C_simple C_skip , c20 => c20
    | c10, C_simple C_skip => c10
    | c10 , c20 => C_seq c10 c20
    end
  | C_if e c1 c2 => C_if e (Remove_skip c1) (Remove_skip c2)
  | C_while e c1 => C_while e (Remove_skip c1)
  | C_dowhile e c1 => C_dowhile e (Remove_skip c1)
  | C_for init e incr c1 => C_for init e incr (Remove_skip c1)
  | C_block c1 => C_block (Remove_skip c1)
  | C_switch cond cases default =>
    (C_switch cond (Remove_skip_case Remove_skip cases) (Remove_skip default))
  | _ => c
  end.

Definition Remove_skip_option (c : option Cstatement) : option Cstatement :=
  match c with
  | None => None
  | Some c0 => Some (Remove_skip c0)
  end.
