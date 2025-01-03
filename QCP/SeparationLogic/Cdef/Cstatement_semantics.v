From SimpleC.ASRT Require Import DefFiles.
From SimpleC.Common Require Import CTypes.
From SimpleC.Common Require Import COps.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.CSE Require Import Cexpr_def Cstate_def Cexpr_val_helper Cexpr_semantics.
From compcert.lib Require Import Coqlib Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.

From AUXLib Require Import relations.

Local Open Scope sets.
Section Stmt_semantics.

Variable env : prog_env.
Variable callees: val -> prog_state -> list val -> prog_state -> val -> Prop.
Variable return_val : int64.

Definition Asgn_op_denote (Asgn : CAssignType) (t : SimpleCtype) (v1 v2 v : val) : Prop :=
  match Asgn with 
    | CO_ASSIGN => False 
    | CO_PLUS_ASSIGN => arith_denote1 t val_add v1 v2 v 
    | CO_MINUS_ASSIGN => arith_denote1 t val_sub v1 v2 v
    | CO_MUL_ASSIGN => arith_denote1 t val_mul v1 v2 v  
    | CO_DIV_ASSIGN => arith_denote2 t val_div v1 v2 v   
    | CO_MOD_ASSIGN => arith_denote2 t val_mod v1 v2 v  
    | CO_AND_ASSIGN => arith_denote1 t val_and v1 v2 v
    | CO_OR_ASSIGN => arith_denote1 t val_or v1 v2 v    
    | CO_XOR_ASSIGN => arith_denote1 t val_xor v1 v2 v   
    | CO_SHL_ASSIGN => arith_denote1 t val_shl v1 v2 v   
    | CO_SHR_ASSIGN => arith_denote1 t val_shr v1 v2 v  
  end.

Definition Asgn_denote (op : CAssignType)(x y : Cexpr) (Pre Post : prog_state) : Prop := 
  if (SimpleCtype.eqb (type_of x) (type_of y) && Stored_able (type_of x)) then 
  exists v' Post', eval_Cexprval_l_denote env callees x Pre v' Post' /\
   exists v2 Post'', eval_Cexprval_denote env callees y Post' v2 Post'' /\ 
   match op with 
     | CO_ASSIGN => state_eq (Split_mem v' v2 Post'') Post
     | _ => exists v1, Merge_mem v' (type_of x) Post'' = Some v1 /\ 
            exists v, Asgn_op_denote op (type_of x) v1 v2 v /\ 
              state_eq (Split_mem v' v Post'') Post  
   end
  else False.

Definition Incdec_op_denote (IncDec : CIncDecType)(t : SimpleCtype) (v1 v2 v : val) : Prop :=
  match IncDec with 
    | CO_INCPRE => arith_denote1 t val_add v1 v2 v      
    | CO_INCPOST => arith_denote1 t val_add v1 v2 v    
    | CO_DECPRE => arith_denote1 t val_sub v1 v2 v     
    | CO_DECPOST => arith_denote1 t val_sub v1 v2 v    
  end.

Definition IncDec_denote (op : CIncDecType) (x : Cexpr) (Pre Post : prog_state) : 
Prop := 
  exists v' Post', eval_Cexprval_l_denote env callees x Pre v' Post' /\
    exists v1, Merge_mem v' (type_of x) Post' = Some v1 /\
      exists v2 , Some v2 = One (type_of x) /\  
            exists v, Incdec_op_denote op (type_of x) v1 v2 v /\ 
              state_eq (Split_mem v' v Post') Post.


Definition Csimplecommand_denote (c : Csimplecommand) : FinDnt :=
  match c with 
    | C_skip => mk_Fin Rels.id ∅ ∅ ∅
    | C_assign op x y => mk_Fin (Asgn_denote op x y) ∅ ∅ ∅ 
    | C_incdec op x => mk_Fin (IncDec_denote op x) ∅ ∅ ∅ 
    | C_compute x => mk_Fin (fun Pre Post => exists v, eval_Cexprval_denote env callees x Pre v Post) ∅ ∅ ∅
  end.

Definition Cseq_denote (D1 D2 : FinDnt) : FinDnt :=
  mk_Fin ((NormalExit D1) ∘ (NormalExit D2)) 
         ((BreakExit D1) ∪ ((NormalExit D1) ∘ (BreakExit D2)))
         ((ContExit D1) ∪ ((NormalExit D1) ∘ (ContExit D2)))
         ((ReturnExit D1) ∪((NormalExit D1) ∘ (ReturnExit D2))).

Definition Cbreak_denote : FinDnt :=
  mk_Fin ∅ Rels.id ∅ ∅.

Definition Ccont_denote : FinDnt :=
  mk_Fin ∅ ∅ Rels.id ∅.

Definition Cret_denote (v : option Cexpr) : FinDnt :=
  mk_Fin ∅ ∅ ∅ (match v with 
                  | None => (fun a b => state_eq a b /\ Merge_mem return_val (CT_basic (CT_int Unsigned I64)) b = None)
                  | Some x => (fun a b => exists b' x0, eval_Cexprval_denote env callees x a x0 b' /\ 
                                              state_eq (Split_mem return_val x0 b') b)
                end).

Definition Truth_denote (cond : Cexpr) : prog_state -> prog_state -> Prop :=
  match (One (type_of cond)) with 
    | None => ∅
    | Some v => (fun a b => eval_Cexprval_denote env callees cond a v b)
  end.

Definition Falth_denote (cond : Cexpr) : prog_state -> prog_state -> Prop :=
  match (Zero (type_of cond)) with 
    | None => ∅
    | Some v => (fun a b => eval_Cexprval_denote env callees cond a v b)
  end.

Definition Cif_denote (cond : Cexpr) (Truth Falth : FinDnt) : FinDnt :=
  mk_Fin (((Truth_denote cond) ∘ (NormalExit Truth)) ∪ ((Falth_denote cond) ∘ (NormalExit Falth))) 
         (((Truth_denote cond) ∘ (BreakExit Truth)) ∪ ((Falth_denote cond) ∘ (BreakExit Falth)))
         (((Truth_denote cond) ∘ (ContExit Truth)) ∪ ((Falth_denote cond) ∘ (ContExit Falth)))
         (((Truth_denote cond) ∘ (ReturnExit Truth)) ∪ ((Falth_denote cond) ∘ (ReturnExit Falth))).

Definition loop_denote (Truth Falth Normbody Breakbody Contbody Retbody Incr : prog_state -> prog_state -> Prop) : FinDnt := 
  mk_Fin (BW_LFix (fun X => (Truth ∘ Normbody ∘ Incr ∘ X) ∪ Falth ∪ (Truth ∘ Contbody ∘ Incr ∘ X) ∪ (Truth ∘ Breakbody))) 
         ∅ ∅
         (BW_LFix (fun X => (Truth ∘ Normbody ∘ Incr ∘ X) ∪ (Truth ∘ Contbody ∘ Incr ∘ X) ∪ (Truth ∘ Retbody))). 

Definition Cwhile_denote (cond : Cexpr) (body : FinDnt) : FinDnt := 
  loop_denote (Truth_denote cond) (Falth_denote cond) (NormalExit body) (BreakExit body) (ContExit body) (ReturnExit body) (NormalExit (Csimplecommand_denote C_skip)).

Definition Cdowhile_denote (cond : Cexpr) (body : FinDnt) : FinDnt :=
  let Truth := Truth_denote cond in 
  let Falth := Falth_denote cond in 
  mk_Fin (BW_LFix (fun X => ((NormalExit body) ∘ Truth ∘ X) ∪ ((NormalExit body) ∘ Falth) ∪ ((ContExit body) ∘ Truth ∘ X) ∪ (BreakExit body))) 
         ∅ ∅
         (BW_LFix (fun X => ((NormalExit body) ∘ Truth ∘ X) ∪ ((ContExit body) ∘ Truth ∘ X) ∪ (ReturnExit body))).

Definition Cfor_denote (init : FinDnt) (cond : Cexpr) (Incr body : FinDnt) : FinDnt := 
  Cseq_denote init (loop_denote (Truth_denote cond) (Falth_denote cond) (NormalExit body) (BreakExit body) (ContExit body) (ReturnExit body) (NormalExit Incr)).

Section Cswitch_denote_sec.
Variable statement_denote : Cstatement -> FinDnt.

(** The false condition , cases exec *)
Fixpoint Ccase_denote (cond : Cexpr) (cases : list (Cexpr * Cstatement)) (default : FinDnt) : (prog_state -> prog_state -> Prop) * FinDnt * FinDnt :=
  match cases with 
    | nil => (Rels.id, default , mk_Fin ∅ ∅ ∅ ∅)
    | (v , body_v) :: cases' => let (fst_mes , res) := Ccase_denote cond cases' default in 
                                let (falth , body) := fst_mes in 
                                let new_body := Cseq_denote (statement_denote body_v) body in 
                                let Falth := Falth_denote (C_binop CO_EQ cond v (type_of cond)) in 
                                let Truth := Truth_denote (C_binop CO_EQ cond v (type_of cond)) in
                                ( Falth ∩ falth , 
                                  new_body,  
                                  mk_Fin ((Truth ∘ (NormalExit new_body)) ∪ (NormalExit res))
                                         ((Truth ∘ (BreakExit new_body)) ∪ (BreakExit res))
                                         ((Truth ∘ (ContExit new_body)) ∪ (ContExit res))
                                         ((Truth ∘ (ReturnExit new_body)) ∪ (ReturnExit res))
                                )                                     
  end.   
  
Fixpoint Valid_cases_expr (label_list : list Cexpr) : list Z * bool := 
  match label_list with 
    | nil => (nil , true)
    | a :: l' => let (res , flag) := Valid_cases_expr l' in
                 if flag then  
                   match expr_simple a with 
                     | Some v => (v :: res , negb (Find Z.eqb res v))
                     | None => (nil , false)
                   end
                 else (nil , false)
  end.

Definition Cswitch_denote (cond : Cexpr) (cases : list (Cexpr * Cstatement)) (default : Cstatement) :  FinDnt :=
  if (snd (Valid_cases_expr (map (fun a => fst a) cases))) then 
    let defaults := statement_denote default in
    let (fst_mes , res) := Ccase_denote cond cases defaults in 
    let (falth , body) := fst_mes in 
    mk_Fin ((falth ∘ (NormalExit defaults)) ∪ NormalExit res ∪ (falth ∘ (BreakExit defaults)) ∪ BreakExit res)
           ∅
           ((falth ∘ (ContExit defaults)) ∪ ContExit res)
           ((falth ∘ (ReturnExit defaults)) ∪ ReturnExit res)
  else mk_Fin ∅ ∅ ∅ ∅.
End Cswitch_denote_sec.

Fixpoint Cstatement_denote (c : Cstatement) : FinDnt :=
  match c with 
    | C_simple cmd => Csimplecommand_denote cmd 
    | C_seq c1 c2 => Cseq_denote (Cstatement_denote c1) (Cstatement_denote c2) 
    | C_if cond c1 c2 => Cif_denote cond (Cstatement_denote c1) (Cstatement_denote c2)
    | C_while cond c1 => Cwhile_denote cond (Cstatement_denote c1) 
    | C_dowhile cond c1 => Cdowhile_denote cond (Cstatement_denote c1) 
    | C_for init cond Incr c1 => Cfor_denote (Csimplecommand_denote init) cond (Csimplecommand_denote Incr) (Cstatement_denote c1) 
    | C_break => Cbreak_denote
    | C_continue => Ccont_denote 
    | C_switch cond cases default => Cswitch_denote Cstatement_denote cond cases default 
    | C_return v => Cret_denote v
    | C_block c => Cstatement_denote c
    | C_vardef _ => mk_Fin Rels.id ∅ ∅ ∅
  end.

End Stmt_semantics.
