From SimpleC.ASRT Require Import DefFiles DepList.
From SimpleC.Common Require Import Notations.
Local Open Scope option_monad_scope.
From SimpleC.CSE Require Import Cexpr_def Cstate_def.
From compcert.lib Require Import Coqlib Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.

From SimpleC.SL Require Import SeparationLogic.
From SimpleC.SL Require Mem.
Import CRules.
Local Open Scope sac_scope.

Definition VarType : Type := ident * Z. (* variable name and type *)
Definition VarList : Type := list VarType.

Definition TypeMapping : Type := Z -> Type.

Definition tylookup (ty_env : TypeMapping) (ty : Z) : Type :=
  if (Z.eq_dec ty 0) then Z
  else ty_env ty.

Definition function_type_denote (ret : Type) (args : list Type) : Type :=
  fold_right (fun ty ret => ty -> ret) ret args.

Definition update_type_mapping (ty_env : TypeMapping) (ty : Z) (v : Type) :=
  fun ty' =>
    match (Z.eq_dec ty ty') with
    | left _ => v
    | right _ => ty_env ty'
    end.

Definition VarMapping (ty_env : TypeMapping) : Type :=
    forall (n : ident) (ty : Z), option (tylookup ty_env ty).

Definition FuncSig_denote (ty_env : TypeMapping) (sig : FuncSig) : Type :=
    Induct.dlist (fun ty => tylookup ty_env ty) (get_func_sig_args sig) ->
    tylookup ty_env (get_func_sig_ret sig).

(* Definition PredSig_denote (ty_env : TypeMapping) (ret : Type) (sig : PredSig) : Type :=
    Induct.dlist (fun ty => tylookup ty_env ty) (get_pred_sig_args sig) ->
    ret. *)


Definition FuncMapping (ty_env : TypeMapping) : Type :=
  forall (n : ident) (sig : FuncSig), option (FuncSig_denote ty_env sig).

Record environment := {
    ty_env : TypeMapping;
    var_env : VarMapping ty_env;
    func_env : FuncMapping ty_env;
    field_addr : Mem.addr -> ident -> ident -> option Mem.addr;
}.

Definition gen_func (ty_env : TypeMapping) (sig : FuncSig)
                    (f : function_type_denote (tylookup ty_env (get_func_sig_ret sig)) (map (tylookup ty_env) (get_func_sig_args sig))) : FuncSig_denote ty_env sig.
    destruct sig; unfold FuncSig_denote; intros.
    induction X.
    - exact f.
    - exact (IHX (f x)).
Defined.

Definition update_var_mapping {ty_env : TypeMapping} (var_env : VarMapping ty_env)
    (id : ident) (ty : Z) (v : tylookup ty_env ty) : VarMapping ty_env :=
  fun id' ty' => if (Pos.eqb id id') then
    match (Z.eq_dec ty ty') with
    | left pf => Some (eq_rect _ (tylookup ty_env) v _ pf)
    | right _ => var_env id' ty'
    end
  else var_env id' ty'.

Definition update_var_env (env : environment)
    (id : ident) (ty : Z) (v : tylookup env.(ty_env) ty) : environment :=
  Build_environment
    env.(ty_env)
    (update_var_mapping (var_env env) id ty v)
    env.(func_env)
    env.(pred_env)
    env.(prop_env)
    env.(field_addr).

Definition update_func_mapping {ty_env : TypeMapping} (env : FuncMapping ty_env)
    (n : ident) (sig : FuncSig) (f : function_type_denote (tylookup ty_env (get_func_sig_ret sig)) (map (tylookup ty_env) (get_func_sig_args sig)))  :=
  fun n' sig' =>
    match (ident_eq_dec n n') with
    | left _ => match (FuncSig.eq_dec sig sig') with
                | left H => eq_rect _ (fun sig => option (FuncSig_denote ty_env sig)) (Some (gen_func ty_env sig f)) _ H
                | right _ => env n' sig'
                end
    | right _ => env n' sig'
    end.

Definition pred_mapping_update {ty_env : TypeMapping} (env : PredMapping ty_env)
    (n : ident) (sig : PredSig) (f : function_type_denote Assertion (map (tylookup ty_env) (get_pred_sig_args sig))) :=
  fun n' sig' =>
    match (ident_eq_dec n n') with
    | left _ => match (PredSig.eq_dec sig sig') with
                | left H => eq_rect _ (fun sig => option (PredSig_denote ty_env expr sig)) (Some (gen_pred ty_env sig Assertion f)) _ H
                | right _ => env n' sig'
                end
    | right _ => env n' sig'
    end.

Definition prop_mapping_update {ty_env : TypeMapping} (n : ident) (sig : PredSig) (f : function_type_denote Prop (map (tylookup ty_env) (get_pred_sig_args sig))) (env : PropMapping ty_env) :=
  fun n' sig' =>
    match (ident_eq_dec n n') with
    | left _ => match (PredSig.eq_dec sig sig') with
                | left H => eq_rect _ (fun sig => option (PredSig_denote ty_env Prop sig)) (Some (gen_pred ty_env sig Prop f)) _ H
                | right _ => env n' sig'
                end
    | right _ => env n' sig'
    end.

Fixpoint expr_val_denote {ty : Z} (x : expr_val ty) (env: environment)
    : option (tylookup env.(ty_env) ty) :=
  match x in expr_val ty return option (tylookup env.(ty_env) ty) with
  | EConstZ z => Some z
  | EVar id ty => (env.(var_env) id ty)
  | EField v id1 id2 =>
    do v0 <- expr_val_denote v env;
    env.(field_addr) v0 id1 id2
  | EFunc f_id sig arg =>
    do f <- env.(func_env) f_id sig;
    do arg_list <- Induct.dmap_option (fun _ x => expr_val_denote x env) arg;
    do f_denote <- env.(func_env) f_id sig;
    Some (f_denote arg_list)
  end.

Definition Unary_prop_denote (op : Unary_prop_op) (P : Prop) : Prop :=
  match op with
  | Pnot => ~ P
  end.

Definition Binary_prop_denote (op : Binary_prop_op) (P1 P2 : Prop) : Prop :=
  match op with
  | Por => P1 \/ P2
  | Pand => P1 /\ P2
  | Pimply => P1 -> P2
  | Piff => P1 <-> P2
  end.

Definition Unary_expr_denote (op : Unary_expr_op) (e : option (expr_val 0)) : Prop :=
  match op with
  | Pis_pointer_or_null => e <> None
  | Pisptr => e <> None /\ e <> Some (EConstZ 0)
  end.



(* Parameter env : prog_env.
Parameter callees: val -> prog_state -> list val -> prog_state -> val -> Prop. *)
(* TODO: Z vs int64? *)
(* Parameter return_val : int64.
Parameter Funcpred_denote : ident -> list int64 -> option int64.
Parameter Seppred_denote : ident -> list int64 -> Prop. *)

(* Definition Uop_denote (op : unary_operation) (x : option int64) : option int64 :=
  match x with
  | None => None
  | Some a => match op with
              | Oneg => Some (Int64.neg a)
              | Onint => Some (Int64.not a)
              | Onot => if (Int64.eq a (Int64.repr 0)) then Some (Int64.repr 1)
                        else Some (Int64.repr 0)
              end
  end.

Definition Binop_denote (op : binary_operation) (x y: option int64) : option int64 :=
  match x , y with
  | Some a , Some b =>
    match op with
    | Oadd => Some (Int64.add a b)
    | Osub => Some (Int64.sub a b)
    | Omul => Some (Int64.mul a b)
    | Odiv => if (Int64.eq b (Int64.repr 0)) then None
              else Some (Int64.divs a b)
    | Omod => if (Int64.eq b (Int64.repr 0)) then None
              else Some (Int64.mods a b)
    | Oand => None
    | Oor => None
    | Oxor => None
    | Oshl => None
    | Oshr => None
    end
  | _ , _ => None
  end. *)

(* Definition var_assignment: Type := ident -> int64. *)
(* Definition update_var (J : var_assignment) (id : ident) (v : int64) : var_assignment :=
  fun id' => if (Pos.eqb id id') then v else J id'. *)



(* Module SL (CRules: SeparationLogicSig).

(* Modle Names: LanguageSig. *)

  Definition model : Type := prog_state.
  Definition expr := model -> Prop.
  Definition join : model -> model -> model -> Prop := prog_state_join.
  Definition is_unit : model -> Prop := prog_state_empty.

(* End LanguageSig. *)

Include DerivedNamesSig.

(* LogicRule <: PrimitiveRuleSig Names *)

  Theorem unit_join : (forall n : model, exists u : model, is_unit u /\ join n u n) .
  Proof.
    intros. exists empty_prog_state.
    unfold is_unit , join. unfold prog_state_empty, prog_state_join. simpl.
    repeat split.
    - apply vars_addr_join_empty2.
    - Mem.solve_empmem.
  Qed.

  Theorem unit_spec : (forall n m u : model, is_unit u -> join n u m -> n = m) .
  Proof.
    intros n m u H1 H2.
    unfold is_unit, join in *.
    destruct u.
    unfold prog_state_empty in H1. simpl in H1. destruct H1 as [H1a H1b].
    apply vars_addr_empty_IS_empty_vars_addr' in H1a.
    apply Mem.mem_empty_IS_empty_mem' in H1b.
    rewrite H1a, H1b in H2.
    symmetry.
    apply prog_state_join_emp_r. auto.
  Qed.

  Definition join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) := prog_state_join_comm.

  Definition join_assoc : (forall mx my mz mxy mxyz : model,
      join mx my mxy -> join mxy mz mxyz -> exists myz : model,
      join my mz myz /\ join mx myz mxyz) := prog_state_join_assoc2.

(* End Rules. *)

Include LogicTheoremSig'.



(* The following are basic definitions *)

Definition mstore (p: addr) (v: Z): expr :=
  fun st => (mem st) = Mem.single_byte_mem p v.

Definition mstore_noninit (p: addr): expr :=
  fun st => (((mem st) = Mem.single_Noninit_mem p) \/ (exists v, (mem st) = Mem.single_byte_mem p v)).

Theorem mstore_mstore_noninit:
  forall p v s,
    mstore p v s ->
    mstore_noninit p s.
Proof.
  unfold mstore, mstore_noninit.
  intros.
  right.
  eauto.
Qed.

Theorem dup_mstore_noninit:
  forall x,
    derivable1
      (sepcon (mstore_noninit x) (mstore_noninit x))
      (coq_prop False).
Proof.
  unfold mstore_noninit, sepcon, derivable1.
  intros.
  destruct H as [m1 [m2 [? [Hm1 Hm2]]]].
  destruct m as [J m], m1 as [J1 m1], m2 as [J2 m2].
  unfold join, prog_state_join, Mem.mem_join in H. simpl in *.
  destruct H as [_ H]. exfalso. clear J J1 J2.
  specialize (H x).
  unfold Mem.single_Noninit_mem, Mem.single_byte_mem in *.
  destruct Hm1 as [? | [? ?]]; destruct Hm2 as [? | [? ?]]; subst;
  assert (Htrue: Mem.addr_eqb x x = true) by apply Z.eqb_refl; rewrite Htrue in H;
  Mem.my_destruct H.
Qed.

Include DerivedPredSig. *)


(* Definition Binary_expr_denote (op : Binary_expr_op) (e1 e2 : option (expr_val 0)) : Prop :=
  match e1 , e2 with
  | Some v1 , Some v2 =>
    match op with
    | Pvle => Z.le v1 v2 = true
    | Pvge => Int64.cmp Cge v1 v2 = true
    | Pvlt => Int64.cmp Clt v1 v2 = true
    | Pvgt => Int64.cmp Cgt v1 v2 = true
    | Pvequal => Int64.cmp Ceq v1 v2 = true
    end
  | _ , _ => False
  end. *)

(* Local Open Scope sac_scope. *)

(* Fixpoint Prop_denote (x : Proposition) (env : environment) : Prop :=
  match x with
  | PropDef.TT => True
  | PropDef.FF => False
  | Up op p => Unary_prop_denote op (Prop_denote p env)
  | Bp op p1 p2 => Binary_prop_denote op (Prop_denote p1 env) (Prop_denote p2 env)
  | Ue op e => Unary_expr_denote op (expr_val_denote 0 e env)
  | Be op e1 e2 => Binary_expr_denote op (expr_val_denote J e1) (expr_val_denote J e2)
  | Qf op id p =>
    match op with
    | PForall => forall a : int64 , Prop_denote p (update_var_env env id a)
    | PExists => exists a : int64 , Prop_denote p (update_var_env env J id a)
    end
  end. *)

Definition Prop_denote (x : Proposition) (env : environment) : Prop := False.

(* Definition Local_denote (x : local) (env : environment) : Prop :=
  match x with
    | Avar id v => eval_id_addr (st.(vars_addr) :: nil) (fst id) = expr_val_denote J v
  end. *)

(* Definition mem_join (m1 m2 m: int64 -> mem_var): Prop :=
  forall i,
    (m1 i = Noperm /\ m2 i = Noperm /\ m i = Noperm) \/
    (m1 i = Noperm /\ m2 i = Noninit /\ m i = Noninit) \/
    (m1 i = Noninit /\ m2 i = Noperm /\ m i = Noninit) \/
    (exists i', m1 i = Noperm /\ m2 i = value i' /\ m i = value i') \/
    (exists i', m1 i = value i' /\ m2 i = Noperm /\ m i = value i'). *)

(* Definition Sep_denote (J : var_assignment) (x : Separation) (st : prog_state) : Prop :=
  match x with
  | DataAt v t addr =>
    match expr_val_denote J v , expr_val_denote J addr with
    | Some v0 , Some addr0 =>
      exists n n1 v1, addr0 = Int64.repr n /\ v0 = Int64.repr n1 /\
                n <= Int64.max_unsigned /\ n >= 0 /\
                Some v1 = Merge_mem addr0 t st /\
                const_denote n1 t v1
    | _ , _ => False
    end
  | UndefDataAt addr t =>
    match expr_val_denote J addr with
    | Some addr0 =>
        exists n, addr0 = Int64.repr n /\ n <= Int64.max_unsigned /\ n >= 0
    | _ => False
    end
  | SepPred id arg_list => let args := map (expr_val_denote J) arg_list in
                          if (Find_None args) then False
                          else Seppred_denote id (Clear_option args)
  end. *)

Definition Pure_asrt_denote (asrt : assertion) (env : environment) : expr :=
  truep.
  (* fold_left and (map (fun a => Local_denote J a st) asrt.(Local_list)) True /\
  fold_left and (map (fun a => Sep_denote J a st) asrt.(Sep_list)) True. *)

(* Fixpoint Add_Exist_denote (Exists_list : list ident) (asrt : assertion) : prog_state -> Prop :=
  match Exists_list with
  | nil => Pure_asrt_denote J asrt
  | a :: l' => (fun st => exists a0 : int64, Add_Exist_denote (fun id => if (Pos.eqb id a) then a0 else J id) l' asrt st)
  end.

Definition Assertion_denote (J : var_assignment) (asrt : assertion) : prog_state -> Prop :=
  Add_Exist_denote J asrt.(Exist_list) asrt. *)
(* End SL. *)





(* Definition Mult_Assertion_denote (J : var_assignment) (Asrt : Assertion) (st : prog_state) : Prop :=
  exists asrt , (In asrt Asrt -> Assertion_denote J asrt st).

Definition Correct_denote (v : val) (x : option int64) : Prop :=
  exists n , x = Some (Int64.repr n) /\ const_denote n (type_of_val v) v.

Definition Post_denote (J : var_assignment) (v : val) (asrts : list (expr_val * assertion)) (st : prog_state) : Prop :=
  exists v0 asrt, In (v0 , asrt) asrts /\
    Correct_denote v (expr_val_denote J v0) /\
    Assertion_denote J asrt st. *)
