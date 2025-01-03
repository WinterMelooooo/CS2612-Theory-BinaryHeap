Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.
(* From SimpleC.SL Require Import SeparationLogic. *)
(* Import SeparationLogic.CRules. *)
From SimpleC.CSE Require Import Cexpr_def Assertion_denote.
From SimpleC.Common Require Import CTypes COps.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.ASRT Require Import DepList DefFiles.


(* Example empty_assertion : assertion := mk_A nil nil nil nil. *)
Example empty_Assertion : Assertion := nil.
(* Record AsrtProof := mk_AsrtProof {
  prop_pf : assertion -> Proposition -> option (* TODO: some proof type *) unit;
  entail_pf : assertion -> Assertion -> option (* TODO: some proof type *) unit;
  return_pf : list Prod_ret -> list Prod_ret -> option (* TODO: some proof type *) unit;
}. *)
Example empty_AsrtProof : AsrtProof := mk_AsrtProof (fun _ _ => None) (fun _ _ => None) (fun _ _ => None).

Example empty_AsrtInfo : AsrtInfo := AsrtInfo_Single empty_Assertion empty_AsrtProof.
(* 
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
 *)
Example C_i32 : SimpleCtype := CT_basic (CT_int Signed I32).
Example AC_const_1 : ACexpr := AC_const empty_AsrtInfo 1%Z C_i32.
Example AC_const_2 : ACexpr := AC_const empty_AsrtInfo 2%Z C_i32.
Example AC_1_plus_2 : ACexpr :=
  AC_binop empty_AsrtInfo CO_PLUS AC_const_1 AC_const_2 C_i32.

(* Record environment := {
    ty_env : TypeMapping;
    var_env : VarMapping ty_env;
    func_env : FuncMapping ty_env;
    pred_env : PredMapping ty_env;
    prop_env : PropMapping ty_env;
    field_addr : Mem.addr -> ident -> ident -> option Mem.addr;
}. *)


Example ty_map : TypeMapping := fun _ => Empty_set.
Example var_map : VarMapping ty_map := fun id ty => None.
Print FuncMapping.
Definition empty_func_map : FuncMapping ty_map := fun id sig => None.

Example Z_binop_sig : FuncSig := FSig (0%Z :: 0%Z :: nil) 0%Z.

Example func_map : FuncMapping ty_map :=
  update_func_mapping empty_func_map 1%positive Z_binop_sig Z.add.

(* Compute (FuncSig_denote ty_map Z_binop_sig). *)
Lemma func_map_1 : func_map 1%positive Z_binop_sig = Some (gen_func ty_map Z_binop_sig Z.add).
Proof.
  unfold func_map. unfold update_func_mapping.
  destruct (ident_eq_dec 1%positive 1%positive); try congruence.
  destruct (FuncSig.eq_dec Z_binop_sig Z_binop_sig); try congruence.
  rewrite <- EqdepTheory.eq_rect_eq.
  reflexivity.
Qed.

Example pred_map : PredMapping ty_map := fun id sig => None.
Example prop_map : PropMapping ty_map := fun id sig => None.


Example env : environment := {|
  ty_env := ty_map;
  var_env := var_map;
  func_env := func_map;
  pred_env := pred_map;
  prop_env := prop_map;
  field_addr := fun _ _ _ => None;
|}.


Example ev_const_1 : expr_val 0 := EConstZ 1%Z.
Example ev_const_2 : expr_val 0 := EConstZ 2%Z.
Example ev_1_plus_2 : expr_val 0 := EFunc 1%positive Z_binop_sig
  (expr_val_list_cons ev_const_1 (expr_val_list_cons ev_const_2 expr_val_list_nil)).

Lemma ev_1_plus_2_denote : expr_val_denote ev_1_plus_2 env = Some 3%Z.
Proof.
  unfold expr_val_denote. simpl.
  rewrite func_map_1. simpl.
  reflexivity.
Qed.

Example ev_var_x : expr_val 0 := EVar 1%positive 0%Z.
Example ev_var_y : expr_val 0 := EVar 2%positive 0%Z.
(* Compute (expr_val_denote ev_var_x env). *)
(* Example env' := update_var_env env 1%positive 0%Z 1%Z.
Example env'' := update_var_env env' 2%positive 0%Z 2%Z. *)
Example ev_x_plus_y : expr_val 0 := EFunc 1%positive Z_binop_sig
  (expr_val_list_cons ev_var_x (expr_val_list_cons ev_var_y expr_val_list_nil)).

Lemma plus_correct:
  forall (env : environment) (x_val y_val : Z),
  (env.(func_env) 1%positive Z_binop_sig = Some (gen_func env.(ty_env) Z_binop_sig Z.add)) ->
  (expr_val_denote ev_var_x env = Some x_val) ->
  (expr_val_denote ev_var_y env = Some y_val) ->
  (expr_val_denote ev_x_plus_y env = Some (Z.add x_val y_val)).
Proof.
  intros env x_val y_val H_func_map Hx Hy.
  unfold expr_val_denote. unfold ev_x_plus_y. simpl.
  rewrite H_func_map.
  unfold expr_val_denote in Hx, Hy.
  unfold ev_var_x, ev_var_y in Hx, Hy.
  rewrite Hx, Hy.
  simpl.
  reflexivity.
Qed.


Example ev_var_x' : expr_val 6 := EVar 1%positive 6%Z.
Example ev_var_y' : expr_val 6 := EVar 2%positive 6%Z.
Example binop_sig : FuncSig := FSig (6%Z :: 6%Z :: nil) 6%Z.
Example ev_x_plus_y' : expr_val 6 := EFunc 1%positive binop_sig
  (expr_val_list_cons ev_var_x' (expr_val_list_cons ev_var_y' expr_val_list_nil)).


(* Lemma how_to_prove : ... 
eq_rect Z (fun t : Type => t -> t -> t) Z.add (tylookup (ty_env env) 6) 
  (eq_sym pf) x_val y_val =
eq_rect Z (fun x : Type => x)
  (eq_rect (tylookup (ty_env env) 6) (fun x : Type => x) x_val Z pf +
   eq_rect (tylookup (ty_env env) 6) (fun x : Type => x) y_val Z pf)%Z
  (tylookup (ty_env env) 6) (eq_sym pf).
Admitted. *)

Lemma plus_correct' (env : environment) (x_val y_val : tylookup env.(ty_env) 6%Z)
  (t : Type) (add : t -> t -> t)
  (pf : tylookup env.(ty_env) 6%Z = t) :
  (env.(func_env) 1%positive binop_sig =
    Some (gen_func env.(ty_env) binop_sig (eq_rect _ (fun t => t -> t -> t) add _ (eq_sym pf)))) ->
  (expr_val_denote ev_var_x' env = Some x_val) ->
  (expr_val_denote ev_var_y' env = Some y_val) ->
  (expr_val_denote ev_x_plus_y' env = Some
    (eq_rect _ (fun x => x) (add (eq_rect _ (fun x => x) x_val _ pf)
      (eq_rect _ (fun x => x) y_val _ pf)) _ (eq_sym pf))).
Proof.
  intros H_func_map Hx Hy.
  unfold expr_val_denote. unfold ev_x_plus_y'. simpl.
  rewrite H_func_map.
  unfold expr_val_denote in Hx, Hy.
  unfold ev_var_x', ev_var_y' in Hx, Hy.
  rewrite Hx, Hy.
  simpl.
  subst t.
  reflexivity.
Qed.
