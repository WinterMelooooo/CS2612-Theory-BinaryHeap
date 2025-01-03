From SimpleC.Common Require Import COps Notations.
From SimpleC.ASRT Require Import DefFiles.
From SimpleC.CSE Require Import Cexpr_def Cexpr_eval Cstate_def.
From compcert.lib Require Import Coqlib.

Local Open Scope option_monad_scope.

Section Sym_exec_version.

(* Variable Safety_checker : assertion -> list Proposition -> option bool. *)

Definition Skip_exec (Pre : assertion) : option Assertion := Some (Pre :: nil).

Definition Asgn_op (Asgn : CAssignType) (x y : expr_val) : expr_val :=
  match Asgn with
  | CO_ASSIGN => y
  | CO_PLUS_ASSIGN => Vbop Oadd x y
  | CO_MINUS_ASSIGN => Vbop Osub x y
  | CO_MUL_ASSIGN => Vbop Omul x y
  | CO_DIV_ASSIGN => Vbop Odiv x y
  | CO_MOD_ASSIGN => Vbop Omod x y
  | CO_AND_ASSIGN => Vbop Oand x y
  | CO_OR_ASSIGN => Vbop Oor x y
  | CO_XOR_ASSIGN => Vbop Oxor x y
  | CO_SHL_ASSIGN => Vbop Oshl x y
  | CO_SHR_ASSIGN => Vbop Oshr x y
  end.

Definition Asgn_exec (Pre : assertion) (Asgn : CAssignType) (x y : ACexpr) : option Assertion :=
  do x_l <- eval_ACexpr_l x Pre;
  Option_map_concat x_l (fun '(x_v, asrt1) =>
    do y_l <- eval_ACexpr y asrt1;
    Some (map (fun '(y_v, asrt2) =>
    (* TODO: safety check *)
      match Asgn with
      | CO_ASSIGN => Change_sep_in_asrt asrt2 x_v y_v
      | _ => Change_sep_in_asrt asrt2 x_v (Asgn_op Asgn x_v y_v)
      end
    ) y_l)
  ).

Definition Incdec_op (IncDec : CIncDecType) (x : expr_val) : expr_val :=
  match IncDec with
  | CO_INCPRE => Vbop Oadd x (EConstZ 1)
  | CO_INCPOST => Vbop Oadd x (EConstZ 1)
  | CO_DECPRE => Vbop Osub x (EConstZ 1)
  | CO_DECPOST => Vbop Osub x (EConstZ 1)
  end.

Definition Incdec_exec (Pre : assertion) (IncDec : CIncDecType) (x : ACexpr) : option Assertion :=
  do x_l <- eval_ACexpr_l x Pre;
  Option_map x_l (fun '(x_v, asrt1) =>
    do x_v <- eval_val (Sep_list asrt1) x_v;
    Some (Change_sep_in_asrt asrt1 x_v (Incdec_op IncDec x_v))
  ).

Definition Compute_exec (Pre : assertion) (x : ACexpr) : option Assertion :=
  do x_l <- eval_ACexpr x Pre;
  Some (map (fun '(x_v, asrt1) => asrt1) x_l).

Definition SimpleCommand_exec (Pre : assertion) (com : ACsimplecommand) : option Assertion :=
  match com with
  | AC_skip => Skip_exec Pre
  | AC_assign Asgn x y => Asgn_exec Pre Asgn x y
  | AC_incdec IncDec x => Incdec_exec Pre IncDec x
  | AC_compute x => Compute_exec Pre x
  end.

Definition Return_exec (Pre : assertion) (x : option ACexpr) : option (list Prod_ret) :=
  match x with
  | None => Some (mk_ret Pre None :: nil)
  | Some x' =>
    do x_l <- eval_ACexpr x' Pre;
    Some (map (fun '(x_v, asrt1) => mk_ret asrt1 (Some x_v)) x_l)
  end.

(* Definition Condition_exec (Pre : assertion) (x : Cexpr) (v : expr_val) : option (Assertion * Assertion) :=
  (** (x == v assertions , x!=v assertions) *)
  match Safe_eval Safety_checker x Pre with
    | None => None
    | Some res => Some (map (fun a => Insert_prop_in_asrt (snd a) (Be Pvequal (fst a) v)) res , map (fun a => Insert_prop_in_asrt (snd a) (Up Pnot (Be Pvequal (fst a) v))) res)
  end. *)

Definition SimpleCommand_exec_list (Pre : Assertion) (com : ACsimplecommand) : option Assertion :=
  Some_concat (map (fun a => SimpleCommand_exec a com) Pre).

Definition Return_exec_list (Pre : Assertion) (x : option ACexpr) : option (list Prod_ret) :=
  Some_concat (map (fun a => Return_exec a x) Pre).

Definition If_Condition_exec_list (Pre : Assertion) (x : ACexpr) : option (Assertion * Assertion) :=
  do x_l <- eval_ACexpr_Assertion x Pre;
  let then_res := concat (map (fun '(x_v, asrt) =>
    if expr_val_eqb x_v Vtrue then asrt :: nil else nil
  ) x_l) in
  let else_res := concat (map (fun '(x_v, asrt) =>
    if expr_val_eqb x_v Vfalse then asrt :: nil else nil
  ) x_l) in
  Some (then_res, else_res).
  (* let condition_res := map (fun a => Condition_exec a x Vtrue) Pre in
    if (Find_None condition_res) then None
    else let fres := concat (map (fun a => fst a) (Clear_option condition_res)) in
         let sres := concat (map (fun a => snd a) (Clear_option condition_res)) in
         Some (fres , sres). *)

Definition Switch_Condition_exec_list (Pre : Assertion) (x v : ACexpr) : option (Assertion * Z) :=
  do val <- expr_simple (ACexpr_to_Cexpr v);
  do x_l <- eval_ACexpr_Assertion x Pre;
  Some (concat (map (fun '(x_v, asrt) =>
    if expr_val_eqb x_v (EConstZ val) then asrt :: nil else nil
  ) x_l), val).

Definition Switch_Default_exec_list (Pre : Assertion) (x : ACexpr) (label_list : list Z) : option Assertion :=
  do x_l <- eval_ACexpr_Assertion x Pre;
  (* Checks if x_v equals to any label in the label_list *)
  let label_list_expr_val := map EConstZ label_list in
  Some (concat (map (fun '(x_v, asrt) =>
    if Find expr_val_eqb label_list_expr_val x_v then nil else (asrt :: nil)
  ) x_l)).
  (* match Some_concat (map (fun a => Safe_eval Safety_checker x a) Pre) with
    | Some eval_res =>
        Some (map (fun a => fold_right (fun P A => Insert_prop_in_asrt A P) (snd a) (map (fun b => Be Pvequal (fst a) (EConstZ b)) label_list) ) eval_res)
    | _ => None
  end. *)

End Sym_exec_version.