From SimpleC.ASRT Require Import DefFiles.
From SimpleC.Common Require Import CTypes COps Notations.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.CSE Require Import Cexpr_def Cstate_def.
From compcert.lib Require Import Coqlib Integers.

Local Open Scope option_monad_scope.


(* Section eval_ACexpr_list_section.
Variable (ty : Z).
Variable (eval_ACexpr : ACexpr -> assertion -> option (list (expr_val ty * assertion))).
Fixpoint eval_ACexpr_list
    (x : list ACexpr) (Asrt : assertion) : option (list ((list (expr_val ty)) * assertion)) :=
  match x with
  | nil => Some nil
  | x' :: l' =>
    do x_l <- eval_ACexpr x' Asrt;
    Option_map_concat x_l (fun '(x_v, asrt) =>
      do l_res <- eval_ACexpr_list l' asrt;
      Option_map l_res (fun '(val_list, post) =>
        Some (x_v :: val_list, post)
      )
    )
  end.
End eval_ACexpr_list_section. *)


Definition get_expr_val_type (e : ACexpr) : Z :=
  Ctype_to_expr_type (type_of_ACexpr e).

Fixpoint get_expr_val_types (l : list ACexpr) : list Z :=
  match l with
  | nil => nil
  | x :: l' => get_expr_val_type x :: get_expr_val_types l'
  end.

Definition eval_ACexpr_list
    (eval_ACexpr : forall x : ACexpr, assertion -> option (list (expr_val (get_expr_val_type x) * assertion))) :=
  fix eval_ACexpr_list (x : list ACexpr) (asrt : assertion)
      : option (list (expr_val_list (get_expr_val_types x) * assertion)) :=
    match x with
    | nil => Some nil
    | x' :: l' =>
      do x_l <- eval_ACexpr x' asrt;
      Option_map_concat x_l (fun '(x_v, asrt) =>
        do l_res <- eval_ACexpr_list l' asrt;
        Option_map l_res (fun '(val_list, post) =>
          Some (expr_val_list_cons x_v val_list, post)
        )
      )
    end.


Definition Safe_cond (t : SimpleCtype) (v : expr_val 0) : list Proposition :=
  match t with
  | CT_basic (CT_int s i) =>
      Be Pvle v (EConstZ (max_int s i)) ::
      Be Pvge v (EConstZ (min_int s i)) :: nil
  | _ => FF :: nil
  end.

Definition Safe_cond_neg (t : SimpleCtype) (v : expr_val 0) : list Proposition :=
  match t with
  | CT_basic (CT_int Signed i) =>
      Up Pnot (Be Pvequal v (EConstZ (min_int Signed i))) :: nil
  | CT_basic (CT_int Unsigned _) => nil
  | _ => FF :: nil
  end.

Definition Safe_cond_nonzero (t : SimpleCtype) (v : expr_val 0) : list Proposition :=
  match t with
  | CT_basic (CT_int s i) =>
      Up Pnot (Be Pvequal v (EConstZ 0)) :: nil
  | _ => FF :: nil
  end.

Definition eval_unop {ty : Z}
    (safe_cond : expr_val ty -> list Proposition)
    (f : expr_val ty -> expr_val ty)
    (asrt: assertion) (e : ACexpr)
    (eval_ACexpr: forall x : ACexpr, assertion -> option (list (expr_val (get_expr_val_type x) * assertion)))
      : option (list (expr_val ty * assertion)) :=
  let e_ty := get_expr_val_type e in
  match Z.eq_dec e_ty ty with
  | left pf =>
    do l <- eval_ACexpr e asrt;
    Option_map l (fun '(v, asrt) =>
      let v := expr_val_cast v pf in
      match eval_Prop_list (Prop_list asrt) (safe_cond v) with
      | true => Some (f v, asrt)
      | _ => None
      end
    )
  | _ => None
  end.
  (* do l <- eval_ACexpr e asrt;
  Option_map l (fun '(v, asrt) =>
    match eval_func (get_expr_val_type e) with
    | None => None
    | Some ef =>
      match eval_Prop_list (Prop_list asrt) (ef.(safe_cond) v) with
      | true => Some (ef.(f) v, asrt)
      | _ => None
      end
    end
  ). *)

Definition eval_binop {ty : Z}
    (safe_cond : expr_val ty -> expr_val ty -> list Proposition)
    (f : expr_val ty -> expr_val ty -> expr_val ty)
    (asrt: assertion) (e1 : ACexpr) (e2 : ACexpr)
    (eval_ACexpr: forall x : ACexpr, assertion -> option (list (expr_val (get_expr_val_type x) * assertion)))
      : option (list (expr_val ty * assertion)) :=
  let e1_ty := get_expr_val_type e1 in
  let e2_ty := get_expr_val_type e2 in
  match Z.eq_dec e1_ty ty, Z.eq_dec e2_ty ty with
  | left pf1, left pf2 =>
    do l1 <- eval_ACexpr e1 asrt;
    Option_map_concat l1 (fun '(v1, asrt1) =>
      let v1 := expr_val_cast v1 pf1 in
      do l2 <- eval_ACexpr e2 asrt1;
      Option_map l2 (fun '(v2, asrt2) =>
        let v2 := expr_val_cast v2 pf2 in
        match eval_Prop_list (Prop_list asrt2) (safe_cond v1 v2) with
        | true => Some (f v1 v2, asrt2)
        | _ => None
        end
      )
    )
  | _, _ => None
  end.
  (* do l1 <- eval_ACexpr e1 asrt;
  Option_map_concat l1 (fun '(v1, asrt1) =>
    match eval_Prop_list (Prop_list asrt1) (safe_cond v1) with
    | true =>
      do l2 <- eval_ACexpr e2 asrt1;
      Option_map l2 (fun '(v2, asrt2) =>
        match eval_Prop_list (Prop_list asrt2) (safe_cond v2) with
        | true => Some (f v1 v2, asrt2)
        | _ => None
        end)
    | _ => None
    end
  ). *)
Definition dup_safe_cond {ty : Z} (safe_cond : expr_val ty -> list Proposition)
    : expr_val ty -> expr_val ty -> list Proposition :=
  fun v1 v2 => safe_cond v1 ++ safe_cond v2.
(* Definition eval_binop_2cond {ty : Z}
  (safe_cond1 safe_cond2 : expr_val ty -> list Proposition)
  (f : expr_val ty -> expr_val ty -> expr_val ty)
  (asrt: assertion) (e1 : ACexpr) (e2 : ACexpr)
  (eval_ACexpr: ACexpr -> assertion -> option (list (expr_val ty * assertion))) :=
do l1 <- eval_ACexpr e1 asrt;
Option_map_concat l1 (fun '(v1, asrt1) =>
  match eval_Prop_list (Prop_list asrt1) (safe_cond1 v1) with
  | true =>
    do l2 <- eval_ACexpr e2 asrt1;
    Option_map l2 (fun '(v2, asrt2) =>
      match eval_Prop_list (Prop_list asrt2) (safe_cond2 v2) with
      | true => Some (f v1 v2, asrt2)
      | _ => None
      end)
  | _ => None
  end
). *)
(* Definition eval_binop (f : expr_val -> expr_val -> expr_val) (l : list (expr_val * assertion)) (x1 : expr_val * assertion) (t : SimpleCtype) :=
  Some (map (fun '(v, asrt) => (f (fst x1) v, asrt)) *)

(* Definition eval_binop1 (f : expr_val -> expr_val -> expr_val) (l : option (list (expr_val * list Proposition * assertion))) (x1 : expr_val * list Proposition) (t : SimpleCtype) :=
  match l with
    | None => None
    | Some l0 => Some (map (fun a => (f (fst x1) (fst (fst a)) , Safe_cond (f (fst x1) (fst (fst a))) t ++ (snd x1) ++ (snd (fst a)) , snd a)) l0)
  end.

Definition eval_binop2 (f : expr_val -> expr_val -> expr_val) (l : option (list (expr_val * list Proposition * assertion))) (x1 : expr_val * list Proposition) (t : SimpleCtype) :=
  match l with
    | None => None
    | Some l0 => Some (map (fun a => (f (fst x1) (fst (fst a)) , Up Pnot (Be Pvequal (fst (fst a)) (EConstZ 0)) :: Safe_cond (f (fst x1) (fst (fst a))) t ++ (snd x1) ++ (snd (fst a)) , snd a)) l0)
  end.

Definition eval_binop3 (f : expr_val -> expr_val -> expr_val) (l : option (list (expr_val * list Proposition * assertion))) (x1 : expr_val * list Proposition) (t : SimpleCtype) : option (list (expr_val * list Proposition * assertion)) := None. *)

Definition eval_cmpop
    (f : expr_val 0 -> expr_val 0 -> Proposition)
    (asrt: assertion) (e1 : ACexpr) (e2 : ACexpr)
    (eval_ACexpr: forall x : ACexpr, assertion -> option (list (expr_val (get_expr_val_type x) * assertion))) :=
  do l1 <- eval_ACexpr e1 asrt;
  Option_map_concat l1 (fun '(v1, asrt1) =>
    do l2 <- eval_ACexpr e2 asrt1;
    Option_map l2 (fun '(v2, asrt2) =>
      match Z.eq_dec (get_expr_val_type e1) 0, Z.eq_dec (get_expr_val_type e2) 0 with
      | left pf1, left pf2 =>
        let v1 := expr_val_cast v1 pf1 in
        let v2 := expr_val_cast v2 pf2 in
        match eval_Prop (Prop_list asrt2) (f v1 v2) with
        | Some true => Some (Vtrue, asrt2)
        | Some false => Some (Vfalse, asrt2)
        | _ => None
        end
      | _, _ => None
      end
    )
  ).
(* Definition eval_cmpop {ty : Z}
    (f : expr_val ty -> expr_val ty -> Proposition)
    (asrt: assertion) (e1 : ACexpr) (e2 : ACexpr)
    (eval_ACexpr: ACexpr -> assertion -> option (list (expr_val ty * assertion))) :=
  do l1 <- eval_ACexpr e1 asrt;
  Option_map_concat l1 (fun '(v1, asrt1) =>
    do l2 <- eval_ACexpr e2 asrt1;
    Option_map l2 (fun '(v2, asrt2) =>
      match eval_Prop (Prop_list asrt2) (f v1 v2) with
      | Some true => Some (Vtrue, asrt2)
      | Some false => Some (Vfalse, asrt2)
      | _ => None
      end
    )
  ). *)



Definition check_AsrtInfo (pre: assertion) (asrt_info: AsrtInfo) : option Assertion :=
  match asrt_info with
  | AsrtInfo_Single asrt pf =>
    match pf.(entail_pf) pre asrt with
    | None => None
    | Some _ =>
      (* TODO: proof valid check *)
      Some asrt
    end
  | AsrtInfo_FunCall pre' post' pf call_wit =>
    match pf.(entail_pf) pre pre' with
    | None => None
    | Some _ =>
      (* TODO: proof valid check *)
      (* TODO: call_wit check *)
      Some pre'
    end
  | AsrtInfo_Empty =>
    Some (pre :: nil)
  end.

Fixpoint eval_ACexpr 
    (* (ty : Z) *)
    (x : ACexpr) (pre : assertion)
    (* : option (list (expr_val ty * assertion)) := *)
    : option (list (expr_val (get_expr_val_type x) * assertion)) :=
  do Asrt <- check_AsrtInfo pre (get_asrt_info x);
  let ty := get_expr_val_type x in
  Option_map_concat Asrt (fun asrt : assertion =>
    match x with
    | AC_const _ i t =>
      match ty with
      | 0 => Some ((EConstZ i, asrt) :: nil)
      | _ => None
      end
    | AC_var _ id t =>
      do v_addr <- eval_Ctmpval asrt id;
      do v <- eval_val (Sep_list asrt) v_addr ty;
      Some ((v, asrt) :: nil)
    | AC_deref Asrt x' t =>
      do v' <- eval_ACexpr x' asrt;
      match Z.eq_dec (get_expr_val_type x') 0 with
      | left pf =>
        Option_map v' (fun '(v, asrt) =>
          do v <- eval_val (Sep_list asrt) (expr_val_cast v pf) ty;
          Some (v, asrt)
        )
      | _ => None
      end
    | AC_addrof _ x' t =>
      match ty return option (list (expr_val ty * assertion)) with
      | 0 => eval_ACexpr_l x' asrt
      | _ => None
      end
    | AC_unop _ op x' t =>
      match ty return option (list (expr_val ty * assertion)) with
      | 0 =>
        match op with
        | CO_NOTINT => None
        | CO_NOTBOOL => eval_unop (Safe_cond t) (unary_op_expr Onot) asrt x' (eval_ACexpr)
        | CO_UMINUS => eval_unop (fun v => Safe_cond t v ++ Safe_cond_neg t v) (unary_op_expr Oneg) asrt x' (eval_ACexpr)
        | CO_UPLUS => eval_unop (Safe_cond t) (fun a => a) asrt x' (eval_ACexpr)
        end
      | _ => None
      end
    | AC_binop _ op x1 x2 t =>
      check (SimpleCtype.eqb (type_of_ACexpr x1) (type_of_ACexpr x2));
      match ty return option (list (expr_val ty * assertion)) with
      | 0 =>
        match op with
        | CO_PLUS  => eval_binop (dup_safe_cond (Safe_cond t)) (binary_op_expr Oadd) asrt x1 x2 (eval_ACexpr)
        | CO_MINUS => eval_binop (dup_safe_cond (Safe_cond t)) (binary_op_expr Osub) asrt x1 x2 (eval_ACexpr)
        | CO_MUL => eval_binop (dup_safe_cond (Safe_cond t)) (binary_op_expr Omul) asrt x1 x2 (eval_ACexpr)
        | CO_DIV => eval_binop (fun a b => Safe_cond t a ++ Safe_cond t b ++ Safe_cond_nonzero t b)
            (binary_op_expr Odiv) asrt x1 x2 (eval_ACexpr)
        | CO_MOD => eval_binop (fun a b => Safe_cond t a ++ Safe_cond t b ++ Safe_cond_nonzero t b)
            (binary_op_expr Omod) asrt x1 x2 (eval_ACexpr)

        | CO_AND => eval_binop (dup_safe_cond (Safe_cond t)) (binary_op_expr Oand) asrt x1 x2 eval_ACexpr
        | CO_OR  => eval_binop (dup_safe_cond (Safe_cond t)) (binary_op_expr Oor)  asrt x1 x2 eval_ACexpr
        | CO_XOR => eval_binop (dup_safe_cond (Safe_cond t)) (binary_op_expr Oxor) asrt x1 x2 eval_ACexpr
        | CO_SHL => eval_binop (dup_safe_cond (Safe_cond t)) (binary_op_expr Oshl) asrt x1 x2 eval_ACexpr
        | CO_SHR => eval_binop (dup_safe_cond (Safe_cond t)) (binary_op_expr Oshr) asrt x1 x2 eval_ACexpr

        | CO_EQ => eval_cmpop (Be Pvequal) asrt x1 x2 eval_ACexpr
        | CO_NE => eval_cmpop (fun a b => Up Pnot (Be Pvequal a b)) asrt x1 x2 eval_ACexpr
        | CO_LT => eval_cmpop (Be Pvlt) asrt x1 x2 eval_ACexpr
        | CO_GT => eval_cmpop (Be Pvgt) asrt x1 x2 eval_ACexpr
        | CO_LE => eval_cmpop (Be Pvle) asrt x1 x2 eval_ACexpr
        | CO_GE => eval_cmpop (Be Pvge) asrt x1 x2 eval_ACexpr

        | CO_BAND =>
          do vl <- eval_ACexpr x1 asrt;
          Option_map_concat vl (fun '(v1, asrt1) =>
            if expr_val_eqb v1 Vtrue then
              do vr <- eval_ACexpr x2 asrt1;
              Option_map_concat vr (fun '(v2, asrt2) =>
                if expr_val_eqb v2 Vtrue then
                  Some ((Vtrue, asrt2) :: nil)
                else if expr_val_eqb v2 Vfalse then
                  Some ((Vfalse, asrt2) :: nil)
                else None
              )
            else if expr_val_eqb v1 Vfalse then
              Some ((Vfalse, asrt1) :: nil)
            else None
          )
        | CO_BOR =>
          do vl <- eval_ACexpr x1 asrt;
          Option_map_concat vl (fun '(v1, asrt1) =>
            if expr_val_eqb v1 Vtrue then
              Some ((Vtrue, asrt1) :: nil)
            else if expr_val_eqb v1 Vfalse then
              do vr <- eval_ACexpr x2 asrt1;
              Option_map_concat vr (fun '(v2, asrt2) =>
                if expr_val_eqb v2 Vtrue then
                  Some ((Vtrue, asrt2) :: nil)
                else if expr_val_eqb v2 Vfalse then
                  Some ((Vfalse, asrt2) :: nil)
                else None
              )
            else None
          )
        end
      | _ => None
      end
    | AC_cast _ x t =>
      match ty return option (list (expr_val ty * assertion)) with
      | 0 => eval_unop (Safe_cond t) (fun a => a) asrt x eval_ACexpr
      | _ => None
      end
    | AC_structfield _ x struct_id field_id t =>
      do l <- eval_ACexpr_l x asrt;
      Option_map l (fun '(v, asrt) =>
        do res <- eval_val (Sep_list asrt) (EField v struct_id field_id) ty;
        Some (res, asrt)
      )
    | AC_sizeof _ t1 t2 =>
      match ty return option (list (expr_val ty * assertion)) with
      | 0 =>
        let v := EConstZ (Ctype_size t1) in
        check eval_Prop_list (Prop_list asrt) (Safe_cond t2 v);
        Some ((v, asrt) :: nil)
      | _ => None
      end
    | AC_call asrt_info f args t =>
      match asrt_info with
      | AsrtInfo_FunCall _ _ pf_call call_wit =>
        do f_name_res <- eval_ACexpr f asrt;
        Option_map_concat f_name_res (fun '(f_name, asrt) =>
          match Z.eq_dec (get_expr_val_type f) 0 with left pf =>
          let f_name := expr_val_cast f_name pf in
          do args_res <- eval_ACexpr_list eval_ACexpr args asrt;
          let pre := (map (fun '(args, pre) => (f_name ,args, pre)) args_res) in
          if fun_pre_call_eqb pre call_wit.(pre_call) then
            Option_map_concat args_res (fun '(args_val, pre) =>
              Option_map call_wit.(post_call) (fun '(opt_v, post) =>
                do v <- opt_v;
                match Z.eq_dec call_wit.(ret_type) ty with left pf =>
                Some (expr_val_cast v pf, post)
                | _ => None end
              )
            )
          else None
          | _ => None end
        )
      | _ => None
      end
    | _ => None (* C_index & C_union *)
    end
  )
(* eval_ACexpr :
    forall x : ACexpr, assertion -> option (list (expr_val (get_expr_val_type x) * assertion))  *)
with eval_ACexpr_l (x : ACexpr) (asrt : assertion) : option (list (expr_val 0 * assertion)) :=
  match x with
  | AC_var _ id t =>
    do val <- eval_Ctmpval asrt id;
    Some ((val, asrt) :: nil)
  | AC_deref _ x' t =>
    match (get_expr_val_type x') as ty' return
        option (list (expr_val ty' * assertion)) -> option (list (expr_val 0 * assertion)) with
    | 0 => fun l => l
    | _ => fun _ => None
    end (eval_ACexpr x' asrt)
  | AC_structfield _ x' struct_id field_id t =>
      do l <- (eval_ACexpr_l x' asrt);
      Option_map l (fun '(v, asrt) =>
        do res <- eval_val (Sep_list asrt) (EField v struct_id field_id) 0;
        Some (res, asrt)
      )
  | _ => None
  end.

Definition eval_ACexpr_Assertion (x : ACexpr) (Asrt: Assertion)
    : option (list (expr_val (get_expr_val_type x) * assertion)) :=
  Option_map_concat Asrt (fun asrt : assertion =>
    eval_ACexpr x asrt
  ).

(* Section Safe_eval.

Variable Safety_checker : assertion -> list Proposition -> option bool.

Definition Safe_eval (x : ACexpr) (asrt : assertion) : option (list (expr_val * assertion)) :=
  match eval_ACexpr x asrt with
    | None => None
    | Some res => Option_move (map (fun a => match Safety_checker (snd a) (snd (fst a)) with
                                              | Some true => Some (fst (fst a) , snd a)
                                              | _ => None
                                             end ) res)
  end.

Definition Safe_eval_l (x : ACexpr) (asrt : assertion) : option (list (expr_val * assertion)) :=
  match eval_ACexpr_l x asrt with
    | None => None
    | Some res => Option_move (map (fun a => match Safety_checker (snd a) (snd (fst a)) with
                                              | Some true => Some (fst (fst a) , snd a)
                                              | _ => None
                                             end ) res)
  end.

End Safe_eval. *)