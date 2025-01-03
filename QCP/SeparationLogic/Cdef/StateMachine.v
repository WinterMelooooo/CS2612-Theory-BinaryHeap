From SimpleC.ASRT Require Import DefFiles.
From SimpleC.Common Require Import Notations.
From SimpleC.CSE Require Import Cexpr_def Cstate_def Cexpr_SymExec.
From compcert.lib Require Import Coqlib.

Local Open Scope option_monad_scope.

Section SM_exec_version.

(* Variable Safety_checker : assertion -> list Proposition -> option bool.
Variable entailment_checker : Assertion -> Assertion -> option bool.
Variable entailment_checker_with_ret : list Prod_ret -> list Prod_ret -> option bool. *)

Definition Pop_stack_list (env : Env) : option (Env * State) :=
  match Machine_stack env with
  | nil => None
  | (st, state) :: l' =>
    Some (mk_env (Funcspecs env) (Funcpreds env) (Seppreds env) l', state)
  end.

Definition Change_Machine_stack (env : Env) (l : list (StateType * State)) : Env :=
  mk_env (Funcspecs env) (Funcpreds env) (Seppreds env) l.

Definition Insert_stack (env : Env) (st : StateType) (state : State) : Env :=
  Change_Machine_stack env ((st, state) :: (Machine_stack env)).

Definition Insert_func (env : Env) (func : funcspec) : Env :=
  mk_env (func :: Funcspecs env) (Funcpreds env) (Seppreds env) (Machine_stack env).

Definition Insert_seppred (env : Env) (def : SepDef_input) : Env :=
  mk_env (Funcspecs env) (Funcpreds env) (def :: Seppreds env) (Machine_stack env).


Definition check_inv_pf (Pre: Assertion) (inv: Assertion) (pf: AsrtProof) : bool :=
  fold_left (fun b pre => b && (
    match pf.(entail_pf) pre inv with
    | Some _ => (* TODO: check proof validity *) true
    | _ => false
    end
  )) Pre true.

(* Definition SimpleCommand_exec_list := SimpleCommand_exec_list Safety_checker.
Definition Return_exec_list := Return_exec_list Safety_checker.
Definition If_Condition_exec_list := If_Condition_exec_list Safety_checker.
Definition Switch_Condition_exec_list := Switch_Condition_exec_list Safety_checker.
Definition Switch_Default_exec_list := Switch_Default_exec_list Safety_checker. *)

Definition In_loop_or_switch (st : StateType) : option bool :=
  match st with
  | In_while_block _ _ _ |
    (* In_do_block _ _ | *)
    In_for_block _ _ _ _ |
    In_switch_cases_block _ | In_switch_default_block => Some true
  | In_Global => Some false
  | _ => None
  end.

Definition In_loop (st : StateType) : option bool :=
  match st with
  | In_while_block _ _ _ |
    (* In_do_block _ _ | *)
    In_for_block _ _ _ _ => Some true
  | In_Global => Some false
  | _ => None
  end.

Fixpoint Break_vaild (stack : list (StateType * State)) : bool :=
  match stack with
  | nil => false
  | (st, state) :: l' =>
    match In_loop_or_switch st with
    | Some true => true
    | Some false => false
    | _ => Break_vaild l'
    end
  end.

Fixpoint Continue_vaild (stack : list (StateType * State)) : bool :=
  match stack with
  | nil => false
  | (st, state) :: l' =>
    match In_loop st with
    | Some true => true
    | Some false => false
    | _ => Continue_vaild l'
    end
  end.

(** In this function, we will generate the loop body *)
Fixpoint loop_body (ps_list : list partial_statement) : list partial_statement :=
  match ps_list with
  | nil => nil
  | a :: l' =>
    match a with
    | PS_while _ _ _ => l'
    | PS_for _ _ _ _ _ => l'
    (* | PS_do _ _ _ => l' *)
    | _ => a :: loop_body l'
    end
  end.

Definition Change_Normal_ret (s : State) (n : Assertion) : State :=
  mk_State n (Break_ret s) (Continue_ret s) (Return_ret s).

(** Here we require that for / while / do / switch / cases / default / if / else need { }
    Here we do not support single block { } without condition & loop keywords
    Here we assume at least 1 case occurs in switch & default occurs after case (if default occurs)
*)
Definition Transition (state_t : StateType) (state : State) (env : Env) (ps : partial_statement):
    option (StateType * State * Env) :=
  match ps with
  | PS_simple scmd =>
    match state_t with
    | In_Global => None
    | _ =>
      do res <- SimpleCommand_exec_list (Normal_ret state) scmd;
      Some (state_t, Change_Normal_ret state res, env)
    end
  | PS_break =>
    check (Break_vaild (Machine_stack env));
    Some (state_t , mk_State nil (Normal_ret state ++ Break_ret state) (Continue_ret state) (Return_ret state) , env)
  | PS_continue =>
    check (Continue_vaild (Machine_stack env));
    Some (state_t , mk_State nil (Break_ret state) (Normal_ret state ++ Continue_ret state) (Return_ret state) , env)
  | PS_return x =>
    match state_t with
    | In_Global => None
    | _ =>
      do res <- Return_exec_list (Normal_ret state) x;
      Some (state_t , mk_State nil (Break_ret state) (Continue_ret state) (res ++ Return_ret state) , env)
    end
  | PS_if cond =>
    match state_t with
    | In_Global => None
    | _ =>
      match If_Condition_exec_list (Normal_ret state) cond with
      | Some (then_Asrt , else_Asrt) =>
        Some (In_if_then_block else_Asrt ,
              Change_Normal_ret state then_Asrt,
              Insert_stack env (In_if_then_block else_Asrt) state)
      | _ => None
      end
    end
  | PS_else =>
    match state_t with
    | In_if_then_block else_pre =>
      do nenv , state' <- Pop_stack_list env;
      Some (In_if_else_block (Normal_ret state),
            Change_Normal_ret state else_pre,
            Insert_stack nenv (In_if_else_block (Normal_ret state)) state)
    | _ => None
    end
  | PS_block_end =>
    match state_t with
    | In_if_then_block else_pre =>
      match (Machine_stack env) with
      | (_, _) :: (st', state') :: l' =>
        Some (st',
          Change_Normal_ret state (else_pre ++ Normal_ret state),
          Change_Machine_stack env ((st', state') :: l'))
      | _ => None
      end
    | In_if_else_block then_post =>
      match (Machine_stack env) with
      | (_, _) :: (st', state') :: l' =>
        Some (st',
          Change_Normal_ret state (Normal_ret state ++ then_post),
          mk_env (Funcspecs env) (Funcpreds env) (Seppreds env) ((st', state') :: l'))
      | _ => None
      end
    | In_switch_cases_block label =>
      match (Machine_stack env) with
      | (_, _) :: (In_switch_block cond asrt label_list, state') :: l' =>
        let new_state_t := In_switch_block cond asrt (label :: label_list) in
        Some (new_state_t,
              state,
              Change_Machine_stack env ((new_state_t, state') :: l'))
      | _ => None
      end
    | In_switch_block _ _ _ =>
      match (Machine_stack env) with
      | (In_switch_block _ _ _, enter_state) :: (st', state') :: l' =>
        Some (st',
              mk_State (Normal_ret state ++ (Break_ret enter_state))
                       (Break_ret enter_state)
                       (Continue_ret state ++ Continue_ret enter_state)
                       (Return_ret state ++ Return_ret enter_state),
              Change_Machine_stack env ((st', state') :: l'))
      | _ => None
      end
    | In_while_block cond inv pf =>
      match (Machine_stack env) with
      | (In_while_block _ _ _, enter_state) :: (st', state') :: l' =>
        let finish := Normal_ret state ++ (Continue_ret state) in
        do _, false_branch <- If_Condition_exec_list finish cond;
        check check_inv_pf false_branch inv pf;
        Some (st',
              mk_State (false_branch ++ (Break_ret state))
                       (Break_ret enter_state)
                       (Continue_ret enter_state)
                       (Return_ret state ++ Return_ret enter_state),
              Change_Machine_stack env ((st', state') :: l'))
      | _ => None
      end
    | In_for_block cond Incr inv pf =>
      match (Machine_stack env) with
      | (In_for_block _ _ _ _, enter_state) :: (st', state') :: l' =>
        let finish := Normal_ret state ++ (Continue_ret state) in
        do Incr_res <- SimpleCommand_exec_list finish Incr;
        check check_inv_pf Incr_res inv pf;
        do _, false_branch <- If_Condition_exec_list Incr_res cond;
        Some (st',
              mk_State (Incr_res ++ (Break_ret state))
                       (Break_ret enter_state)
                       (Continue_ret enter_state)
                       (Return_ret state ++ Return_ret enter_state),
              Change_Machine_stack env ((st', state') :: l'))
      | _ => None
      end
    | In_func_block Posts pf =>
      match (Normal_ret state), (Break_ret state), (Continue_ret state) with
      | nil, nil, nil =>  (* Function ends; only Return_ret is allowed. *)
        check pf.(return_pf) (Return_ret state) Posts;
        do nenv, _ <- Pop_stack_list env;
        Some (In_Global , mk_State nil nil nil nil , nenv)
      | _, _, _ => None
      end
    (* TODO *)
    | _ => None
    end
  | PS_switch cond =>
    match state_t with
    | In_Global => None
    | _ =>
      let new_state_t := In_switch_block cond (Normal_ret state) nil in
      Some (new_state_t , mk_State nil nil nil nil ,
            Insert_stack env new_state_t state)
    end
  | PS_case label =>
    match state_t with
    | In_switch_block cond Asrt label_list =>
      do res, v <- Switch_Condition_exec_list Asrt cond label;
      if (Find Z.eqb label_list v) then None else (* label not in label_list *)
      let new_state_t := In_switch_cases_block v in
      let new_state := Change_Normal_ret state (res ++ Normal_ret state) in
      Some (new_state_t,
            new_state,
            Insert_stack env new_state_t new_state)
    | _ => None
    end
  | PS_default =>
    match state_t with
    | In_switch_block cond Asrt label_list =>
      do res <- Switch_Default_exec_list Asrt cond label_list;
      let new_state_t := In_switch_default_block in
      let new_state := Change_Normal_ret state (res ++ Normal_ret state) in
      Some (new_state_t,
            new_state,
            Insert_stack env new_state_t new_state)
    | _ => None
    end
  | PS_while cond inv pf =>
    match state_t with
    | In_Global => None
    | _ =>
      check check_inv_pf (Normal_ret state) inv pf;
      do true_branch, _ <- If_Condition_exec_list inv cond;
      let new_state_t := In_while_block cond inv pf in
      Some (new_state_t, mk_State true_branch nil nil nil,
            Insert_stack env new_state_t state)
    end
  (*| PS_do =>
      match state_t with
      | In_Global => None
      | Get_Inv inv =>
        match entailment_checker (Normal_ret state) inv with
        | Some true =>
          match Pop_stack_list env with
          | Some (nenv , _ , ps') => Some (In_do_block inv, mk_State inv nil nil nil, Insert_stack_ps nenv (In_do_block inv) state (ps' ++ (ps :: nil)))
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end *)
  | PS_for init cond Incr inv pf =>
    match state_t with
    | In_Global => None
    | _ =>
      do init_res <- SimpleCommand_exec_list (Normal_ret state) init;
      check check_inv_pf init_res inv pf;
      do true_branch, _ <- If_Condition_exec_list inv cond;
      let new_state_t := In_for_block cond Incr inv pf in
      Some (new_state_t, mk_State true_branch nil nil nil,
            Insert_stack env new_state_t state)
    end
  (* | PS_inv inv =>
    match state_t with
    | In_Global | Get_Inv _ => None
    | _ => Some (Get_Inv inv , state , Insert_stack_ps env (Get_Inv inv) state (ps :: nil))
    end *)
  | PS_assert Asrt pf =>
    match state_t with
    | In_Global => None
    | _ =>
      check check_inv_pf (Normal_ret state) Asrt pf;
      Some (state_t,
            Change_Normal_ret state Asrt,
            env)
    end
  | _ => None
  end.


(* Definition End_switch (state : State) (env : Env) (res : Assertion) : option (StateType * State * Env) :=
  match (Machine_stack env) with
    | (In_switch_default_block , _0) :: (st, state0) :: (st', state') :: l' =>
       Some (st', (mk_State (res ++ (Normal_ret state) ++ (Break_ret state)) (Break_ret state0) (Continue_ret state ++ Continue_ret state0) (Return_ret state ++ Return_ret state0)), mk_env (Funcspecs env) (Funcpreds env) (Seppreds env) ((st', state') :: l'))
    | _ => None
  end.

Definition End_loop (state : State) (env : Env) (cond : Cexpr) (inv : Assertion) (Incr : Csimplecommand) (ps0 : list partial_statement) : option (StateType * State * Env) :=
  match (Machine_stack env) with
  | nil => None
  | (st, state0) :: nil => None
  | (st, state0) :: (st', state') :: l' =>
    do Incr_res <- (SimpleCommand_exec_list (Normal_ret state ++ (Continue_ret state)) Incr);
    match entailment_checker Incr_res inv with
    | Some true =>
      match If_Condition_exec_list inv cond with
      | None => None
      | Some (fres , sres) =>
        Some (st', (mk_State (sres ++ (Break_ret state)) (Break_ret state0) (Continue_ret state0) (Return_ret state ++ Return_ret state0)), mk_env (Funcspecs env) (Funcpreds env) (Seppreds env) ((st', state' ++ ps_list ++ ps0) :: l'))
      end
    | _ => None
    end
  end.

Definition End_do_while (state : State) (env : Env) (cond : Cexpr) (inv : Assertion) (ps0 : list partial_statement) : option (StateType * State * Env) :=
  match (Machine_stack env) with
  | nil => None
  | (st, state0) :: nil => None
  | (st, state0) :: (st', state') :: l' =>
    match (If_Condition_exec_list (Normal_ret state ++ (Continue_ret state)) cond) with
    | None => None
    | Some (fres , sres) =>
      match entailment_checker fres inv with
      | Some true => Some (st', (mk_State (sres ++ (Break_ret state)) (Break_ret state0) (Continue_ret state0) (Return_ret state ++ Return_ret state0)), mk_env (Funcspecs env) (Funcpreds env) (Seppreds env) ((st', state' ++ ps_list ++ ps0) :: l'))
      | _ => None
      end
    end
  end. *)

Fixpoint Machine_Start (state_t : StateType) (state : State) (env : Env) (ps_list : list partial_statement) : option (StateType * State * Env) :=
  match ps_list with
  | nil => (* match (Machine_stack env) with
              | nil => Some (state_t , state , env)
              | _ => None
            end *)  Some (state_t , state , env)
  | ps :: ps' =>
    let res := Transition state_t state env ps in
    match res with
    | None => None
    | Some (nst, ns, nenv) => Machine_Start nst ns nenv ps'
    end
  end.

Definition Machine_exec (env : Env) (Pre : assertion) (Post : list Prod_ret) (pf : AsrtProof)
    (ps_list : list partial_statement) :=
  let state_t := In_func_block Post pf in
  let state := mk_State (Pre :: nil) nil nil nil in
  Machine_Start state_t state (Insert_stack env state_t state) ps_list.

End SM_exec_version.