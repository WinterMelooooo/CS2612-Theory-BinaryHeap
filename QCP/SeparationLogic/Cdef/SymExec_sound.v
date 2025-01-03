(* 2024.7.23 TODO: rewrite *)

From SimpleC.Common Require Import COps.
From SimpleC.ASRT Require Import DefFiles.
From SimpleC.CSE Require Import Cexpr_def Cstate_def Cexpr_val_helper Cstatement_semantics Cexpr_SymExec StateMachine Ceval_sound.
From compcert.lib Require Import Coqlib Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
From AUXLib Require Import relations.
Local Open Scope sets.

Definition State_valid (env : prog_env) (return_val : int64) (Pre : assertion) (Post : State) (sem : FinDnt) := 
  Single_sound env Pre (Normal_ret Post) (NormalExit sem) /\ 
  Single_sound env Pre (Break_ret Post) (BreakExit sem) /\ 
  Single_sound env Pre (Continue_ret Post) (ContExit sem) /\
  Single_ret_sound env return_val Pre (Return_ret Post) (ReturnExit sem).


(** These lemmas can be used directly*)

Lemma SimpleCommand_exec_sound :
  forall env callees return_val Safety_checker scomd Pre Post,
    Sound_safety_checker Safety_checker ->
    SimpleCommand_exec Safety_checker Pre scomd = Some Post ->
    State_valid env return_val Pre (mk_State Post nil nil nil) (Csimplecommand_denote env callees scomd).
Proof.
Admitted.

Lemma SimpleCommand_exec_list_sound :
  forall env callees return_val Safety_checker scomd Pre Post, 
    SimpleCommand_exec_list Safety_checker Pre scomd = Some Post -> 
      forall v , In v Pre -> 
        exists Post' , 
        SimpleCommand_exec Safety_checker v scomd = Some Post' /\ 
        (forall v , In v Post' -> In v Post) /\ State_valid env return_val v (mk_State Post' nil nil nil) (Csimplecommand_denote env callees scomd).
Proof.
Admitted.

Lemma Return_exec_list_sound :
  forall env callees return_val Safety_checker x Pre Post, 
    Return_exec_list Safety_checker Pre x = Some Post -> 
      forall v , In v Pre -> 
        exists Post' , 
        Return_exec Safety_checker v x = Some Post' /\ 
        (forall v , In v Post' -> In v Post) /\ State_valid env return_val v (mk_State nil nil nil Post') (Cret_denote env callees return_val x).
Proof.
Admitted.

Lemma If_Condition_exec_list_sound :
   forall env callees return_val Safety_checker x Pre T_Post F_Post, 
    If_Condition_exec_list Safety_checker Pre x = Some (T_Post , F_Post) -> 
      forall v , In v Pre -> 
        exists T_Post' F_Post', 
        Condition_exec Safety_checker v x Vtrue = Some (T_Post' , F_Post') /\
        (forall v , In v T_Post' -> In v T_Post) /\
        (forall v , In v F_Post' -> In v F_Post) /\ State_valid env return_val v (mk_State T_Post' nil nil nil) (mk_Fin (Truth_denote env callees x) ∅ ∅ ∅) /\ State_valid env return_val v (mk_State F_Post' nil nil nil) (mk_Fin (Falth_denote env callees x) ∅ ∅ ∅).
Proof.
Admitted.

Lemma Switch_Condition_exec_list_sound :
   forall env callees return_val Safety_checker x y Pre T_Post sres,
    Switch_Condition_exec_list Safety_checker Pre x y = Some (T_Post, sres) ->
    expr_simple y = Some sres /\
    (forall v , In v Pre ->
     State_valid env return_val v (mk_State T_Post nil nil nil)
        (mk_Fin (Truth_denote env callees (C_binop CO_EQ x y (type_of x))) ∅ ∅ ∅)).
Proof.
Admitted.

Lemma Switch_Default_exec_list_sound :
   forall env callees return_val Safety_checker x expr_labels Z_labels Pre Post,
   Switch_Default_exec_list Safety_checker Pre x Z_labels = Some Post ->
   Valid_cases_expr expr_labels = (rev Z_labels, true) ->
   (forall v , In v Pre ->
    State_valid env return_val v (mk_State Post nil nil nil)
      (mk_Fin
         (fold_right
            (fun y s => (Falth_denote env callees (C_binop CO_EQ x y (type_of x))) ∩ s)
            Rels.id expr_labels)
         ∅ ∅ ∅)).
Proof.
Admitted.

(** Here is the main theorem *)

Ltac inv H := inversion H; subst; clear H.

Definition not_Get_Inv (state_t : StateType) : Prop :=
  match state_t with
  | Get_Inv _ => False
  | _ => True
  end.

Ltac destruct_options :=
  repeat
  match goal with
  | H : context [ match ?x with | Some _ => _ | None => None end ] |- _ =>
    destruct x eqn:?; [| discriminate]
  | H : match ?state_t with
        | In_Global | Get_Inv _ => None
        | In_func_block _ => ?A
        | In_while_block _ _ => _
        | In_do_block _ => _
        | In_for_block _ _ _ => _
        | In_switch_block _ => _
        | In_switch_cases_block _ _ _ => _
        | In_switch_default_block => _
        | In_if_then_block _ => _
        | In_if_else_block _ => _
        end = Some ?B |- _ =>
    assert (state_t <> In_Global /\ not_Get_Inv state_t) by (destruct state_t; split; simpl; try congruence; auto);
    assert (A = Some B) by (destruct state_t; congruence); clear H
  | H : match ?state_t with
        | In_Global => None
        | Get_Inv _ => ?A
        | In_func_block _ => _
        | In_while_block _ _ => _
        | In_do_block _ => _
        | In_for_block _ _ _ => _
        | In_switch_block _ => _
        | In_switch_cases_block _ _ _ => _
        | In_switch_default_block => _
        | In_if_then_block _ => _
        | In_if_else_block _ => _
        end = Some ?B |- _ =>
    assert (state_t <> In_Global) by (destruct state_t; congruence);
    assert (A = Some B) by (destruct state_t; congruence); clear H
  | H : match ?state_t with
        | In_if_then_block Fault => ?A
        | In_Global => None
        | Get_Inv _ => None
        | In_func_block _ => None
        | In_while_block _ _ => None
        | In_do_block _ => None
        | In_for_block _ _ _ => None
        | In_switch_block _ => None
        | In_switch_cases_block _ _ _ => None
        | In_switch_default_block => None
        | In_if_else_block _ => None
        end = Some ?B |- _ =>
        destruct state_t; try congruence
  | H : Some _ = Some _ |- _ => inv H
  | H : context [ let (_, _) := ?P in _ ] |- _ => destruct P
  | H : (if ?b then _ else None) = Some _ |- _ => destruct b eqn:?; [ | discriminate]
  end.

(* 
Definition Cstatement_ind2 (P : Cstatement -> Prop)
  (Hsimple : forall c : Csimplecommand, P (C_simple c))
  (Hseq : forall c : Cstatement, P c ->
     forall c0 : Cstatement, P c0 -> P (C_seq c c0))
  (Hif : forall (c : Cexpr) (c0 : Cstatement),
     P c0 -> forall c1 : Cstatement, P c1 -> P (C_if c c0 c1))
  (Hwhile : forall (c : Cexpr) (c0 : Cstatement),
     P c0 -> P (C_while c c0))
  (Hdowhile : forall (c : Cexpr) (c0 : Cstatement),
    P c0 -> P (C_dowhile c c0))
  (Hfor : forall (c : Csimplecommand) (c0 : Cexpr)
    (c1 : Csimplecommand) (c2 : Cstatement),
    P c2 -> P (C_for c c0 c1 c2))
  (Hbreak : P C_break)
  (Hcontinue : P C_continue)
  (Hswitch : forall (c : Cexpr) (l : list (Cexpr * Cstatement)),
    Forall (fun p => P (snd p)) l ->
    forall c0 : Cstatement, P c0 -> P (C_switch c l c0))
  (Hreturn : forall o : option Cexpr, P (C_return o))
  (Hassert : forall l : AssertionC_assert l))
  (Hinv : forall l : Assertion, P (C_inv l)) :
  forall c : Cstatement, P c :=
  fix f c :=
    match c with
    | C_simple c => Hsimple c
    | C_seq c c0 => Hseq c (f c) c0 (f c0)
    | C_if c c0 c1 => Hif c c0 (f c0) c1 (f c1)
    | C_while c c0 => Hwhile c c0 (f c0)
    | C_dowhile c c0 => Hdowhile c c0 (f c0)
    | C_for c c0 c1 c2 => Hfor c c0 c1 c2 (f c2)
    | C_break => Hbreak
    | C_continue => Hcontinue
    | C_switch c l c0 =>
      Hswitch c l
        ((fix f' (l : list (Cexpr * Cstatement)) :=
          match l return Forall (fun p => P (snd p)) l with
          | nil => Forall_nil (fun p => P (snd p))
          | p :: l' => @Forall_cons (Cexpr * Cstatement) (fun p => P (snd p)) p l' (f (snd p)) (f' l')
          end) l) c0 (f c0)
    | C_return o => Hreturn o
    | C_assert l => Hassert l
    | C_inv l => Hinv l
    end.
*)

Lemma Some_concat_Some_app :
  forall (A : Type) (ox : option (list A)) ol l',
  Some_concat (ox :: ol) = Some l' ->
  exists x l,
  ox = Some x /\ Some_concat ol = Some l /\ l' = x ++ l.
Proof.
  unfold Some_concat. intros.
  destruct ox; [ | discriminate].
  generalize dependent l'.
  induction ol; intros; simpl in *.
  - inv H. eauto.
  - destruct a; [ | discriminate].
    destruct (Find_None ol); [discriminate | ].
    inv H.
    specialize (IHol _ eq_refl).
    destruct IHol as [x [l1 [? [? ?] ] ] ].
    inv H. inv H0. simpl.
    eauto.
Qed.


Definition State_update_Normal st n :=
  {|
    Normal_ret := n;
    Break_ret := st.(Break_ret);
    Continue_ret := st.(Continue_ret);
    Return_ret := st.(Return_ret);
  |}.

Section Safety_And_Entailment_Checkers.

Variable Safety_checker : assertion -> list Proposition -> option bool.
Variable entailment_checker : Assertion -> Assertion -> option bool.
Variable entailment_checker_with_ret : list Prod_ret -> list Prod_ret -> option bool.

Variable HSafety_checker : Sound_safety_checker Safety_checker.
Variable Hentailment_checker : Sound_entailment_checker entailment_checker.
Variable Hentailment_checker_with_ret : Sound_entailment_checker_with_ret entailment_checker_with_ret.

Definition SimpleCommand_exec_list' := SimpleCommand_exec_list Safety_checker.

Definition If_Condition_exec_list' := If_Condition_exec_list Safety_checker.

Definition Return_exec_list' := Return_exec_list Safety_checker.

Definition Switch_Condition_exec_list' := Switch_Condition_exec_list Safety_checker.

Definition Switch_Default_exec_list' := Switch_Default_exec_list Safety_checker.

Definition Machine_Start' := Machine_Start Safety_checker entailment_checker entailment_checker_with_ret.

Definition entail (Pre Post : Assertion) : Prop :=
  forall v , In v Pre ->
  forall env J st, Assertion_denote env J st v ->
  exists m , In m Post /\ Assertion_denote env J st m.

Lemma entail_refl : forall Pre, entail Pre Pre.
Proof.
  unfold entail.
  intros. eauto.
Qed.

Lemma entail_trans : forall Pre Mid Post,
  entail Pre Mid -> entail Mid Post -> entail Pre Post.
Proof.
  unfold entail.
  intros.
  specialize (H v H1 env J st H2).
  destruct H as [m [? ?] ].
  specialize (H0 m H env J st H3).
  apply H0.
Qed.

Lemma entailment_checker_entail : forall Pre Post,
  entailment_checker Pre Post = Some true ->
  entail Pre Post.
Proof.
  intros. apply Hentailment_checker in H. exact H.
Qed.

Hint Immediate entailment_checker_entail : core.

Definition state_stack_match (stack : list (StateType * State * list partial_statement))
  state_t state_t_k state_k ps_list stack' :=
  (not_Get_Inv state_t /\ state_t = state_t_k /\
   stack = (state_t_k, state_k, ps_list) :: stack') \/
  (exists inv state_k' ps_list1 ps_list2, ps_list = ps_list1 ++ PS_inv inv :: ps_list2 /\
   state_t = Get_Inv inv /\ not_Get_Inv state_t_k /\
   stack = (Get_Inv inv, state_k', PS_inv inv :: ps_list2) ::
           (state_t_k, state_k, ps_list1) :: stack').

Definition state_stack_match_cases (stack : list (StateType * State * list partial_statement))
  state_t state_t_k' state_k' ps_list stack' :=
  exists state_t_k state_k ps_list1 ps_list2,
  stack = (state_t_k, state_k, ps_list2) :: (state_t_k', state_k', ps_list1) :: stack' /\
  ps_list = ps_list1 ++ ps_list2 /\
  match state_t, state_t_k with
  | In_switch_cases_block cond asrt Faults, In_switch_cases_block cond' asrt' Faults' =>
    cond = cond' /\ asrt = asrt'
  | _, _ => False
  end.

Section Exec_Res_Case.

Variable exec_res : State -> Cstatement -> State -> Prop.

Inductive exec_res_case (cond : Cexpr) (asrt : Assertion) :
  State -> list Z -> list (Cexpr * Cstatement) -> State -> list Z -> Prop :=
| SER_nil : forall state labels,
  exec_res_case cond asrt state labels nil state labels
| SER_cons : forall label c cases pre post fres sres pre_c post_c labels1 labels2,
  Switch_Condition_exec_list' asrt cond label = Some (fres, sres) ->
  Find Z.eqb labels1 sres = false ->
  pre_c = State_update_Normal pre (fres ++ pre.(Normal_ret)) ->
  exec_res pre_c c post_c ->
  exec_res_case cond asrt post_c (sres :: labels1) cases post labels2 ->
  exec_res_case cond asrt pre labels1 ((label, c) :: cases) post labels2.

End Exec_Res_Case.


Inductive exec_res : State -> Cstatement -> State -> Prop :=
| ER_simple : forall scmd pre post post_n,
  SimpleCommand_exec_list' pre.(Normal_ret) scmd = Some post_n ->
  post = State_update_Normal pre post_n ->
  exec_res pre (C_simple scmd) post
| ER_seq : forall c1 c2 pre mid post,
  exec_res pre c1 mid ->
  exec_res mid c2 post ->
  exec_res pre (C_seq c1 c2) post
| ER_if : forall e c1 c2 pre post fres sres post1 post2,
  If_Condition_exec_list' pre.(Normal_ret) e = Some (fres, sres) ->
  exec_res (mk_State fres nil nil nil) c1 post1 ->
  exec_res (mk_State sres nil nil nil) c2 post2 ->
  post = mk_State (post1.(Normal_ret) ++ post2.(Normal_ret))
                  (post2.(Break_ret) ++ post1.(Break_ret) ++ pre.(Break_ret))
                  (post2.(Continue_ret) ++ post1.(Continue_ret) ++ pre.(Continue_ret))
                  (post2.(Return_ret) ++ post1.(Return_ret) ++ pre.(Return_ret)) ->
  exec_res pre (C_if e c1 c2) post
| ER_while : forall e c pre post inv fres sres post1 incr_res,
  entail pre.(Normal_ret) inv ->
  If_Condition_exec_list' inv e = Some (fres, sres) ->
  exec_res (mk_State fres nil nil nil) c post1 ->
  SimpleCommand_exec_list' (post1.(Normal_ret) ++ post1.(Continue_ret)) C_skip = Some incr_res ->
  entail incr_res inv ->
  post = mk_State (sres ++ post1.(Break_ret)) pre.(Break_ret)
                  pre.(Continue_ret) (post1.(Return_ret) ++ pre.(Return_ret)) ->
  exec_res pre (C_while e c) post
| ER_dowhile : forall e c pre post inv post1 fres sres,
  entail pre.(Normal_ret) inv ->
  exec_res (mk_State inv nil nil nil) c post1 ->
  If_Condition_exec_list' (post1.(Normal_ret) ++ post1.(Continue_ret)) e = Some (fres, sres) ->
  entail fres inv ->
  post = mk_State (sres ++ post1.(Break_ret)) pre.(Break_ret)
                  pre.(Continue_ret) (post1.(Return_ret) ++ pre.(Return_ret)) ->
  exec_res pre (C_dowhile e c) post
| ER_for : forall init cond incr body pre post inv init_res fres sres post1 incr_res,
  SimpleCommand_exec_list' pre.(Normal_ret) init = Some init_res ->
  entail init_res inv ->
  If_Condition_exec_list' inv cond = Some (fres, sres) ->
  exec_res (mk_State fres nil nil nil) body post1 ->
  SimpleCommand_exec_list' (post1.(Normal_ret) ++ post1.(Continue_ret)) incr = Some incr_res ->
  entail incr_res inv ->
  post = mk_State (sres ++ post1.(Break_ret)) pre.(Break_ret)
                  pre.(Continue_ret) (post1.(Return_ret) ++ pre.(Return_ret)) ->
  exec_res pre (C_for init cond incr body) post
| ER_break : forall pre post,
  post = mk_State nil (pre.(Normal_ret) ++ pre.(Break_ret)) pre.(Continue_ret) pre.(Return_ret) ->
  exec_res pre C_break post
| ER_continue : forall pre post,
  post = mk_State nil pre.(Break_ret) (pre.(Normal_ret) ++ pre.(Continue_ret)) pre.(Return_ret) ->
  exec_res pre C_continue post
| ER_switch : forall cond cases default Pre Post labels Post1 Post2 res,
  exec_res_case exec_res cond Pre.(Normal_ret)
    (mk_State nil nil nil nil) nil cases Post1 labels ->
  Switch_Default_exec_list' Pre.(Normal_ret) cond labels = Some res ->
  exec_res (State_update_Normal Post1 (res ++ Post1.(Normal_ret))) default Post2 ->
  Post = mk_State (Post2.(Normal_ret) ++ Post2.(Break_ret))
                  Pre.(Break_ret)
                  (Post2.(Continue_ret) ++ Pre.(Continue_ret))
                  (Post2.(Return_ret) ++ Pre.(Return_ret)) ->
  exec_res Pre (C_switch cond cases default) Post
| ER_return : forall e pre post res,
  Return_exec_list' pre.(Normal_ret) e = Some res ->
  post = mk_State nil pre.(Break_ret) pre.(Continue_ret) (res ++ pre.(Return_ret)) ->
  exec_res pre (C_return e) post.
(*| ER_assert : forall pre post asrt,
  entail pre.(Normal_ret) asrt ->
  post = State_update_Normal pre asrt ->
  exec_res pre (C_assert asrt) post 
| ER_inv : forall pre post inv,
  pre = post ->
  exec_res pre (C_inv inv) post. *)

Hint Constructors exec_res_case : core.
Hint Constructors exec_res : core.


Lemma Machine_Start_app_iff :
  forall Safety_checker entailment_checker entailment_checker_with_ret
    ps_list1 ps_list2 state_t0 state0 env0 state_t2 state2 env2,
  (exists state_t1 state1 env1,
    Machine_Start Safety_checker entailment_checker entailment_checker_with_ret
     state_t0 state0 env0 ps_list1 = Some (state_t1, state1, env1) /\
   Machine_Start Safety_checker entailment_checker entailment_checker_with_ret
     state_t1 state1 env1 ps_list2 = Some (state_t2, state2, env2)) <->
   Machine_Start Safety_checker entailment_checker entailment_checker_with_ret
    state_t0 state0 env0 (ps_list1 ++ ps_list2) = Some (state_t2, state2, env2).
Proof.
  induction ps_list1; intros; simpl in *.
  - split; intros.
    + destruct H as [state_t1 [state1 [env1 [? ?] ] ] ].
      destruct_options. auto.
    + eauto.
  - split; intros.
    + destruct H as [state_t1 [state1 [env1 [? ?] ] ] ].
      destruct_options.
      apply IHps_list1.
      eauto.
    + destruct_options.
      apply IHps_list1. auto.
Qed.


Lemma StateMachine_Start_result_cases :
  forall cases ps_list,
  Some_concat
    (map
        (fun b : Cexpr * Cstatement =>
        match Stmt_to_ps (snd b) with
        | Some s1 => Some (PS_other_case (fst b) :: s1)
        | None => None
        end) cases) = Some ps_list ->
  Forall
    (fun p : Cexpr * Cstatement =>
      forall ps_list : list partial_statement,
      Stmt_to_ps (snd p) = Some ps_list ->
      forall (state_t_s : StateType)
        (state_s : State) (env_s : Env)
        (state_t_k : StateType) (state_k : State)
        (ps_list_k : list partial_statement)
        (stack : list
                  (StateType * State *
                    list partial_statement))
        (state_t_e : StateType) (state_e : State)
        (env_e : Env),
      Machine_Start' state_t_s state_s env_s ps_list =
        Some (state_t_e, state_e, env_e) ->
      state_stack_match env_s.(Machine_stack) state_t_s state_t_k state_k ps_list_k stack ->
      state_stack_match env_e.(Machine_stack) state_t_e state_t_k state_k (ps_list_k ++ ps_list) stack /\
          exec_res state_s (snd p) state_e) cases ->
  forall state_t_s state_s env_s
         state_t_k' state_k' ps_list_k stack
         state_t_e state_e env_e,
  Machine_Start' state_t_s state_s env_s ps_list =
    Some (state_t_e, state_e, env_e) ->
  state_stack_match_cases env_s.(Machine_stack) state_t_s state_t_k' state_k' ps_list_k stack ->
  not_Get_Inv state_t_e ->
  exists cond asrt labels0 labels,
  state_t_s = In_switch_cases_block cond asrt labels0 /\
  exec_res_case exec_res cond asrt state_s labels0 cases state_e labels /\
  state_t_e = In_switch_cases_block cond asrt labels /\
  state_stack_match_cases env_e.(Machine_stack) state_t_e state_t_k' state_k' (ps_list_k ++ ps_list) stack.
Proof.
  unfold state_stack_match_cases.
  induction cases; intros * HPS HEX0 * HEX HSM HST_e; simpl in *.
  - unfold Some_concat, Find_None in HPS. simpl in HPS. inv HPS.
    simpl in HEX. inv HEX.
    destruct HSM as [state_t_k [state_k [ps_list1 [ps_list2 [HENV_e [-> ?] ] ] ] ] ].
    destruct state_t_e; try contradiction.
    destruct state_t_k; try contradiction.
    destruct H as [-> ->].
    rewrite app_nil_r. do 4 eexists.
    repeat split; eauto.
    do 3 eexists. repeat split; eauto.
  - destruct a. simpl in *. destruct_options.
    apply Some_concat_Some_app in HPS.
    destruct HPS as [l1 [l' [? [? ->] ] ] ].
    inv HEX0. inv H. specialize (IHcases _ H0 H4).
    simpl in HEX.
    destruct HSM as [state_t_k [state_k [ps_list1 [ps_list2 [HENV_s [-> ?] ] ] ] ] ].
    destruct state_t_s, state_t_k; try contradiction.
    destruct H as [-> ->]. destruct_options.
    unfold Pop_stack_list in Heqo2. rewrite HENV_s in Heqo2. inv Heqo2.
    destruct (Find Z.eqb l0 z) eqn:HFind; [discriminate | ]. destruct_options.
    unfold Push_stack_list in Heqo2. simpl in Heqo2. inv Heqo2.
    apply Machine_Start_app_iff in HEX.
    destruct HEX as [state_t_m [state_m [env_m [HEXl HEXl'] ] ] ].
    edestruct (H3 _ Heqo) as [HSM_m HER_m]; eauto.
    { unfold state_stack_match. left. simpl. repeat split; eauto. }
    destruct HSM_m as [
      [HNINV_m [-> HENV_m] ] |
      [inv [state_k'' [ps_list3 [ps_list4 [? [-> [HNINV_k HENV_m] ] ] ] ] ] ] ].
    2:{ exfalso. destruct cases; simpl in *.
        - unfold Some_concat, Find_None in H0. simpl in H0. inv H0.
          simpl in HEXl'. inv HEXl'. contradiction.
        - apply Some_concat_Some_app in H0.
          destruct H0 as [? [? [? [? ->] ] ] ].
          destruct p. destruct_options.
          simpl in HEXl'. congruence. }
    edestruct IHcases as [cond [asrt [labels0 [labels [? [? [? ?] ] ] ] ] ] ].
    { apply HEXl'. }
    { do 4 eexists. repeat split; eauto. simpl. auto. }
    { auto. }
    subst. inv H. simpl in *.
    destruct H5 as [state_t_k [state_k [ps_list3 [ps_list4 [HENV_e [? ?] ] ] ] ] ].
    do 4 eexists. repeat split; eauto.
    + rewrite HENV_e. exists state_t_k, state_k, ps_list3, ps_list4.
      repeat split; auto.
      rewrite <- app_assoc. rewrite <- ! app_assoc in H.
      simpl in H. apply H.
Qed.

Theorem StateMachine_Start_result :
  forall comd ps_list,
  Stmt_to_ps comd = Some ps_list ->
  forall state_t_s state_s env_s
         state_t_k state_k ps_list_k stack
         state_t_e state_e env_e,
  Machine_Start' state_t_s state_s env_s ps_list =
    Some (state_t_e, state_e, env_e) ->
  state_stack_match env_s.(Machine_stack) state_t_s state_t_k state_k ps_list_k stack ->
  state_stack_match env_e.(Machine_stack) state_t_e state_t_k state_k (ps_list_k ++ ps_list) stack /\
  exec_res state_s comd state_e.
Proof.
Admitted.
(* 
  unfold state_stack_match.
  induction comd using Cstatement_ind2; simpl; intros * HPS * HEX HSM_s.
  - (* C_simple *)
    inv HPS. simpl in HEX. destruct_options.
    unfold Push_stack in Heqo0.
    destruct HSM_s as [
      [HNINV_s [<- HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    2:{ rewrite HENV_s in *. subst. destruct H. contradiction. }
    rewrite HENV_s in *. subst. inv Heqo0.
    simpl. repeat split; eauto.
  - (* C_seq *)
    destruct_options.
    specialize (IHcomd1 _ eq_refl). specialize (IHcomd2 _ eq_refl).
    apply Machine_Start_app_iff in HEX.
    destruct HEX as [state_t_m [state_m [env_m [HEXl HEXl0] ] ] ].
    specialize (IHcomd1 _ _ _ _ _ _ _ _ _ _ HEXl HSM_s).
    destruct IHcomd1 as [HSM_m HER_m].
    specialize (IHcomd2 _ _ _ _ _ _ _ _ _ _ HEXl0 HSM_m).
    destruct IHcomd2 as [HSM_e HER_e].
    rewrite <- ! app_assoc in HSM_e.
    repeat split; eauto.
  - (* C_if *)
    destruct_options.
    destruct HSM_s as [
      [HNINV_s [<- HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    2:{ simpl in HEX. congruence. }
    specialize (IHcomd1 _ eq_refl). specialize (IHcomd2 _ eq_refl).
    simpl in HEX. destruct_options.
    apply Machine_Start_app_iff in HEX.
    destruct HEX as [state_t1 [state1 [env1 [HEXl HEXl'] ] ] ].
    unfold Insert_stack_ps in HEXl.
    edestruct IHcomd1 as [HSM1 HER1].
    { eauto. }
    { left. simpl. repeat split; eauto. }
    destruct HSM1 as [
      [HNINV1 [-> HENV1] ] |
      [inv [state_k' [ps_list1 [ps_list2 [? [-> [HNINV_k HENV1] ] ] ] ] ] ] ].
    2:{ simpl in HEXl'. congruence. }
    simpl in HEXl'. unfold Pop_stack_list in HEXl'. rewrite HENV1 in HEXl'.
    apply Machine_Start_app_iff in HEXl'.
    destruct HEXl' as [state_t2 [state2 [env2 [HEXl0 HEXl0'] ] ] ].
    unfold Insert_stack_ps in HEXl0.
    edestruct IHcomd2 as [HSM2 HER2].
    { eauto. }
    { left. simpl. repeat split; eauto. }
    destruct HSM2 as [
      [HNINV2 [-> HENV2] ] |
      [inv [state_k' [ps_list1 [ps_list2 [? [-> [HNINV_k HENV2] ] ] ] ] ] ] ].
    2:{ simpl in HEXl0'. congruence. }
    simpl in HEXl0'. unfold End_if in HEXl0'.
    rewrite HENV2 in HEXl0'. rewrite HENV_s in HEXl0'.
    simpl in HEXl0'. inv HEXl0'.
    simpl. repeat split; eauto.
    left. rewrite <- ! app_assoc. simpl. repeat split; eauto.
  - (* C_while *)
    destruct_options.
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    { simpl in HEX. destruct state_t_k; try congruence; contradiction. }
    simpl in HEX. destruct_options.
    unfold Insert_stack_ps in HEX.
    apply Machine_Start_app_iff in HEX.
    destruct HEX as [state_t1 [state1 [env1 [HEXl HEXl'] ] ] ].
    edestruct (IHcomd _ eq_refl) as [HSM1 HER1].
    { eauto. }
    { left. simpl. repeat split; eauto. }
    destruct HSM1 as [
      [HNINV1 [-> HENV1] ] |
      [inv' [state_k'' [ps_list3 [ps_list4 [? [-> [HNINV_k' HENV1] ] ] ] ] ] ] ].
    2:{ simpl in HEXl'. congruence. }
    unfold Pop_stack_list in Heqo3.
    rewrite HENV_s in Heqo3. inv Heqo3.
    simpl in HENV1. simpl in HEXl'.
    unfold End_loop in HEXl'. rewrite HENV1 in HEXl'.
    simpl in HEXl'. rewrite Heqo2 in HEXl'.
    destruct_options. simpl in *.
    repeat split; eauto.
    * left. rewrite <- ! app_assoc. simpl.
      repeat split; eauto.
  - (* C_dowhile *)
    destruct_options.
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    { simpl in HEX. destruct state_t_k; try congruence; contradiction. }
    simpl in HEX. destruct_options.
    unfold Pop_stack_list in Heqo2.
    rewrite HENV_s in Heqo2. inv Heqo2.
    apply Machine_Start_app_iff in HEX.
    destruct HEX as [state_t1 [state1 [env1 [HEXl HEXl'] ] ] ].
    edestruct (IHcomd _ eq_refl) as [HSM1 HER1].
    { eauto. }
    { left. simpl. repeat split; eauto. }
    destruct HSM1 as [
      [HNINV1 [-> HENV1] ] |
      [inv' [state_k'' [ps_list3 [ps_list4 [? [-> [HNINV_k' HENV1] ] ] ] ] ] ] ].
    2:{ simpl in HEXl'. congruence. }
    simpl in HEXl'. unfold End_do_while in HEXl'.
    rewrite HENV1 in HEXl'. destruct_options.
    repeat split; eauto.
    * left. rewrite <- ! app_assoc. simpl.
      repeat split; eauto.
  - (* C_for *)
    destruct_options.
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    { simpl in HEX. destruct state_t_k; try congruence; contradiction. }
    simpl in HEX. destruct_options.
    unfold Pop_stack_list in Heqo4.
    rewrite HENV_s in Heqo4. inv Heqo4.
    apply Machine_Start_app_iff in HEX.
    destruct HEX as [state_t1 [state1 [env1 [HEXl HEXl'] ] ] ].
    edestruct (IHcomd _ eq_refl) as [HSM1 HER1].
    { eauto. }
    { left. simpl. repeat split; eauto. }
    destruct HSM1 as [
      [HNINV1 [-> HENV1] ] |
      [inv' [state_k'' [ps_list3 [ps_list4 [? [-> [HNINV_k' HENV1] ] ] ] ] ] ] ].
    2:{ simpl in HEXl'. congruence. }
    simpl in HEXl'. unfold End_loop in HEXl'.
    rewrite HENV1 in HEXl'. rewrite Heqo3 in HEXl'. destruct_options.
    repeat split; eauto.
    * left. rewrite <- ! app_assoc. simpl.
      repeat split; eauto.
  - (* C_break *)
    inv HPS. simpl in HEX. destruct_options.
    destruct (Break_vaild (Machine_stack env_s)) eqn:?; [ | discriminate].
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    2:{ rewrite HENV_s in Heqb0. simpl in Heqb0. congruence. }
    unfold Push_stack in Heqo0. rewrite HENV_s in Heqo0. inv Heqo0.
    simpl. repeat split; eauto.
  - (* C_continue *)
    inv HPS. simpl in HEX. destruct_options.
    destruct (Continue_vaild (Machine_stack env_s)) eqn:?; [ | discriminate].
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    2:{ rewrite HENV_s in Heqb0. simpl in Heqb0. congruence. }
    unfold Push_stack in Heqo0. rewrite HENV_s in Heqo0. inv Heqo0.
    simpl. repeat split; eauto.
  - (* C_switch *)
    rename H into IHcases.
    destruct_options. simpl in HEX. destruct_options.
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    2:{ destruct H. contradiction. }
    destruct l as [ | [efirst cfirst] cothers]; simpl in Heqo; [discriminate | ].
    destruct_options. simpl in HEX. destruct_options.
    rename l2 into lfirst. rename l into lothers. rename l1 into ldefault.
    rewrite <- app_assoc in HEX.
    apply Machine_Start_app_iff in HEX.
    destruct HEX as [state_t1 [state1 [env1 [HEXlf HEXlf'] ] ] ].
    inv IHcases. rename H2 into IHfirst. rename H3 into IHothers.
    edestruct (IHfirst _ Heqo2) as [HSM1 HERf].
    { apply HEXlf. }
    { left. repeat split; eauto. }
    destruct HSM1 as [
      [HNINV1 [-> HENV1] ] |
      [inv [state_k' [ps_list1 [ps_list2 [? [-> [HNINV_k HENV1] ] ] ] ] ] ] ].
    2:{ exfalso. clear - Heqo1 HEXlf'. destruct cothers; simpl in *.
        - unfold Some_concat, Find_None in Heqo1. simpl in Heqo1. inv Heqo1.
          simpl in HEXlf'. congruence.
        - apply Some_concat_Some_app in Heqo1.
          destruct Heqo1 as [? [? [? [? ->] ] ] ].
          destruct p. destruct_options. simpl in *.
          congruence. }
    simpl in *.
    apply Machine_Start_app_iff in HEXlf'.
    destruct HEXlf' as [state_t2 [state2 [env2 [HEXlo HEXlo'] ] ] ].
    pose proof (StateMachine_Start_result_cases _ _ Heqo1 IHothers).
    unfold state_stack_match_cases in H0.
    edestruct H0 as [cond' [asrt' [labels1 [labels2 [? [? [? ?] ] ] ] ] ] ].
    { apply HEXlo. }
    { rewrite HENV1. do 4 eexists. repeat split; eauto. }
    { destruct state_t2; auto. simpl in HEXlo'. congruence. }
    inv H1. subst.
    destruct H4 as [state_t_k' [state_k' [ps_list1' [ps_list2' [HENV2 [? ?] ] ] ] ] ].
    destruct state_t_k'; try contradiction. destruct H3 as [<- <-].
    simpl in HEXlo'.
    unfold Pop_stack_list, Push_stack_list, Insert_stack_ps in HEXlo'.
    rewrite HENV2 in HEXlo'. simpl in HEXlo'. destruct_options.
    apply Machine_Start_app_iff in HEXlo'.
    destruct HEXlo' as [state_t3 [state3 [env3 [HEXld HEXld'] ] ] ].
    edestruct (IHcomd _ eq_refl) as [HSM3 HER3].
    { eauto. }
    { left. simpl. repeat split; eauto. }
    destruct HSM3 as [
      [HNINV3 [-> HENV3] ] |
      [inv' [state_k'' [ps_list1 [ps_list2 [? [-> [HNINV_k' HENV3] ] ] ] ] ] ] ].
    2:{ simpl in HEXld'. congruence. }
    simpl in HEXld'. unfold End_switch in HEXld'.
    rewrite HENV3 in HEXld'. rewrite HENV_s in HEXld'. inv HEXld'.
    repeat split; eauto.
    + left. repeat split; eauto. simpl.
      rewrite <- H1. simpl. auto.
    + econstructor; eauto.
      * econstructor; eauto.
        unfold State_update_Normal. simpl. rewrite app_nil_r. auto.
  - (* C_return *)
    inv HPS. simpl in HEX. destruct_options.
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    2:{ destruct H. contradiction. }
    unfold Push_stack in Heqo1.
    rewrite HENV_s in Heqo1. inv Heqo1.
    simpl. repeat split; eauto.
  - (* C_assert *)
    inv HPS. simpl in HEX. destruct_options.
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    + unfold Push_stack in Heqo0. rewrite HENV_s in Heqo0. inv Heqo0.
      simpl. repeat split; eauto.
    + unfold Push_stack in Heqo0. rewrite HENV_s in Heqo0. inv Heqo0.
      simpl. repeat split; eauto.
      * right. exists inv, state_k', ps_list1, (ps_list2 ++ PS_assert l :: nil).
        rewrite <- app_assoc. simpl.
        repeat split; eauto.
  - (* C_inv *)
    inv HPS. simpl in HEX. destruct_options.
    destruct HSM_s as [
      [HNINV_s [-> HENV_s] ] |
      [inv [state_k' [ps_list1 [ps_list2 [-> [-> [HNINV_k HENV_s] ] ] ] ] ] ] ].
    2:{ destruct H. contradiction. }
    simpl. repeat split; eauto.
    + right. rewrite HENV_s.
      do 4 eexists. repeat split; eauto.
Qed.
*)

Definition sublist {A : Type} (l1 : list A) (l2 : list A) : Prop :=
  forall x, In x l1 -> In x l2.

Lemma sublist_refl : forall (A : Type) (l : list A),
  sublist l l.
Proof.
  unfold sublist. intros. intros. apply H.
Qed.

Lemma sublist_trans : forall (A : Type) (l1 l2 l3 : list A),
  sublist l1 l2 -> sublist l2 l3 ->
  sublist l1 l3.
Proof.
  unfold sublist. intros. auto.
Qed.

Lemma sublist_nil : forall (A : Type) (l : list A),
  sublist nil l.
Proof.
  unfold sublist. intros. inv H.
Qed.

Lemma exec_res_sublist :
  forall comd Pre Post,
  exec_res Pre comd Post ->
  (sublist Pre.(Break_ret) Post.(Break_ret)) /\
  (sublist Pre.(Continue_ret) Post.(Continue_ret)) /\
  (sublist Pre.(Return_ret) Post.(Return_ret)).
Proof.
  induction comd; intros.
  - (* C_simple *)
    inv H. unfold State_update_Normal. simpl.
    repeat split; apply sublist_refl.
  - (* C_seq *)
    inv H.
    specialize (IHcomd1 _ _ H3).
    specialize (IHcomd2 _ _ H5).
    destruct IHcomd1 as [? [? ?] ].
    destruct IHcomd2 as [? [? ?] ].
    repeat split; eapply sublist_trans; eauto.
  - (* C_if *)
    inv H. simpl. unfold sublist. repeat split; intros;
    apply in_app_iff; right; apply in_app_iff; right; auto.
  - (* C_while *)
    inv H. simpl. repeat split; try apply sublist_refl.
    + unfold sublist. intros. apply in_app_iff. right. auto.
  - (* C_dowhile *)
    inv H. simpl. repeat split; try apply sublist_refl.
    + unfold sublist. intros. apply in_app_iff. right. auto.
  - (* C_for *)
    inv H. simpl. repeat split; try apply sublist_refl.
    + unfold sublist. intros. apply in_app_iff. right. auto.
  - (* C_break *)
    inv H. simpl. repeat split; try apply sublist_refl.
    + unfold sublist. intros. apply in_app_iff. right. auto.
  - (* C_continue *)
    inv H. simpl. repeat split; try apply sublist_refl.
    + unfold sublist. intros. apply in_app_iff. right. auto.
  - (* C_switch *)
    inv H. simpl. repeat split; try apply sublist_refl.
    + unfold sublist. intros. apply in_app_iff. right. auto.
    + unfold sublist. intros. apply in_app_iff. right. auto.
  - (* C_return *)
    inv H. simpl. repeat split; try apply sublist_refl.
    + unfold sublist. intros. apply in_app_iff. right. auto.
  (*- (* C_assert *)
    inv H. simpl. repeat split; apply sublist_refl.
  - (* C_inv *)
    inv H. simpl. repeat split; apply sublist_refl.*)
Admitted.


Lemma exec_res_case_sublist :
  forall cond asrt cases Pre Post labels1 labels2,
  exec_res_case exec_res cond asrt Pre labels1 cases Post labels2 ->
  (sublist Pre.(Break_ret) Post.(Break_ret)) /\
  (sublist Pre.(Continue_ret) Post.(Continue_ret)) /\
  (sublist Pre.(Return_ret) Post.(Return_ret)).
Proof.
  induction cases; intros.
  - inv H. repeat split; apply sublist_refl.
  - inv H. apply exec_res_sublist in H7. destruct H7 as [? [? ?] ].
    specialize (IHcases _ _ _ _ H10). destruct IHcases as [? [? ?] ].
    repeat split; eapply sublist_trans; eauto.
Qed.


Lemma State_valid_conseq_post : forall env return_val pre Post Post' sem,
  State_valid env return_val pre Post sem ->
  sublist Post.(Normal_ret) Post'.(Normal_ret) ->
  sublist Post.(Break_ret) Post'.(Break_ret) ->
  sublist Post.(Continue_ret) Post'.(Continue_ret) ->
  sublist Post.(Return_ret) Post'.(Return_ret) ->
  State_valid env return_val pre Post' sem.
Proof.
  unfold State_valid, Single_sound, Single_ret_sound, sublist.
  intros. destruct H as [HN [HB [HC HR] ] ].
  repeat split; intros.
  - specialize (HN _ _ _ H H4).
    destruct HN as [Post_asrt [? ?] ].
    exists Post_asrt. split; auto.
  - specialize (HB _ _ _ H H4).
    destruct HB as [Post_asrt [? ?] ].
    exists Post_asrt. split; auto.
  - specialize (HC _ _ _ H H4).
    destruct HC as [Post_asrt [? ?] ].
    exists Post_asrt. split; auto.
Qed.

Lemma State_valid_conseq_pre : forall env return_val Pre Post Pre' sem,
  entail Pre Pre' ->
  (forall pre, In pre Pre' ->
    State_valid env return_val pre Post sem) ->
  (forall pre, In pre Pre ->
    State_valid env return_val pre Post sem).
Proof.
  unfold State_valid, Single_sound, Single_ret_sound.
  intros. unfold entail in H.
  specialize (H _ H1).
  repeat split; intros.
  - specialize (H _ _ _ H2). destruct H as [pre_asrt [? ?] ].
    specialize (H0 _ H). destruct H0 as [? _].
    specialize (H0 _ _ _ H4 H3). auto.
  - specialize (H _ _ _ H2). destruct H as [pre_asrt [? ?] ].
    specialize (H0 _ H). destruct H0 as [_ [? _] ].
    specialize (H0 _ _ _ H4 H3). auto.
  - specialize (H _ _ _ H2). destruct H as [pre_asrt [? ?] ].
    specialize (H0 _ H). destruct H0 as [_ [_ [? _] ] ].
    specialize (H0 _ _ _ H4 H3). auto.
Qed.


Lemma State_valid_seq : forall env return_val Pre Mid Post sem1 sem2,
  forall pre, In pre Pre ->
  State_valid env return_val pre Mid sem1 ->
  (forall pre, In pre Mid.(Normal_ret) ->
    State_valid env return_val pre Post sem2) ->
  sublist Mid.(Break_ret) Post.(Break_ret) ->
  sublist Mid.(Continue_ret) Post.(Continue_ret) ->
  sublist Mid.(Return_ret) Post.(Return_ret) ->
  State_valid env return_val pre Post (Cseq_denote sem1 sem2).
Proof.
  unfold State_valid, Single_sound, Single_ret_sound, Cseq_denote. simpl.
  intros. rename H2 into HSLB. rename H3 into HSLC. rename H4 into HSLR.
  repeat split; intros.
  - destruct H3 as [Mid_st [? ?] ].
    destruct H0 as [? _].
    specialize (H0 _ _ _ H2 H3).
    destruct H0 as [Mid_asrt [? ?] ].
    specialize (H1 _ H0). destruct H1 as [? _].
    specialize (H1 _ _ _ H5 H4).
    destruct H1 as [Post_asrt [? ?] ].
    exists Post_asrt. split; auto.
  - destruct H3 as [? | [Mid_st [? ?] ] ].
    + destruct H0 as [_ [? _] ].
      specialize (H0 _ _ _ H2 H3).
      destruct H0 as [Post_asrt [? ?] ].
      exists Post_asrt. split; auto.
    + destruct H0 as [? _].
      specialize (H0 _ _ _ H2 H3).
      destruct H0 as [Mid_asrt [? ?] ].
      specialize (H1 _ H0). destruct H1 as [_ [? _] ].
      specialize (H1 _ _ _ H5 H4).
      destruct H1 as [Post_asrt [? ?] ].
      exists Post_asrt. split; auto.
  - destruct H3 as [? | [Mid_st [? ?] ] ].
    + destruct H0 as [_ [_ [? _] ] ].
      specialize (H0 _ _ _ H2 H3).
      destruct H0 as [Post_asrt [? ?] ].
      exists Post_asrt. split; auto.
    + destruct H0 as [? _].
      specialize (H0 _ _ _ H2 H3).
      destruct H0 as [Mid_asrt [? ?] ].
      specialize (H1 _ H0). destruct H1 as [_ [_ [? _] ] ].
      specialize (H1 _ _ _ H5 H4).
      destruct H1 as [Post_asrt [? ?] ].
      exists Post_asrt. split; auto.
Qed.


Lemma exec_res_sound_loop :
  forall env callees return_val
         cond body incr inv Pre Post fres sres Post1 incr_res
         body_denote incr_denote,
  body_denote = Cstatement_denote env callees return_val body ->
  incr_denote = Csimplecommand_denote env callees incr ->
  If_Condition_exec_list' inv cond = Some (fres, sres) ->
  exec_res (mk_State fres nil nil nil) body Post1 ->
  SimpleCommand_exec_list' (Post1.(Normal_ret) ++ Post1.(Continue_ret)) incr = Some incr_res ->
  entail incr_res inv ->
  Post = mk_State (sres ++ Post1.(Break_ret)) Pre.(Break_ret)
                  Pre.(Continue_ret) (Post1.(Return_ret) ++ Pre.(Return_ret)) ->
  (forall Pre Post,
    exec_res Pre body Post ->
   forall pre, In pre Pre.(Normal_ret) ->
   State_valid env return_val pre Post
     (Cstatement_denote env callees return_val body)) ->
  forall pre, In pre inv ->
  State_valid env return_val pre Post
    (loop_denote (Truth_denote env callees cond) (Falth_denote env callees cond) (NormalExit body_denote) (BreakExit body_denote) (ContExit body_denote) (ReturnExit body_denote) (NormalExit incr_denote)).
Proof.
  intros. subst. rename H6 into Hbody.
  pose proof (Hcond :=
    If_Condition_exec_list_sound env callees return_val
      Safety_checker _ _ _ _ H1). clear H1.
  pose proof (Hincr :=
    SimpleCommand_exec_list_sound env callees return_val
      Safety_checker _ _ _ H3). clear H3.
  unfold entail in H4.
  unfold State_valid, Single_sound, Single_ret_sound.
  simpl. unfold BW_LFix, omega_lub, oLub_while_fin.
  sets_unfold. repeat split; intros.
  - destruct H0 as [n ?].
    generalize dependent Pre_st.
    generalize dependent pre.
    induction n; intros; simpl in H0; [contradiction | ].
    specialize (Hcond _ H7). clear H7.
    destruct Hcond as [T_Post [F_Post [_ [HIn_fres [Hin_sres [HcondT HcondF] ] ] ] ] ].
    destruct H0 as [ [ [? | ?] | ?] | ?].
    + destruct H0 as [Mid_st1 [HTr [Mid_st2 [HN12 [Mid_st3 [? ?] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ H HTr).
      destruct HcondT as [Mid_asrt1 [HIn_TP HAd1] ].
      specialize (Hbody _ _ H2). simpl in Hbody.
      specialize (Hbody _ (HIn_fres _ HIn_TP)).
      destruct Hbody as [Hbody _].
      unfold State_valid, Single_sound in Hbody.
      specialize (Hbody _ _ _ HAd1 HN12).
      destruct Hbody as [Mid_asrt2 [HIn_post1 HAd2] ].
      assert (HIn_post1' : In Mid_asrt2 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. left. auto. }
      specialize (Hincr _ HIn_post1').
      destruct Hincr as [Mid_asrt3 [_ [HIn_incr Hincr] ] ].
      unfold State_valid, Single_sound in Hincr.
      destruct Hincr as [Hincr _].
      specialize (Hincr _ _ _ HAd2 H0). simpl in Hincr.
      destruct Hincr as [Mid_asrt4 [HIn3 HAd4] ].
      specialize (H4 _ (HIn_incr _ HIn3) _ _ _ HAd4).
      destruct H4 as [post_st [HIn_inv HAd_post] ].
      specialize (IHn _ HIn_inv _ HAd_post H1). auto.
    + unfold State_valid, Single_sound in HcondF.
      destruct HcondF as [HcondF _]. simpl in HcondF.
      specialize (HcondF _ _ _ H H0).
      destruct HcondF as [Post_asrt [HIn_FP HAd_Post] ].
      exists Post_asrt. split; auto.
      apply in_app_iff. left. auto.
    + destruct H0 as [Mid_st1 [HTr [Mid_st2 [HN12 [Mid_st3 [? ?] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ H HTr).
      destruct HcondT as [Mid_asrt1 [HIn_TP HAd1] ].
      specialize (Hbody _ _ H2). simpl in Hbody.
      specialize (Hbody _ (HIn_fres _ HIn_TP)).
      destruct Hbody as [_ [_ [Hbody _] ] ].
      unfold State_valid, Single_sound in Hbody.
      specialize (Hbody _ _ _ HAd1 HN12).
      destruct Hbody as [Mid_asrt2 [HIn_post1 HAd2] ].
      assert (HIn_post1' : In Mid_asrt2 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. right. auto. }
      specialize (Hincr _ HIn_post1').
      destruct Hincr as [Mid_asrt3 [_ [HIn_incr Hincr] ] ].
      unfold State_valid, Single_sound in Hincr.
      destruct Hincr as [Hincr _].
      specialize (Hincr _ _ _ HAd2 H0). simpl in Hincr.
      destruct Hincr as [Mid_asrt4 [HIn3 HAd4] ].
      specialize (H4 _ (HIn_incr _ HIn3) _ _ _ HAd4).
      destruct H4 as [post_st [HIn_inv HAd_post] ].
      specialize (IHn _ HIn_inv _ HAd_post H1). auto.
    + destruct H0 as [Mid_st [HTr HBreak] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ H HTr).
      destruct HcondT as [Mid_asrt1 [HIn_TP HAd1] ].
      specialize (Hbody _ _ H2). simpl in Hbody.
      specialize (Hbody _ (HIn_fres _ HIn_TP)).
      destruct Hbody as [_ [Hbody _] ].
      unfold State_valid, Single_sound in Hbody.
      specialize (Hbody _ _ _ HAd1 HBreak).
      destruct Hbody as [Post_asrt [HIn_post HAd_Post] ].
      exists Post_asrt. split; auto.
      apply in_app_iff. right. auto.
  - contradiction.
  - contradiction.
  (* - destruct H0 as [n ?].
    generalize dependent Pre_st.
    generalize dependent pre.
    induction n; intros; simpl in H0; [contradiction | ].
    specialize (Hcond _ H7). clear H7.
    destruct Hcond as [T_Post [F_Post [_ [HIn_fres [Hin_sres [HcondT HcondF] ] ] ] ] ].
    destruct H0 as [ [? | ?] | ?].
    + destruct H0 as [Mid_st1 [HTr [Mid_st2 [HN12 [Mid_st3 [? ?] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ H HTr).
      destruct HcondT as [Mid_asrt1 [HIn_TP HAd1] ].
      specialize (Hbody _ _ H2). simpl in Hbody.
      specialize (Hbody _ (HIn_fres _ HIn_TP)).
      destruct Hbody as [Hbody _].
      unfold State_valid, Single_sound in Hbody.
      specialize (Hbody _ _ _ HAd1 HN12).
      destruct Hbody as [Mid_asrt2 [HIn_post1 HAd2] ].
      assert (HIn_post1' : In Mid_asrt2 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. left. auto. }
      specialize (Hincr _ HIn_post1').
      destruct Hincr as [Mid_asrt3 [_ [HIn_incr Hincr] ] ].
      unfold State_valid, Single_sound in Hincr.
      destruct Hincr as [Hincr _].
      specialize (Hincr _ _ _ HAd2 H0). simpl in Hincr.
      destruct Hincr as [Mid_asrt4 [HIn3 HAd4] ].
      specialize (H4 _ (HIn_incr _ HIn3) _ _ _ HAd4).
      destruct H4 as [post_st [HIn_inv HAd_post] ].
      specialize (IHn _ HIn_inv _ HAd_post H1). auto.
    + destruct H0 as [Mid_st1 [HTr [Mid_st2 [HN12 [Mid_st3 [? ?] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ H HTr).
      destruct HcondT as [Mid_asrt1 [HIn_TP HAd1] ].
      specialize (Hbody _ _ H2). simpl in Hbody.
      specialize (Hbody _ (HIn_fres _ HIn_TP)).
      destruct Hbody as [_ [_ [Hbody _] ] ].
      unfold State_valid, Single_sound in Hbody.
      specialize (Hbody _ _ _ HAd1 HN12).
      destruct Hbody as [Mid_asrt2 [HIn_post1 HAd2] ].
      assert (HIn_post1' : In Mid_asrt2 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. right. auto. }
      specialize (Hincr _ HIn_post1').
      destruct Hincr as [Mid_asrt3 [_ [HIn_incr Hincr] ] ].
      unfold State_valid, Single_sound in Hincr.
      destruct Hincr as [Hincr _].
      specialize (Hincr _ _ _ HAd2 H0). simpl in Hincr.
      destruct Hincr as [Mid_asrt4 [HIn3 HAd4] ].
      specialize (H4 _ (HIn_incr _ HIn3) _ _ _ HAd4).
      destruct H4 as [post_st [HIn_inv HAd_post] ].
      specialize (IHn _ HIn_inv _ HAd_post H1). auto.
    + destruct H0 as [Mid_st [HTr HReturn] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ H HTr).
      destruct HcondT as [Mid_asrt1 [HIn_TP HAd1] ].
      specialize (Hbody _ _ H2). simpl in Hbody.
      specialize (Hbody _ (HIn_fres _ HIn_TP)).
      destruct Hbody as [_ [_ [_ Hbody] ] ].
      unfold Single_ret_sound in Hbody.
      specialize (Hbody _ _ _ HAd1 HReturn).
      destruct Hbody as [Post_asrt [HIn_post HPost] ].
      exists Post_asrt. split; auto.
      apply in_app_iff. left. auto. *)
Qed.


Lemma exec_res_sound_dowhile :
  forall env callees return_val
         cond body inv Pre Post fres sres Post1 body_denote,
  body_denote = Cstatement_denote env callees return_val body ->
  exec_res (mk_State inv nil nil nil) body Post1 ->
  If_Condition_exec_list' (Post1.(Normal_ret) ++ Post1.(Continue_ret)) cond = Some (fres, sres) ->
  entail fres inv ->
  Post = mk_State (sres ++ Post1.(Break_ret)) Pre.(Break_ret)
                  Pre.(Continue_ret) (Post1.(Return_ret) ++ Pre.(Return_ret)) ->
  (forall Pre Post,
   exec_res Pre body Post ->
   forall pre, In pre Pre.(Normal_ret) ->
   State_valid env return_val pre Post
     (Cstatement_denote env callees return_val body)) ->
  forall pre, In pre inv ->
  State_valid env return_val pre Post
    (Cdowhile_denote env callees cond body_denote).
Proof.
  intros. subst. rename H4 into Hbody.
  pose proof (Hcond :=
    If_Condition_exec_list_sound env callees return_val
      Safety_checker _ _ _ _ H1). clear H1.
  unfold State_valid, Single_sound, Single_ret_sound.
  simpl in *. unfold BW_LFix, omega_lub, oLub_while_fin.
  sets_unfold. repeat split; intros.
  - destruct H1 as [n ?].
    generalize dependent Pre_st.
    generalize dependent pre.
    induction n; intros; simpl in H1; [contradiction | ].
    specialize (Hbody _ _ H0 _ H5).
    destruct H1 as [ [ [? | ?] | ?] | ?].
    + destruct H1 as [Mid_st1 [HN1 [Mid_st2 [HTr ?] ] ] ].
      unfold State_valid, Single_sound in Hbody.
      destruct Hbody as [Hbody _].
      specialize (Hbody _ _ _ H HN1).
      destruct Hbody as [Mid_asrt1 [HIn_post1 HAd1] ].
      assert (HIn_post1' : In Mid_asrt1 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. left. auto. }
      specialize (Hcond _ HIn_post1').
      destruct Hcond as [T_Post [F_Post [_ [HIn_fres [HIn_sres [HcondT HcondF] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ HAd1 HTr).
      destruct HcondT as [Mid_asrt2 [HIn_TP HAd2] ].
      specialize (H2 _ (HIn_fres _ HIn_TP) _ _ _ HAd2).
      destruct H2 as [Mid_asrt3 [HIn_inv HAd3] ].
      specialize (IHn _ HIn_inv _ HAd3 H1).
      auto.
    + destruct H1 as [Mid_st1 [HN1 HFl] ].
      unfold State_valid, Single_sound in Hbody.
      destruct Hbody as [Hbody _].
      specialize (Hbody _ _ _ H HN1).
      destruct Hbody as [Mid_asrt1 [HIn_post1 HAd1] ].
      assert (HIn_post1' : In Mid_asrt1 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. left. auto. }
      specialize (Hcond _ HIn_post1').
      destruct Hcond as [T_Post [F_Post [_ [HIn_fres [HIn_sres [HcondT HcondF] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondF as [HcondF _]. simpl in HcondF.
      specialize (HcondF _ _ _ HAd1 HFl).
      destruct HcondF as [Post_asrt [HIn_FP HAd_Post] ].
      exists Post_asrt.
      split; auto.
      apply in_app_iff. left. auto.
    + destruct H1 as [Mid_st1 [HC1 [Mid_st2 [HTr ?] ] ] ].
      unfold State_valid, Single_sound in Hbody.
      destruct Hbody as [_ [_ [Hbody _] ] ].
      specialize (Hbody _ _ _ H HC1).
      destruct Hbody as [Mid_asrt1 [HIn_post1 HAd1] ].
      assert (HIn_post1' : In Mid_asrt1 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. right. auto. }
      specialize (Hcond _ HIn_post1').
      destruct Hcond as [T_Post [F_Post [_ [HIn_fres [HIn_sres [HcondT HcondF] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ HAd1 HTr).
      destruct HcondT as [Mid_asrt2 [HIn_TP HAd2] ].
      specialize (H2 _ (HIn_fres _ HIn_TP) _ _ _ HAd2).
      destruct H2 as [Mid_asrt3 [HIn_inv HAd3] ].
      specialize (IHn _ HIn_inv _ HAd3 H1).
      auto.
    + unfold State_valid, Single_sound in Hbody.
      destruct Hbody as [_ [Hbody _] ].
      specialize (Hbody _ _ _ H H1).
      destruct Hbody as [Post_asrt [HIn_post1 HAd_Post] ].
      exists Post_asrt.
      split; auto.
      apply in_app_iff. right. auto.
  - contradiction.
  - contradiction.
  (* - destruct H1 as [n ?].
    generalize dependent Pre_st.
    generalize dependent pre.
    induction n; intros; simpl in H1; [contradiction | ].
    specialize (Hbody _ _ H0 _ H5).
    destruct H1 as [ [? | ?] | ?].
    + destruct H1 as [Mid_st1 [HN1 [Mid_st2 [HTr ?] ] ] ].
      unfold State_valid, Single_sound in Hbody.
      destruct Hbody as [Hbody _].
      specialize (Hbody _ _ _ H HN1).
      destruct Hbody as [Mid_asrt1 [HIn_post1 HAd1] ].
      assert (HIn_post1' : In Mid_asrt1 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. left. auto. }
      specialize (Hcond _ HIn_post1').
      destruct Hcond as [T_Post [F_Post [_ [HIn_fres [HIn_sres [HcondT HcondF] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ HAd1 HTr).
      destruct HcondT as [Mid_asrt2 [HIn_TP HAd2] ].
      specialize (H2 _ (HIn_fres _ HIn_TP) _ _ _ HAd2).
      destruct H2 as [Mid_asrt3 [HIn_inv HAd3] ].
      specialize (IHn _ HIn_inv _ HAd3 H1).
      auto.
    + destruct H1 as [Mid_st1 [HC1 [Mid_st2 [HTr ?] ] ] ].
      unfold State_valid, Single_sound in Hbody.
      destruct Hbody as [_ [_ [Hbody _] ] ].
      specialize (Hbody _ _ _ H HC1).
      destruct Hbody as [Mid_asrt1 [HIn_post1 HAd1] ].
      assert (HIn_post1' : In Mid_asrt1 (Normal_ret Post1 ++ Continue_ret Post1)).
      { apply in_app_iff. right. auto. }
      specialize (Hcond _ HIn_post1').
      destruct Hcond as [T_Post [F_Post [_ [HIn_fres [HIn_sres [HcondT HcondF] ] ] ] ] ].
      unfold State_valid, Single_sound in HcondT.
      destruct HcondT as [HcondT _]. simpl in HcondT.
      specialize (HcondT _ _ _ HAd1 HTr).
      destruct HcondT as [Mid_asrt2 [HIn_TP HAd2] ].
      specialize (H2 _ (HIn_fres _ HIn_TP) _ _ _ HAd2).
      destruct H2 as [Mid_asrt3 [HIn_inv HAd3] ].
      specialize (IHn _ HIn_inv _ HAd3 H1).
      auto.
    + unfold State_valid, Single_sound in Hbody.
      destruct Hbody as [_ [_ [_ Hbody] ] ].
      specialize (Hbody _ _ _ H H1).
      destruct Hbody as [Post_asrt [HIn_post1 HAd_Post] ].
      exists Post_asrt.
      split; auto.
      apply in_app_iff. left. auto. *)
Qed.


Lemma Find_Zeqb_false : forall l x,
  Find Z.eqb l x = false <-> ~ In x l.
Proof.
  unfold not. intros. induction l; simpl in *.
  - split; auto.
  - destruct (x =? a) eqn:Heq; [apply Z.eqb_eq in Heq | apply Z.eqb_neq in Heq].
    + subst. split; intros.
      * congruence.
      * exfalso. apply H. auto.
    + split; intros.
      * destruct H0; [congruence | tauto].
      * apply IHl. intros. tauto.
Qed.


Lemma exec_res_case_split :
  forall cond cases asrt Pre labels1 Post labels2,
  exec_res_case exec_res cond asrt Pre labels1 cases Post labels2 ->
  exists labels3, labels2 = labels3 ++ labels1 /\
  forall l, ~ (In l labels3 /\ In l labels1).
Proof.
  unfold not. intros. induction H.
  - exists nil. simpl. split; auto.
    intros. tauto.
  - destruct IHexec_res_case as [labels3 [-> ?] ].
    exists (labels3 ++ sres :: nil).
    rewrite <- app_assoc. simpl. split; auto.
    intros. destruct H5.
    apply in_app_iff in H5. destruct H5.
    + apply (H4 l). split; auto.
      right. auto.
    + apply Find_Zeqb_false in H0.
      inv H5; auto.
Qed.

Lemma exec_res_sound_cases_falth :
  forall env callees return_val cond cases default
         asrt Pre Post labels0 labels falth body res,
  exec_res_case exec_res cond asrt Pre labels0 cases Post (labels ++ labels0) ->
  Ccase_denote env callees (Cstatement_denote env callees return_val)
    cond cases default = (falth, body, res) ->
  Valid_cases_expr (map fst cases) = (rev labels, true) /\
  (falth ⊆
    (fold_right
      (fun y s => (Falth_denote env callees (C_binop CO_EQ cond y (type_of cond))) ∩ s)
      Rels.id (map fst cases))).
Proof.
  sets_unfold.
  induction cases; intros; simpl in *.
  - inv H0. inv H. repeat split; auto.
    + assert (length labels0 = length (labels ++ labels0)) by congruence.
      rewrite app_length in H.
      destruct labels; auto. simpl in H. lia.
  - destruct a. simpl. inv H0. inv H.
    destruct (Ccase_denote env callees (Cstatement_denote env callees return_val) cond cases default) as [ [falth1 body1] res1] eqn:?.
    inv H2.
    pose proof (exec_res_case_split _ _ _ _ _ _ _ H12).
    destruct H as [labels3 [? ?] ].
    replace (labels3 ++ sres :: labels0) with ((labels3 ++ sres :: nil) ++ labels0) in H
      by (rewrite <- app_assoc; auto).
    apply app_inv_tail_iff in H. subst.
    rewrite <- app_assoc in H12. simpl in H12.
    specialize (IHcases _ _ _ _ _ _ _ _ _ H12 Heqp).
    destruct IHcases as [? ?].
    destruct (Valid_cases_expr (map fst cases)) eqn:?.
    inv H.
    pose proof (Switch_Condition_exec_list_sound env callees return_val _ _ _ _ _ _ H4).
    destruct H as [? _].
    rewrite H. simpl. split.
    + f_equal.
      * rewrite rev_app_distr. simpl. auto.
      * apply negb_true_iff.
        apply Find_Zeqb_false. apply Find_Zeqb_false in H5.
        intros ?. apply in_rev in H2.
        apply (H0 sres). split; auto. left. auto.
    + sets_unfold. intros.
      destruct H2. specialize (H1 _ _ H3). split; auto.
Qed.


Lemma exec_res_sound_cases_body :
  forall env callees return_val cond cases default
         asrt Pre Post1 Post labels0 labels falth body res,
   (Forall
     (fun p : Cexpr * Cstatement =>
       forall Pre Post : State,
       exec_res Pre (snd p) Post ->
       forall pre : assertion,
       In pre (Normal_ret Pre) ->
       State_valid env return_val pre Post
         (Cstatement_denote env callees return_val (snd p)))
     cases) ->
  exec_res_case exec_res cond asrt Pre labels0 cases Post1 (labels ++ labels0) ->
  Ccase_denote env callees (Cstatement_denote env callees return_val)
    cond cases default = (falth, body, res) ->
  (forall pre, In pre Post1.(Normal_ret) ->
   State_valid env return_val pre Post default) ->
  ((sublist Post1.(Break_ret) Post.(Break_ret)) /\
   (sublist Post1.(Continue_ret) Post.(Continue_ret)) /\
   (sublist Post1.(Return_ret) Post.(Return_ret))) ->
  (forall pre, In pre Pre.(Normal_ret) ->
   State_valid env return_val pre Post body).
Proof.
  induction cases; simpl; intros * Hcases ? ? Hdefault Hdefault_sublist.
  - inv H0. inv H. auto.
  - destruct a.
    destruct (Ccase_denote env callees (Cstatement_denote env callees return_val) cond cases default) as [ [falth0 body0] res0] eqn:?.
    inv H. inv H0. inv Hcases.
    pose proof (exec_res_case_split _ _ _ _ _ _ _ H12).
    destruct H as [labels3 [? ?] ].
    replace (labels3 ++ sres :: labels0) with ((labels3 ++ sres :: nil) ++ labels0) in H
      by (rewrite <- app_assoc; auto).
    apply app_inv_tail_iff in H. subst. simpl in *.
    rewrite <- app_assoc in H12. simpl in H12.
    specialize (IHcases _ _ _ _ _ _ _ _ _ _ H2 H12 Heqp Hdefault).
    specialize (H1 _ _ H11). simpl in H1.
    intros.
    assert (In pre (fres ++ Normal_ret Pre)).
    { apply in_app_iff. right. auto. }
    specialize (H1 _ H3).
    unfold Cseq_denote, State_valid, Single_sound, Single_ret_sound.
    simpl. repeat split; intros.
    + destruct H7 as [Mid_st1 [Hc0 Hbody0] ].
      destruct H1 as [? _].
      unfold Single_sound in H1.
      specialize (H1 _ _ _ H6 Hc0).
      destruct H1 as [Mid_asrt1 [? ?] ].
      specialize (IHcases Hdefault_sublist _ H1).
      destruct IHcases as [IHcases ?].
      unfold Single_sound in IHcases.
      specialize (IHcases _ _ _ H7 Hbody0).
      destruct IHcases as [Post_asrt [? ?] ].
      exists Post_asrt. split; auto.
    + destruct H7 as [Hc0 | [Mid_st1 [Hc0 Hbody] ] ].
      * destruct H1 as [_ [? _] ].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H6 Hc0).
        destruct H1 as [Post_asrt [? ?] ].
        pose proof (exec_res_case_sublist _ _ _ _ _ _ _ H12).
        destruct H8 as [? _]. destruct Hdefault_sublist as [? _].
        exists Post_asrt. split; auto.
      * destruct H1 as [? _].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H6 Hc0).
        destruct H1 as [Mid_asrt1 [? ?] ].
        specialize (IHcases Hdefault_sublist _ H1).
        destruct IHcases as [_ [IHcases _] ].
        unfold Single_sound in IHcases.
        specialize (IHcases _ _ _ H7 Hbody).
        destruct IHcases as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
    + destruct H7 as [Hc0 | [Mid_st1 [Hc0 Hbody] ] ].
      * destruct H1 as [_ [_ [? _] ] ].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H6 Hc0).
        destruct H1 as [Post_asrt [? ?] ].
        pose proof (exec_res_case_sublist _ _ _ _ _ _ _ H12).
        destruct H8 as [_ [? _] ]. destruct Hdefault_sublist as [_ [? _] ].
        exists Post_asrt. split; auto.
      * destruct H1 as [? _].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H6 Hc0).
        destruct H1 as [Mid_asrt1 [? ?] ].
        specialize (IHcases Hdefault_sublist _ H1).
        destruct IHcases as [_ [_ [IHcases _] ] ].
        unfold Single_sound in IHcases.
        specialize (IHcases _ _ _ H7 Hbody).
        destruct IHcases as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
    (* + destruct H7 as [Hc0 | [Mid_st1 [Hc0 Hbody] ] ].
      * destruct H1 as [_ [_ [_ ?] ] ].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H6 Hc0).
        destruct H1 as [Post_asrt [? ?] ].
        pose proof (exec_res_case_sublist _ _ _ _ _ _ _ H12).
        destruct H8 as [_ [_ ?] ]. destruct Hdefault_sublist as [_ [_ ?] ].
        exists Post_asrt. split; auto.
      * destruct H1 as [? _].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H6 Hc0).
        destruct H1 as [Mid_asrt1 [? ?] ].
        specialize (IHcases Hdefault_sublist _ H1).
        destruct IHcases as [_ [_ [_ IHcases] ] ].
        unfold Single_sound in IHcases.
        specialize (IHcases _ _ _ H7 Hbody).
        destruct IHcases as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto. *)
Qed.


Lemma exec_res_sound_cases_res :
  forall env callees return_val cond cases default
         asrt Pre Post1 Post labels0 labels falth body res,
   (Forall
     (fun p : Cexpr * Cstatement =>
       forall Pre Post : State,
       exec_res Pre (snd p) Post ->
       forall pre : assertion,
       In pre (Normal_ret Pre) ->
       State_valid env return_val pre Post
         (Cstatement_denote env callees return_val (snd p)))
     cases) ->
  exec_res_case exec_res cond asrt Pre labels0 cases Post1 (labels ++ labels0) ->
  Ccase_denote env callees (Cstatement_denote env callees return_val)
    cond cases default = (falth, body, res) ->
  (forall pre, In pre Post1.(Normal_ret) ->
   State_valid env return_val pre Post default) ->
  ((sublist Post1.(Break_ret) Post.(Break_ret)) /\
   (sublist Post1.(Continue_ret) Post.(Continue_ret)) /\
   (sublist Post1.(Return_ret) Post.(Return_ret))) ->
  (forall pre, In pre asrt ->
   State_valid env return_val pre Post res).
Proof.
  induction cases; simpl; intros * Hcases ? ? Hdefault Hdefault_sublist.
  - inv H0. unfold State_valid, Single_sound, Single_ret_sound.
    simpl. repeat split; intros; contradiction.
  - destruct a.
    destruct (Ccase_denote env callees (Cstatement_denote env callees return_val) cond cases default) as [ [falth0 body0] res0] eqn:?.
    inv H. inv H0. inv Hcases.
    pose proof (exec_res_case_split _ _ _ _ _ _ _ H12).
    destruct H as [labels3 [? ?] ].
    replace (labels3 ++ sres :: labels0) with ((labels3 ++ sres :: nil) ++ labels0) in H
      by (rewrite <- app_assoc; auto).
    apply app_inv_tail_iff in H. subst. simpl in *.
    rewrite <- app_assoc in H12. simpl in H12.
    specialize (IHcases _ _ _ _ _ _ _ _ _ _ H2 H12 Heqp Hdefault Hdefault_sublist).
    specialize (H1 _ _ H11). simpl in H1.
    unfold State_valid, Single_sound, Single_ret_sound. simpl.
    pose proof (Switch_Condition_exec_list_sound env callees return_val Safety_checker
                  _ _ _ _ _ H4).
    destruct H.
    repeat split; intros.
    + destruct H8 as [ [Mid_st1 [HTr [Mid_st2 [Hc0 Hbody] ] ] ] | Hres0 ].
      * specialize (H3 _ H6).
        destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H7 HTr).
        destruct H3 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (fres ++ Normal_ret Pre)).
        { apply in_app_iff. left. auto. }
        specialize (H1 _ H9).
        destruct H1 as [? _].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H8 Hc0).
        destruct H1 as [Mid_asrt2 [? ?] ].
        eapply exec_res_sound_cases_body; eauto.
      * specialize (IHcases _ H6).
        destruct IHcases as [IHcases _].
        unfold Single_sound in IHcases.
        eauto.
    + destruct H8 as [ [Mid_st1 [HTr [Hc0 | [Mid_st2 [Hc0 Hbody] ] ] ] ] | Hres0 ].
      * specialize (H3 _ H6).
        destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H7 HTr).
        destruct H3 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (fres ++ Normal_ret Pre)).
        { apply in_app_iff. left. auto. }
        specialize (H1 _ H9).
        destruct H1 as [_ [? _] ].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H8 Hc0).
        destruct H1 as [Post_asrt [? ?] ].
        pose proof (exec_res_case_sublist _ _ _ _ _ _ _ H12).
        destruct H13 as [? _]. destruct Hdefault_sublist as [? _].
        exists Post_asrt. split; auto.
      * specialize (H3 _ H6).
        destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H7 HTr).
        destruct H3 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (fres ++ Normal_ret Pre)).
        { apply in_app_iff. left. auto. }
        specialize (H1 _ H9).
        destruct H1 as [? _].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H8 Hc0).
        destruct H1 as [Mid_asrt2 [? ?] ].
        eapply exec_res_sound_cases_body; eauto.
      * specialize (IHcases _ H6).
        destruct IHcases as [_ [IHcases _]].
        unfold Single_sound in IHcases.
        eauto.
    + destruct H8 as [ [Mid_st1 [HTr [Hc0 | [Mid_st2 [Hc0 Hbody] ] ] ] ] | Hres0 ].
      * specialize (H3 _ H6).
        destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H7 HTr).
        destruct H3 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (fres ++ Normal_ret Pre)).
        { apply in_app_iff. left. auto. }
        specialize (H1 _ H9).
        destruct H1 as [_ [_ [? _] ] ].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H8 Hc0).
        destruct H1 as [Post_asrt [? ?] ].
        pose proof (exec_res_case_sublist _ _ _ _ _ _ _ H12).
        destruct H13 as [_ [? _] ]. destruct Hdefault_sublist as [_ [? _] ].
        exists Post_asrt. split; auto.
      * specialize (H3 _ H6).
        destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H7 HTr).
        destruct H3 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (fres ++ Normal_ret Pre)).
        { apply in_app_iff. left. auto. }
        specialize (H1 _ H9).
        destruct H1 as [? _].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H8 Hc0).
        destruct H1 as [Mid_asrt2 [? ?] ].
        eapply exec_res_sound_cases_body; eauto.
      * specialize (IHcases _ H6).
        destruct IHcases as [_ [_ [IHcases _] ] ].
        unfold Single_sound in IHcases.
        eauto.
    (* + destruct H8 as [ [Mid_st1 [HTr [Hc0 | [Mid_st2 [Hc0 Hbody] ] ] ] ] | Hres0 ].
      * specialize (H3 _ H6).
        destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H7 HTr).
        destruct H3 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (fres ++ Normal_ret Pre)).
        { apply in_app_iff. left. auto. }
        specialize (H1 _ H9).
        destruct H1 as [_ [_ [_ ?] ] ].
        unfold Single_ret_sound in H1.
        specialize (H1 _ _ _ H8 Hc0).
        destruct H1 as [Post_asrt [? ?] ].
        pose proof (exec_res_case_sublist _ _ _ _ _ _ _ H12).
        destruct H13 as [_ [_ ?] ]. destruct Hdefault_sublist as [_ [_ ?] ].
        exists Post_asrt. split; auto.
      * specialize (H3 _ H6).
        destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H7 HTr).
        destruct H3 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (fres ++ Normal_ret Pre)).
        { apply in_app_iff. left. auto. }
        specialize (H1 _ H9).
        destruct H1 as [? _].
        unfold Single_sound in H1.
        specialize (H1 _ _ _ H8 Hc0).
        destruct H1 as [Mid_asrt2 [? ?] ].
        eapply exec_res_sound_cases_body; eauto.
      * specialize (IHcases _ H6).
        destruct IHcases as [_ [_ [_ IHcases] ] ].
        unfold Single_ret_sound in IHcases.
        eauto. *)
Qed.


Theorem exec_res_sound :
  forall env callees return_val comd Pre Post,
  exec_res Pre comd Post ->
  forall pre, In pre Pre.(Normal_ret) ->
  State_valid env return_val pre Post
    (Cstatement_denote env callees return_val comd).
Proof.
Admitted. (*
  induction comd using Cstatement_ind2; intros; simpl in *.
  - (* C_simple *)
    inv H.
    unfold State_update_Normal.
    pose proof (SimpleCommand_exec_list_sound env callees return_val
                  Safety_checker _ _ _ H2 _ H0).
    destruct H as [Post' [_ [? ?] ] ].
    apply (State_valid_conseq_post _ _ _ _ _ _ H1); simpl;
    try apply sublist_nil.
    eapply sublist_trans; eauto. apply sublist_refl.
  - (* C_seq *)
    inv H.
    specialize (IHcomd1 _ _ H4 _ H0).
    specialize (IHcomd2 _ _ H6).
    destruct (exec_res_sublist _ _ _ H6) as [? [? ?] ].
    apply (State_valid_seq _ _ _ _ _ _ _ _ H0 IHcomd1 IHcomd2 H H1 H2).
  - (* C_if *)
    inv H.
    specialize (IHcomd1 _ _ H6).
    specialize (IHcomd2 _ _ H8).
    simpl in *.
    pose proof (If_Condition_exec_list_sound env callees return_val
                  Safety_checker _ _ _ _ H4 _ H0).
    destruct H as [T_Post' [F_Post' [_ [? [? [? ?] ] ] ] ] ].
    unfold Cif_denote, State_valid, Single_sound, Single_ret_sound.
    simpl. repeat split; intros.
    + destruct H7 as [ [Mid_st [? ?] ] | [Mid_st [? ?] ] ].
      * destruct H2 as [? _].
        unfold Single_sound in H2. simpl in H2.
        specialize (H2 _ _ _ H5 H7).
        destruct H2 as [Mid_asrt [? ?] ].
        specialize (IHcomd1 _ (H _ H2)).
        destruct IHcomd1 as [IHcomdN1 _].
        unfold Single_sound in IHcomdN1.
        specialize (IHcomdN1 _ _ _ H10 H9).
        destruct IHcomdN1 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
      * destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H5 H7).
        destruct H3 as [Mid_asrt [? ?] ].
        specialize (IHcomd2 _ (H1 _ H3)).
        destruct IHcomd2 as [IHcomdN2 _].
        unfold Single_sound in IHcomdN2.
        specialize (IHcomdN2 _ _ _ H10 H9).
        destruct IHcomdN2 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. right. auto.
    + destruct H7 as [ [Mid_st [? ?] ] | [Mid_st [? ?] ] ].
      * destruct H2 as [? _].
        unfold Single_sound in H2. simpl in H2.
        specialize (H2 _ _ _ H5 H7).
        destruct H2 as [Mid_asrt [? ?] ].
        specialize (IHcomd1 _ (H _ H2)).
        destruct IHcomd1 as [_ [IHcomdB1 _] ].
        unfold Single_sound in IHcomdB1.
        specialize (IHcomdB1 _ _ _ H10 H9).
        destruct IHcomdB1 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. right.
        apply in_app_iff. left. auto.
      * destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H5 H7).
        destruct H3 as [Mid_asrt [? ?] ].
        specialize (IHcomd2 _ (H1 _ H3)).
        destruct IHcomd2 as [_ [IHcomdB2 _] ].
        unfold Single_sound in IHcomdB2.
        specialize (IHcomdB2 _ _ _ H10 H9).
        destruct IHcomdB2 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
    + destruct H7 as [ [Mid_st [? ?] ] | [Mid_st [? ?] ] ].
      * destruct H2 as [? _].
        unfold Single_sound in H2. simpl in H2.
        specialize (H2 _ _ _ H5 H7).
        destruct H2 as [Mid_asrt [? ?] ].
        specialize (IHcomd1 _ (H _ H2)).
        destruct IHcomd1 as [_ [_ [IHcomdC1 _] ] ].
        unfold Single_sound in IHcomdC1.
        specialize (IHcomdC1 _ _ _ H10 H9).
        destruct IHcomdC1 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. right.
        apply in_app_iff. left. auto.
      * destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H5 H7).
        destruct H3 as [Mid_asrt [? ?] ].
        specialize (IHcomd2 _ (H1 _ H3)).
        destruct IHcomd2 as [_ [_ [IHcomdC2 _] ] ].
        unfold Single_sound in IHcomdC2.
        specialize (IHcomdC2 _ _ _ H10 H9).
        destruct IHcomdC2 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
    + destruct H7 as [ [Mid_st [? ?] ] | [Mid_st [? ?] ] ].
      * destruct H2 as [? _].
        unfold Single_sound in H2. simpl in H2.
        specialize (H2 _ _ _ H5 H7).
        destruct H2 as [Mid_asrt [? ?] ].
        specialize (IHcomd1 _ (H _ H2)).
        destruct IHcomd1 as [_ [_ [_ IHcomdR1] ] ].
        unfold Single_sound in IHcomdR1.
        specialize (IHcomdR1 _ _ _ H10 H9).
        destruct IHcomdR1 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. right.
        apply in_app_iff. left. auto.
      * destruct H3 as [? _].
        unfold Single_sound in H3. simpl in H3.
        specialize (H3 _ _ _ H5 H7).
        destruct H3 as [Mid_asrt [? ?] ].
        specialize (IHcomd2 _ (H1 _ H3)).
        destruct IHcomd2 as [_ [_ [_ IHcomdR2] ] ].
        unfold Single_sound in IHcomdR2.
        specialize (IHcomdR2 _ _ _ H10 H9).
        destruct IHcomdR2 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
  - (* C_while *)
    inv H.
    generalize dependent pre.
    apply (State_valid_conseq_pre _ _ _ _ _ _ H3). intros.
    unfold Cwhile_denote.
    eapply exec_res_sound_loop; eauto.
  - (* C_dowhile *)
    inv H.
    generalize dependent pre.
    apply (State_valid_conseq_pre _ _ _ _ _ _ H3). intros.
    eapply exec_res_sound_dowhile; eauto.
  - (* C_for *)
    inv H.
    unfold Cfor_denote.
    pose proof (SimpleCommand_exec_list_sound env callees return_val
                 Safety_checker _ _ _ H5 _ H0).
    destruct H as [init_res' [_ [? ?] ] ].
    eapply State_valid_seq; eauto.
    2:{ simpl. apply sublist_nil. }
    2:{ simpl. apply sublist_nil. }
    2:{ simpl. apply sublist_nil. }
    intros. simpl in *.
    generalize dependent pre0.
    assert (entail init_res' inv).
    { clear - H H6. unfold entail in *. intros.
      specialize (H6 _ (H _ H0)). auto. }
    apply (State_valid_conseq_pre _ _ _ _ _ _ H2). intros.
    eapply exec_res_sound_loop; eauto.
  - (* C_break *)
    inv H.
    unfold Cbreak_denote, State_valid, Single_sound, Single_ret_sound.
    simpl. repeat split; intros; try contradiction.
    inv H1. exists pre. split; auto.
    apply in_app_iff. left. auto.
  - (* C_continue *)
    inv H.
    unfold Ccont_denote, State_valid, Single_sound, Single_ret_sound.
    simpl. repeat split; intros; try contradiction.
    inv H1. exists pre. split; auto.
    apply in_app_iff. left. auto.
  - (* C_switch *)
    inv H0.
    replace labels with (labels ++ nil) in H5 by (rewrite app_nil_r; auto).
    unfold Cswitch_denote. simpl.
    destruct (Ccase_denote env callees
                (Cstatement_denote env callees return_val) c l
                (Cstatement_denote env callees return_val comd)) as [ [falth' body'] res'] eqn:?.
    pose proof (exec_res_sound_cases_falth _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 Heqp).
    destruct H0.
    change fst with (fun a : Cexpr * Cstatement => fst a) in H0. rewrite H0.
    simpl.
    specialize (IHcomd _ _ H9). simpl in IHcomd.
    assert (forall pre, In pre (Normal_ret Post1) ->
            State_valid env return_val pre Post2
            (Cstatement_denote env callees return_val comd)).
    { intros. apply IHcomd. apply in_app_iff. right. auto. }
    pose proof (exec_res_sublist _ _ _ H9). simpl in H4.
    pose proof (exec_res_sound_cases_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  H H5 Heqp H3 H4 _ H1).
    pose proof (Switch_Default_exec_list_sound env callees return_val _ _ _ _ _ _
                  H7 H0 _ H1).
    unfold State_valid, Single_sound, Single_ret_sound. simpl.
    repeat split; intros.
    + destruct H11 as [ [ [ [Mid_st [Hfl Hcomd] ] | Hres] | [Mid_st [Hfl Hcomd] ] ] | Hres].
      * specialize (H2 _ _ Hfl).
        destruct H8 as [? _]. simpl in H8.
        unfold Single_sound in H8.
        specialize (H8 _ _ _ H10 H2).
        destruct H8 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (res ++ Normal_ret Post1)).
        { apply in_app_iff. left. auto. }
        specialize (IHcomd _ H12).
        destruct IHcomd as [IHcomd _].
        unfold Single_sound in IHcomd.
        specialize (IHcomd _ _ _ H11 Hcomd).
        destruct IHcomd as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
      * destruct H6 as [? _].
        unfold Single_sound in H6.
        specialize (H6 _ _ _ H10 Hres).
        destruct H6 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
      * specialize (H2 _ _ Hfl).
        destruct H8 as [? _]. simpl in H8.
        unfold Single_sound in H8.
        specialize (H8 _ _ _ H10 H2).
        destruct H8 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (res ++ Normal_ret Post1)).
        { apply in_app_iff. left. auto. }
        specialize (IHcomd _ H12).
        destruct IHcomd as [_ [IHcomd _] ].
        unfold Single_sound in IHcomd.
        specialize (IHcomd _ _ _ H11 Hcomd).
        destruct IHcomd as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. right. auto.
      * destruct H6 as [_ [? _] ].
        unfold Single_sound in H6.
        specialize (H6 _ _ _ H10 Hres).
        destruct H6 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. right. auto.
    + contradiction.
    + destruct H11 as [ [Mid_st [Hfl Hcomd] ] | Hres].
      * specialize (H2 _ _ Hfl).
        destruct H8 as [? _]. simpl in H8.
        unfold Single_sound in H8.
        specialize (H8 _ _ _ H10 H2).
        destruct H8 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (res ++ Normal_ret Post1)).
        { apply in_app_iff. left. auto. }
        specialize (IHcomd _ H12).
        destruct IHcomd as [_ [_ [IHcomd _] ] ].
        unfold Single_sound in IHcomd.
        specialize (IHcomd _ _ _ H11 Hcomd).
        destruct IHcomd as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
      * destruct H6 as [_ [_ [? _] ] ].
        unfold Single_sound in H6.
        specialize (H6 _ _ _ H10 Hres).
        destruct H6 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
    + destruct H11 as [ [Mid_st [Hfl Hcomd] ] | Hres].
      * specialize (H2 _ _ Hfl).
        destruct H8 as [? _]. simpl in H8.
        unfold Single_sound in H8.
        specialize (H8 _ _ _ H10 H2).
        destruct H8 as [Mid_asrt1 [? ?] ].
        assert (In Mid_asrt1 (res ++ Normal_ret Post1)).
        { apply in_app_iff. left. auto. }
        specialize (IHcomd _ H12).
        destruct IHcomd as [_ [_ [_ IHcomd] ] ].
        unfold Single_sound in IHcomd.
        specialize (IHcomd _ _ _ H11 Hcomd).
        destruct IHcomd as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
      * destruct H6 as [_ [_ [_ ?] ] ].
        unfold Single_sound in H6.
        specialize (H6 _ _ _ H10 Hres).
        destruct H6 as [Post_asrt [? ?] ].
        exists Post_asrt. split; auto.
        apply in_app_iff. left. auto.
  - (* C_return *)
    inv H.
    pose proof (Return_exec_list_sound env callees return_val
                  Safety_checker _ _ _ H2 _ H0).
    destruct H as [Post' [_ [? ?] ] ].
    apply (State_valid_conseq_post _ _ _ _ _ _ H1); simpl;
      try apply sublist_nil.
    unfold sublist. intros.
    apply in_app_iff. left. auto.
  - (* C_assert *)
    inv H.
    unfold Ccont_denote, State_valid, Single_sound, Single_ret_sound.
    simpl. repeat split; intros; try contradiction.
    inv H1. apply (H2 _ H0 _ _ _ H).
  - (* C_inv *)
    inv H.
    unfold Ccont_denote, State_valid, Single_sound, Single_ret_sound.
    simpl. repeat split; intros; try contradiction.
    inv H1. exists pre. split; auto.
Qed. *)

End Safety_And_Entailment_Checkers.


Theorem StateMachine_sound :
  forall env callees return_val Safety_checker entailment_checker entailment_checker_with_ret
  comd ps env_s env_e state_t Pre Post,
    Stmt_to_ps comd = Some ps ->
    Sound_safety_checker Safety_checker ->
    Sound_entailment_checker entailment_checker ->
    Sound_entailment_checker_with_ret entailment_checker_with_ret ->
    Machine_exec Safety_checker entailment_checker entailment_checker_with_ret env_s Pre ps = Some (state_t , Post , env_e) ->
    State_valid env return_val Pre Post (Cstatement_denote env callees return_val comd).
Proof.
  unfold Machine_exec.
  intros * HPS HSC HEC HECR HEX. unfold Insert_stack in HEX.
  pose proof (StateMachine_Start_result Safety_checker entailment_checker entailment_checker_with_ret HSC HEC HECR _ _ HPS).
  edestruct H as [_ HER]; eauto.
  { unfold state_stack_match. left. repeat split; eauto. }
  clear - HSC HEC HECR HEX HER.
  assert (HIn : In Pre (Pre :: nil)) by (left; auto).
  eapply exec_res_sound ; eauto.
Qed.
