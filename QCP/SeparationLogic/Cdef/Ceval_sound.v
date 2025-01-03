From SimpleC.ASRT Require Import DefFiles.
From SimpleC.CSE Require Import Cexpr_def Cstate_def Cexpr_val_helper Cexpr_eval Cexpr_semantics.
From compcert.lib Require Import Coqlib Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.

Local Open Scope sets_scope.

Section Assertion_sem.

Variable env : prog_env.
Variable callees: val -> prog_state -> list val -> prog_state -> val -> Prop.
Variable return_val : int64.

Definition var_assignment: Type := ident -> int64.

Definition Uop_denote (op : unary_operation) (x : option int64) : option int64 := 
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
    | Some a , Some b => match op with 
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
  end.

Fixpoint expr_val_denote (J : var_assignment) (x : expr_val) : option int64 :=
  match x with 
    | EConstZ z => Some (Int64.repr z) 
    | EVar id => Some (J id) 
    | Vuop op a => Uop_denote op (expr_val_denote J a)
    | Vbop op a b => Binop_denote op (expr_val_denote J a) (expr_val_denote J b)
    | EField v id1 id2 => match expr_val_denote J v with 
                               | None => None 
                               | Some v0 => struct_pos env v0 id2
                             end 
    | EFunc _ _ => None (* TODO: *)
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

Definition Unary_expr_denote (op : Unary_expr_op) (e : option int64) : Prop :=
  match op with 
    | Pis_pointer_or_null => e <> None  
    | Pisptr => e <> None /\ e <> Some (Int64.repr 0)
  end.

Definition Binary_expr_denote (op : Binary_expr_op) (e1 e2 : option int64) : Prop :=
  match e1 , e2 with 
    | Some v1 , Some v2 => match op with 
                             | Pvle => Int64.cmp Cle v1 v2 = true 
                             | Pvge => Int64.cmp Cge v1 v2 = true  
                             | Pvlt => Int64.cmp Clt v1 v2 = true 
                             | Pvgt => Int64.cmp Cgt v1 v2 = true 
                             | Pvequal => Int64.cmp Ceq v1 v2 = true 
                           end 
    | _ , _ => False
  end.

Fixpoint Prop_denote (J : var_assignment) (x : Proposition) : Prop :=
  match x with 
    | TT => True 
    | FF => False 
    | Up op p => Unary_prop_denote op (Prop_denote J p)
    | Bp op p1 p2 => Binary_prop_denote op (Prop_denote J p1) (Prop_denote J p2)
    | Ue op e => Unary_expr_denote op (expr_val_denote J e)
    | Be op e1 e2 => Binary_expr_denote op (expr_val_denote J e1) (expr_val_denote J e2)
    | Qf _ _ _ => False  (* TODO: *)
  end.


Definition Local_denote (J : var_assignment) (st : prog_state) (x : local) : Prop :=
  match x with 
    | Avar id v => 
    exists addr, eval_id_addr ((vars_addr st) :: nil) (fst id) = Some addr
  end.
  
Definition mem_join (m1 m2 m: int64 -> mem_var): Prop :=
  forall i,
    (m1 i = Noperm /\ m2 i = Noperm /\ m i = Noperm) \/
    (m1 i = Noperm /\ m2 i = Noninit /\ m i = Noninit) \/
    (m1 i = Noninit /\ m2 i = Noperm /\ m i = Noninit) \/
    (exists i', m1 i = Noperm /\ m2 i = value i' /\ m i = value i') \/
    (exists i', m1 i = value i' /\ m2 i = Noperm /\ m i = value i').

Definition Sep_denote (J : var_assignment) (st : prog_state) (x : Separation) : Prop :=
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
    | _ => False (* TODO: *)
  end.
  
Definition Assertion_denote (J : var_assignment) (st : prog_state) (asrt : assertion) : Prop := 
  fold_left and (map (fun a => Prop_denote J a) asrt.(Prop_list)) True /\ 
  fold_left and (map (fun a => Local_denote J st a) asrt.(Local_list)) True /\ 
  fold_left and (map (fun a => Sep_denote J st a) asrt.(Sep_list)) True.

Definition Correct_denote (v : val) (x : option int64) : Prop :=
  exists n , x = Some (Int64.repr n) /\ const_denote n (type_of_val v) v.

Definition Post_denote (J : var_assignment) (st : prog_state) (v : val) (asrts : list (expr_val * assertion)) : Prop :=
  exists v0 asrt, In (v0 , asrt) asrts /\ 
    Correct_denote v (expr_val_denote J v0) /\ 
    Assertion_denote J st asrt.
End Assertion_sem.


Definition Single_sound (env : prog_env) (Pre : assertion) (Post : Assertion) (sem : prog_state -> prog_state -> Prop) : Prop :=
  forall Pre_st J Post_st, 
    Assertion_denote env J Pre_st Pre -> 
    sem Pre_st Post_st ->
    exists Post_asrt, In Post_asrt Post /\ Assertion_denote env J Post_st Post_asrt.  

Definition Single_ret_sound (env : prog_env) (return_val : int64) (Pre : assertion) (Post : list Prod_ret) (sem : prog_state -> prog_state -> Prop) : Prop := True.
(* TODO: *)
(*
  forall Pre_st J Post_st, 
    Assertion_denote env J Pre_st Pre -> 
    sem Pre_st Post_st ->
    exists Post_asrt, In Post_asrt Post /\ Assertion_denote env J Post_st (Union_assert Post_asrt.(Assert_r)) /\ (
    (exists v t v1, Post_asrt.(Return) = Some v /\ 
                  Merge_mem return_val t Post_st = Some v1 /\ 
                  Correct_denote v1 (expr_val_denote env J v))  \/ (forall t,
                 Merge_mem return_val t Post_st = None /\ Post_asrt.(Return) = None))
. *)

Definition Sound_entailment_checker (entailment_checker : Assertion -> Assertion -> option bool) := 
  forall Pre Post, entailment_checker Pre Post = Some true -> 
    forall v , In v Pre -> 
      forall env J st, Assertion_denote env J st v -> 
      exists m , In m Post /\ Assertion_denote env J st m 
  .

Definition Sound_entailment_checker_with_ret (entailment_checker_with_ret : list Prod_ret -> list Prod_ret -> option bool) := 
  forall Pre Post, entailment_checker_with_ret Pre Post = Some true ->
    forall v, In v Pre -> 
      forall env J st, 
        Assertion_denote env J st (v.(Assert_r)) -> 
        exists m , In m Post /\ Assertion_denote env J st (m.(Assert_r)) /\ 
        (v.(Return) = None -> m.(Return) = None) /\ 
        (exists p1, v.(Return) = Some p1 -> 
            exists p2, m.(Return) = Some p2 /\ expr_val_denote env J p1 = expr_val_denote env J p2).  

Definition Sound_safety_checker (Safety_checker : assertion -> list Proposition -> option bool) :=
  forall Pre P, Safety_checker Pre P = Some true -> 
    (forall env J Pre_st , Assertion_denote env J Pre_st Pre -> 
                           fold_left and (map (fun a => Prop_denote env J a) P) True).

(** This lemma you can use directly *)
(*
Lemma FOLD_LEFT_INIT:
forall l p,
fold_left and l p ->
p.
Proof.
induction l; intros; simpl in *.
-tauto. 
- specialize (IHl (p /\ a)).
  pose proof IHl H.
  tauto.
Qed.

Lemma subgoal: 
forall l (a:Prop) (b:Prop), (a->b) -> (fold_left and l a -> fold_left and l b).
Proof.
  induction l as[| l0 l'].
  intros.
  simpl in H0 |-*.
  specialize (H H0).
  tauto.
  intros.
  simpl in H0 |-*.
  specialize (IHl' (a /\ l0) (b /\ l0)).
  assert (forall l1 a1 b1:Prop, (a1 -> b1)->((a1/\l1) -> (b1/\l1))).
  {
    intros.
    destruct H2.
    specialize (H1 H2).
    tauto.
  }
  specialize (H1 l0 a b H).
  specialize (IHl' H1 H0).
  tauto.
Qed.
Lemma FOLD_LEFT_TRUE:
forall l p,
fold_left and l p ->
fold_left and l True.
Proof.
  intros.
  assert ( p -> True ).
  { tauto. }
  pose proof (subgoal l p True H0 H).
  tauto.
Qed.
Lemma FOLD_LEFT_PROOF_INIT:
forall (l:list Prop) (p:Prop),
fold_left and l True ->
p->
fold_left and l p.
Proof.
  intros.
  assert (True -> p).
  { tauto. }
  pose proof (subgoal l True p H1 H).
  tauto.
Qed.

Lemma Sep_denote_eq_state:
forall Pre_st Post_st env J a,
state_eq Pre_st Post_st ->
Sep_denote env J Pre_st a ->
Sep_denote env J Post_st a.
Proof.
   intros.
   destruct a; simpl in *.
   destruct e; simpl in *.
   - destruct e0; simpl in *; try tauto.
   destruct o; simpl in *; try tauto.
   destruct (expr_val_denote env J e0); try tauto.
   destruct H0 as [?[?[?[??]]]].
   exists x.
   split;[tauto|].
   split;[tauto|].
   split;[tauto|].
   unfold state_eq in H.
   destruct H.
   specialize (H4 i).
   unfold eqb_mem_var in H4.
   rewrite H3 in H4.
   destruct (mem Post_st i).
   + discriminate.
   + reflexivity.
   + discriminate.
   -  destruct (expr_val_denote env J e0); simpl in *; [|tauto].
      destruct H0 as [?[?[?[?[?[?[?[??]]]]]]]].
      exists x, x0, x1.
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[|tauto].
      unfold state_eq in H. destruct H.
      rewrite H4.
      pose proof (H6 i).
      unfold eqb_mem_var in H7.
      destruct (mem Pre_st i)eqn:?; simpl in *; try tauto;
      destruct (mem Post_st i)eqn:?; simpl in *; try tauto; try discriminate.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + apply Byte.same_if_eq in H7.
         destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; rewrite H7; try tauto.
         * pose proof (H6 (Int64.add i (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10.
            rewrite H8,H9,H10.
            tauto.
         * pose proof (H6 (Int64.add i (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10.
            rewrite H8,H9,H10.
            tauto.
         * pose proof (H6         ((Int64.add i (Int64.repr 1)))). unfold eqb_mem_var in H8.
            destruct (mem Pre_st   ((Int64.add i (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add i (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 ((Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st ((Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 ((Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))).
            unfold eqb_mem_var in H11.
            destruct (mem Pre_st ((Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 ((Int64.add
            (Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1)))).
            unfold eqb_mem_var in H12.
            destruct (mem Pre_st ((Int64.add
            (Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
            (Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H13.
            destruct (mem Pre_st   ((Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
            destruct (mem Pre_st   ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
            rewrite H8,H9,H10,H11, H12, H13, H14.
            tauto.
         * pose proof (H6         ((Int64.add i (Int64.repr 1)))). unfold eqb_mem_var in H8.
            destruct (mem Pre_st   ((Int64.add i (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add i (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H9.
            destruct (mem Pre_st   ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H10.
            destruct (mem Pre_st   ((Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H11.
            destruct (mem Pre_st   ((Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
            destruct (mem Pre_st   ((Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H13.
            destruct (mem Pre_st   ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
            destruct (mem Pre_st   ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
            rewrite H8,H9,H10,H11, H12, H13, H14.
            tauto.
   - destruct (expr_val_denote env J e0); simpl in *; [|tauto].
      destruct H0 as [?[?[?[?[?[?[?[??]]]]]]]].
      exists x, x0, x1.
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[|tauto].
      unfold state_eq in H. destruct H.
      rewrite H4.
      pose proof (H6 i0).
      unfold eqb_mem_var in H7.
      destruct (mem Pre_st i0)eqn:?; simpl in *; try tauto;
      destruct (mem Post_st i0)eqn:?; simpl in *; try tauto; try discriminate.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + unfold Byte.eq in H7.
         destruct ( zeq (Byte.unsigned i1) (Byte.unsigned i2)); simpl in *; [|discriminate].
         destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; rewrite e; try tauto.
         * pose proof (H6 (Int64.add i0 (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            unfold Byte.eq in H8.
            destruct (zeq (Byte.unsigned i3) (Byte.unsigned i4))eqn:?; simpl in *; try discriminate.
            unfold Byte.eq in H9.
            destruct (zeq (Byte.unsigned i5) (Byte.unsigned i6))eqn:?; simpl in *; try discriminate.
            unfold Byte.eq in H10.
            destruct (zeq (Byte.unsigned i7) (Byte.unsigned i8))eqn:?; simpl in *; try discriminate.
            rewrite e1, e2, e3.
            tauto.
         * pose proof (H6 (Int64.add i0 (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            unfold Byte.eq in H8.
            destruct (zeq (Byte.unsigned i3) (Byte.unsigned i4))eqn:?; simpl in *; try discriminate.
            unfold Byte.eq in H9.
            destruct (zeq (Byte.unsigned i5) (Byte.unsigned i6))eqn:?; simpl in *; try discriminate.
            unfold Byte.eq in H10.
            destruct (zeq (Byte.unsigned i7) (Byte.unsigned i8))eqn:?; simpl in *; try discriminate.
            rewrite e1, e2, e3.
            tauto.
         * pose proof (H6         (Int64.add i0 (Int64.repr 1))). unfold eqb_mem_var in H8.
            destruct (mem Pre_st   (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
            destruct (mem Pre_st   ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
            destruct (mem Pre_st   ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H13.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
            rewrite H8,H9,H10,H11, H12, H13, H14.
            tauto.
         * pose proof (H6         (Int64.add i0 (Int64.repr 1))). unfold eqb_mem_var in H8.
            destruct (mem Pre_st   (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
            destruct (mem Pre_st   ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
            destruct (mem Pre_st   ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H13.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
            rewrite H8,H9,H10,H11, H12, H13, H14.
            tauto.
   - destruct (expr_val_denote env J e0); try tauto.
      destruct (expr_val_denote env J e); try tauto.
      destruct (struct_pos env i1 i); try tauto.
      destruct H0 as [?[?[?[?[?[?[?[??]]]]]]]].
      exists x, x0, x1.
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[|tauto].
      rewrite H4.
      unfold state_eq in H. destruct H.
      pose proof (H6 i0).
      unfold eqb_mem_var in H7.
      destruct (mem Pre_st i0)eqn:?; simpl in *; try tauto;
      destruct (mem Post_st i0)eqn:?; simpl in *; try tauto; try discriminate.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + apply Byte.same_if_eq in H7.
         destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; rewrite H7; try tauto.
         * pose proof (H6 (Int64.add i0 (Int64.repr 1))).
         unfold eqb_mem_var in H8.
         destruct (mem Pre_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
         unfold eqb_mem_var in H9.
         destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1))).
         unfold eqb_mem_var in H8.
         destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         apply Byte.same_if_eq in H8, H9, H10.
         rewrite H8,H9,H10.
         tauto.
      * pose proof (H6 (Int64.add i0 (Int64.repr 1))).
         unfold eqb_mem_var in H8.
         destruct (mem Pre_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
         unfold eqb_mem_var in H9.
         destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1))).
         unfold eqb_mem_var in H8.
         destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         apply Byte.same_if_eq in H8, H9, H10.
         rewrite H8,H9,H10.
         tauto.
      * pose proof (H6         (Int64.add i0 (Int64.repr 1))). unfold eqb_mem_var in H8.
         destruct (mem Pre_st   (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
         unfold eqb_mem_var in H9.
         destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1))).
         unfold eqb_mem_var in H10.
         destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
         destruct (mem Pre_st   ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
         destruct (mem Pre_st   ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))). unfold eqb_mem_var in H13.
         destruct (mem Pre_st   (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
         destruct (mem Pre_st   (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
         rewrite H8,H9,H10,H11, H12, H13, H14.
         tauto.
      * pose proof (H6         (Int64.add i0 (Int64.repr 1))). unfold eqb_mem_var in H8.
         destruct (mem Pre_st   (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
         unfold eqb_mem_var in H9.
         destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1))).
         unfold eqb_mem_var in H10.
         destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
         destruct (mem Pre_st   ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
         destruct (mem Pre_st   ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))). unfold eqb_mem_var in H13.
         destruct (mem Pre_st   (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
         destruct (mem Pre_st   (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
         rewrite H8,H9,H10,H11, H12, H13, H14.
         tauto.
   - destruct (expr_val_denote env J e); simpl in *; try tauto; try discriminate.
      destruct o; simpl in *; try tauto; try discriminate.
      destruct (union_pos env i i0); simpl in *; try tauto; try discriminate.
      destruct (expr_val_denote env J e0); simpl in *; try tauto; try discriminate.
      destruct H0 as [?[?[?[?[?[?[?[??]]]]]]]].
      exists x, x0, x1.
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[|tauto].
      rewrite H4.
      unfold state_eq in H.
      destruct H.
      pose proof (H6 i2).
      unfold eqb_mem_var in H7.
      destruct (mem Pre_st i2)eqn:?; simpl in *; try tauto;
      destruct (mem Post_st i2)eqn:?; simpl in *; try tauto; try discriminate.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + apply Byte.same_if_eq in H7.
         destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; rewrite H7; try tauto.
         * pose proof (H6 (Int64.add i2 (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i2 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i2 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10.
            rewrite H8,H9,H10.
            tauto.
         * pose proof (H6 (Int64.add i2 (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i2 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i2 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10.
            rewrite H8,H9,H10.
            tauto.
         * pose proof (H6         (Int64.add i2 (Int64.repr 1))). unfold eqb_mem_var in H8.
            destruct (mem Pre_st   (Int64.add i2 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i2 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
            (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
            destruct (mem Pre_st   ((Int64.add
            (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
            (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
            destruct (mem Pre_st   ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H13.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
            rewrite H8,H9,H10,H11, H12, H13, H14.
            tauto.
         * pose proof (H6         (Int64.add i2 (Int64.repr 1))). unfold eqb_mem_var in H8.
            destruct (mem Pre_st   (Int64.add i2 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i2 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
            (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
            destruct (mem Pre_st   ((Int64.add
            (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
            (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
            destruct (mem Pre_st   ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H13.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i2 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
            rewrite H8,H9,H10,H11, H12, H13, H14.
            tauto.
   -destruct (Uop_denote u (expr_val_denote env J e)); simpl in *; try tauto; try discriminate.
      destruct (expr_val_denote env J e0); simpl in *; try tauto; try discriminate.
      destruct H0 as [?[?[?[?[?[?[?[??]]]]]]]].
      exists x, x0, x1.
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[|tauto].
      rewrite H4.
      unfold state_eq in H.
      destruct H.
      pose proof (H6 i0).
      unfold eqb_mem_var in H7.
      destruct (mem Pre_st i0)eqn:?; simpl in *; try tauto;
      destruct (mem Post_st i0)eqn:?; simpl in *; try tauto; try discriminate.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + apply Byte.same_if_eq in H7.
         destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; rewrite H7; try tauto.
         * pose proof (H6 (Int64.add i0 (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10.
            rewrite H8,H9,H10.
            tauto.
         * pose proof (H6 (Int64.add i0 (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10.
            rewrite H8,H9,H10.
            tauto.
         * pose proof (H6         (Int64.add i0 (Int64.repr 1))). unfold eqb_mem_var in H8.
            destruct (mem Pre_st   (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
            destruct (mem Pre_st   ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
            destruct (mem Pre_st   ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H13.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
            rewrite H8,H9,H10,H11, H12, H13, H14.
            tauto.
         * pose proof (H6         (Int64.add i0 (Int64.repr 1))). unfold eqb_mem_var in H8.
            destruct (mem Pre_st   (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H10.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
            destruct (mem Pre_st   ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ((Int64.add
            (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
            destruct (mem Pre_st   ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st ( (Int64.add
               (Int64.add
                  (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1)))). unfold eqb_mem_var in H13.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
               (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6         (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
            destruct (mem Pre_st   (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (      (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add
                           (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                           (Int64.repr 1)) (Int64.repr 1)) 
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
            rewrite H8,H9,H10,H11, H12, H13, H14.
            tauto.
   - destruct (Binop_denote b (expr_val_denote env J e1) (expr_val_denote env J e2)); simpl in *; try tauto; try discriminate.
      destruct (expr_val_denote env J e0); simpl in *; try tauto; try discriminate.
      destruct H0 as [?[?[?[?[?[?[?[??]]]]]]]].
      exists x, x0, x1.
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[tauto|].
      split;[|tauto].
      rewrite H4.
      unfold state_eq in H.
      destruct H.
      pose proof (H6 i0).
      unfold eqb_mem_var in H7.
      destruct (mem Pre_st i0)eqn:?; simpl in *; try tauto;
      destruct (mem Post_st i0)eqn:?; simpl in *; try tauto; try discriminate.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; tauto.
      + apply Byte.same_if_eq in H7.
         destruct s; simpl in *; try tauto; destruct s; simpl in *; try tauto; rewrite Heqm; rewrite Heqm0; rewrite H7; try tauto.
         * pose proof (H6 (Int64.add i0 (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
            unfold eqb_mem_var in H9.
            destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))).
            unfold eqb_mem_var in H8.
            destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto;
            destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
            apply Byte.same_if_eq in H8, H9, H10.
            rewrite H8,H9,H10.
            tauto.
      * pose proof (H6 (Int64.add i0 (Int64.repr 1))).
         unfold eqb_mem_var in H8.
         destruct (mem Pre_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
         unfold eqb_mem_var in H9.
         destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1))).
         unfold eqb_mem_var in H8.
         destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         apply Byte.same_if_eq in H8, H9, H10.
         rewrite H8,H9,H10.
         tauto.
      * pose proof (H6         (Int64.add i0 (Int64.repr 1))). unfold eqb_mem_var in H8.
         destruct (mem Pre_st   (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
         unfold eqb_mem_var in H9.
         destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1))).
         unfold eqb_mem_var in H10.
         destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
         destruct (mem Pre_st   ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
         destruct (mem Pre_st   ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))). unfold eqb_mem_var in H13.
         destruct (mem Pre_st   (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
         destruct (mem Pre_st   (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
         rewrite H8,H9,H10,H11, H12, H13, H14.
         tauto.
      * pose proof (H6         (Int64.add i0 (Int64.repr 1))). unfold eqb_mem_var in H8.
         destruct (mem Pre_st   (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add i0 (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))).
         unfold eqb_mem_var in H9.
         destruct (mem Pre_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct (mem Post_st (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6 (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1))).
         unfold eqb_mem_var in H10.
         destruct (mem Pre_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
         (Int64.repr 1)))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H11.
         destruct (mem Pre_st   ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st ((Int64.add
         (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H12.
         destruct (mem Pre_st   ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st ( (Int64.add
            (Int64.add
               (Int64.add (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1)))). unfold eqb_mem_var in H13.
         destruct (mem Pre_st   (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                     (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))
            (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         pose proof (H6         (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1)))). unfold eqb_mem_var in H14.
         destruct (mem Pre_st   (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto;
         destruct ( mem Post_st (      (Int64.add
            (Int64.add
               (Int64.add
                  (Int64.add
                     (Int64.add
                        (Int64.add (Int64.add i0 (Int64.repr 1)) (Int64.repr 1))
                        (Int64.repr 1)) (Int64.repr 1)) 
                  (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 1))))eqn:?; simpl in *; try tauto; try discriminate.
         apply Byte.same_if_eq in H8, H9, H10, H11, H12, H13, H14.
         rewrite H8,H9,H10,H11, H12, H13, H14.
         tauto.
Qed.

Lemma eq_state:
forall env J Pre_st Post_st Pre_asrt , state_eq Pre_st Post_st -> 
      Assertion_denote env J Pre_st Pre_asrt -> 
      Assertion_denote env J Post_st Pre_asrt.
Proof.
  intros.
  unfold Assertion_denote in H0 |-*.
  unfold Prod_asrt_denote in H0 |-*.
  destruct H0 as [H1 [H2 H3]].
  split.
  {
    tauto. 
  }
  {
    split.
    + clear H1 H3.
      unfold Local_denote in H2 |-*.
      unfold state_eq in H.
      assert (forall l b, (fold_left and
       (map
          (fun a : local =>
           match a with
           | temp id v =>
               Some (vars_addr Pre_st id) =
               expr_val_denote env J v
           end) l) b) -> (fold_left and
       (map
          (fun a : local =>
           match a with
           | temp id v =>
               Some (vars_addr Post_st id) =
               expr_val_denote env J v
           end) l) b)).
      {
        induction l;intros.
        - simpl in H0 |-*.
          tauto.
        - simpl in H0 |-*.
          destruct a.
          destruct H.
          specialize (H i).
          pose proof Int64.same_if_eq (vars_addr Pre_st i) (vars_addr Post_st i) H.
          rewrite H3 in H0.
          specialize (IHl (b /\ Some (vars_addr Post_st i) = expr_val_denote env J e) H0).
          tauto.
      } 
      specialize (H0 (Local_list (Split_assert Pre_asrt)) True H2).
      tauto.
    + clear H1 H2.
      set (l:=(Sep_list (Split_assert Pre_asrt))) in *.
      clearbody l.
      induction l; simpl in *; [tauto|].
      pose proof FOLD_LEFT_INIT (map (fun a : Separation => Sep_denote env J Pre_st a) l)
      (True /\ Sep_denote env J Pre_st a) H3.
      destruct H0. clear H0.
      apply FOLD_LEFT_TRUE in H3.
      pose proof IHl H3.
      assert (Sep_denote env J Post_st a). { 
        pose proof Sep_denote_eq_state Pre_st Post_st env J a H H1.
        tauto.
      }
      assert (True/\ Sep_denote env J Post_st a). { tauto. }
      apply FOLD_LEFT_PROOF_INIT;tauto. 
  }
Qed.      

Lemma ADMITTED:
(forall env J Pre_st Pre_asrt i e e0 CType v,Assertion_denote env J Pre_st Pre_asrt ->eval_tmpval 
(Local_list (Split_assert Pre_asrt)) i = Some e ->eval_val (Sep_list (Split_assert Pre_asrt)) e = Some e0 ->
var_denote i CType Pre_st v ->exists n : Z,expr_val_denote env J e0 = Some (Int64.repr n) /\ const_denote n
(type_of_val v) v)/\(forall Post_asrts: list (expr_val * assertion),Option_move (None :: nil) = Some Post_asrts)/\(forall (env: prog_env)
(callees: val -> prog_state -> list val -> prog_state -> val -> Prop)(Pre_asrt: assertion)(Pre_st Post_st: prog_state)
(Post_asrts: list (expr_val * assertion))(safe_checker: assertion -> list Proposition -> option bool)(z CType: SimpleCtype)(v: val)(J: var_assignment),
(forall i : ident, Int64.eq (vars_addr Pre_st i) (vars_addr Post_st i) = true) ->(forall j : int64, eqb_mem_var (mem Pre_st j) (mem Post_st j) = true) ->
Assertion_denote env J Pre_st Pre_asrt ->Sound_safety_checker safe_checker ->Safe_eval safe_checker (C_sizeof z CType) Pre_asrt = Some Post_asrts ->
const_denote (Ctype_size z) CType v -> Post_denote env J Post_st v Post_asrts).
Proof.
Admitted.

Lemma SUBGOAL0:
forall Post_asrts: list (expr_val * assertion),
Option_move (None :: nil) = Some Post_asrts.
Proof.
   pose proof ADMITTED.
   destruct H as [?[??]]; try tauto; try discriminate.
Qed.

Lemma B2:
forall env J Pre_st Pre_asrt i e e0 CType v,
Assertion_denote env J Pre_st Pre_asrt ->
eval_tmpval (Local_list (Split_assert Pre_asrt)) i = Some e ->
eval_val (Sep_list (Split_assert Pre_asrt)) e = Some e0 ->
var_denote i CType Pre_st v ->
exists n : Z,
  expr_val_denote env J e0 = Some (Int64.repr n) /\ const_denote n (type_of_val v) v.
Proof.
   pose proof ADMITTED.
   destruct H as [?[??]]; try tauto; try discriminate.
Qed.

Lemma B3:
forall (env: prog_env)
(callees: val -> prog_state -> list val -> prog_state -> val -> Prop)
(Pre_asrt: assertion)
(Pre_st Post_st: prog_state)
(Post_asrts: list (expr_val * assertion))
(safe_checker: assertion -> list Proposition -> option bool)
(z CType: SimpleCtype)
(v: val)
(J: var_assignment),
(forall i : ident, Int64.eq (vars_addr Pre_st i) (vars_addr Post_st i) = true) ->
(forall j : int64, eqb_mem_var (mem Pre_st j) (mem Post_st j) = true) ->
Assertion_denote env J Pre_st Pre_asrt ->
Sound_safety_checker safe_checker ->
Safe_eval safe_checker (C_sizeof z CType) Pre_asrt = Some Post_asrts ->
const_denote (Ctype_size z) CType v -> Post_denote env J Post_st v Post_asrts.
Proof.
   pose proof ADMITTED.
   destruct H as [?[??]]; try tauto; try discriminate.
Qed. *)

(* Lemma eval_sound : 
  forall env callees Pre_asrt Pre_st Post_st Post_asrts safe_checker x v J,
    Assertion_denote env J Pre_st Pre_asrt -> 
    Sound_safety_checker safe_checker -> 
    Safe_eval safe_checker x Pre_asrt = Some Post_asrts ->
    eval_Cexprval_denote env callees x Pre_st v Post_st ->
    Post_denote env J Post_st v Post_asrts 
with eval_l_sound : 
  forall env callees Pre_asrt Pre_st Post_st Post_asrts safe_checker x v J,
    Assertion_denote env J Pre_st Pre_asrt ->
    Sound_safety_checker safe_checker ->  
    Safe_eval_l safe_checker x Pre_asrt = Some Post_asrts -> 
    eval_Cexprval_l_denote env callees x Pre_st v Post_st ->
    Post_denote env J Post_st (Vulong v) Post_asrts.
Proof.
Admitted. *)
(*
+ induction x as [z CType|i CType|z CType|z CType|z CType|z CType|z CType|z CType|z CType|CType1 CType2|e1 IHe1 e2 IHe2 CType|e IHe liste CType].
  - intros.
    unfold Safe_eval in H1.
    simpl in H1.
    destruct (safe_checker Pre_asrt (Safe_cond (EConstZ z) CType)) eqn:H4.
    2:{
      unfold Option_move in H1 .
      simpl in H1.
      discriminate.
    }
    destruct b.
      2:{
          unfold Option_move in H1 .
          simpl in H1.
          discriminate.
      }
      1:{
          unfold Option_move in H1 .
          simpl in H1.
          injection H1 as H1.
          unfold Post_denote.
          exists (EConstZ z), Pre_asrt.
          split.
          + unfold In.
            rewrite <-H1.
            tauto.
          + split.
            - unfold Correct_denote.
              exists z.
              split.
              {
                unfold expr_val_denote.
                tauto.
              }
              {
                assert (type_of_val v = CType).
                {
                  unfold eval_Cexprval_denote in H2.
                  destruct H2 as [H2 H3].
                  destruct CType in H2 |- *.
                  + simpl in H2.
                    tauto.
                  + simpl in H2.
                    destruct s.
                    - destruct H2 as [H2 [? ?]].
                      unfold type_of_val.
                      rewrite H2.
                      tauto.
                    - destruct H2 as [H2 [? ?]].
                      unfold type_of_val.
                      rewrite H2.
                      tauto.
                  + simpl in H2.
                    destruct s.
                    - destruct H2 as [H2 [? ?]].
                      unfold type_of_val.
                      rewrite H2.
                      tauto.
                    - destruct H2 as [H2 [? ?]].
                      unfold type_of_val.
                      rewrite H2.
                      tauto.
                  + simpl in H2.
                    destruct s.
                    - destruct H2 as [H2 [? ?]].
                      unfold type_of_val.
                      rewrite H2.
                      tauto.
                    - destruct H2 as [H2 [? ?]].
                      unfold type_of_val.
                      rewrite H2.
                      tauto.
                  + simpl in H2.
                    tauto.
                  + simpl in H2.
                    tauto.
                  + simpl in H2.
                    tauto.
                  + simpl in H2.
                    tauto.
                  + simpl in H2.
                    tauto.
                  + simpl in H2.
                    tauto.
                }
                unfold eval_Cexprval_denote in H2.
                destruct H2 as [H2 H5].
                rewrite H3.
                tauto.
              }
            - unfold eval_Cexprval_denote in H2.
              destruct H2 as [H2 H5].
              pose proof eq_state env J Pre_st Post_st Pre_asrt H5 H.
              tauto.
        }
  - clear eval_sound eval_l_sound.
    intros.
    unfold Safe_eval in H1.
    simpl in H1.
    destruct (eval_Ctmpval Pre_asrt i) eqn:H3.
    2:{ discriminate. }
    destruct (Option_move
         (map
            (fun a : expr_val * assertion =>
             match
               eval_val (Sep_list (Split_assert (snd a)))
                 (fst a)
             with
             | Some v => Some (v, nil, snd a)
             | None => None
             end) l)) eqn:H4.
    2:{ discriminate. }
    unfold eval_Ctmpval in H3.
    destruct (eval_tmpval (Local_list (Split_assert Pre_asrt)) i) eqn:H5.
    2:{ discriminate. }
    injection H3 as H3.
    rewrite <-H3 in H4.
    simpl in H4.
    destruct (eval_val (Sep_list (Split_assert Pre_asrt)) e) eqn:H7.
    2:{ 
      unfold Option_move in H4.
      simpl in H4.
      discriminate. 
    }
    unfold Option_move in H4.
    simpl in H4.
    injection H4 as H4.
    rewrite <-H4 in H1.
    simpl in H1.
    destruct (safe_checker Pre_asrt nil).
    2:{ discriminate. }
    destruct b.
    2:{ unfold Option_move in H1. simpl in H1. discriminate.  }
    unfold Option_move in H1.
    simpl in H1.
    injection H1 as H1.
    unfold Post_denote.
    exists e0, Pre_asrt.
    split.
    1:{
      unfold In.
      rewrite <-H1.
      tauto.
    }
    split.
    2:{
      unfold eval_Cexprval_denote in H2.
      destruct H2 as [H2 H6].
      pose proof eq_state env J Pre_st Post_st Pre_asrt H6 H.
      tauto.
    } 
    unfold Correct_denote.
    destruct H2 as [H2 H6].
    clear H4 l0 H3 l H6 Post_st H1 Post_asrts H0 safe_checker.
    pose proof B2 env J Pre_st Pre_asrt i e e0 CType v H H5 H7 H2.
    tauto.
  (* 3 *)
  - clear eval_sound eval_l_sound.
    intros; simpl in *.
    destruct H2 as [?[??]].
    unfold Post_denote.
    unfold Safe_eval in H1; simpl in *.
    destruct (eval_Cexprval z Pre_asrt); simpl in *; try discriminate.
    destruct (Option_move
    (map
       (fun a : expr_val * list Proposition * assertion =>
        match eval_val (Sep_list (Split_assert (snd a))) (fst (fst a)) with
        | Some v => Some (v, snd (fst a), snd a)
        | None => None
        end) l)) eqn:?; simpl in *; try tauto; try discriminate.
    unfold Option_move in Heqo.
    destruct (Find_None
    (map
       (fun a : expr_val * list Proposition * assertion =>
        match eval_val (Sep_list (Split_assert (snd a))) (fst (fst a)) with
        | Some v => Some (v, snd (fst a), snd a)
        | None => None
        end) l)) eqn:?; simpl in *; try tauto; try discriminate.
    injection Heqo as Heqo. 
    unfold Option_move in H1.
    destruct (Find_None
    (map
       (fun a : expr_val * list Proposition * assertion =>
        match safe_checker (snd a) (snd (fst a)) with
        | Some b => if b then Some (fst (fst a), snd a) else None
        | None => None
        end)
       (Clear_option
          (map
             (fun a : expr_val * list Proposition * assertion =>
              match eval_val (Sep_list (Split_assert (snd a))) (fst (fst a)) with
              | Some v => Some (v, snd (fst a), snd a)
              | None => None
              end) l)))) eqn:?; simpl in *; try discriminate; try tauto.
    destruct (Find_None
    (map
       (fun a : expr_val * list Proposition * assertion =>
        match safe_checker (snd a) (snd (fst a)) with
        | Some b => if b then Some (fst (fst a), snd a) else None
        | None => None
        end) l0)) eqn:?; simpl in *; try discriminate; try tauto.
    specialize (CType v J).
    pose proof CType H H0.
    assert (Safe_eval safe_checker z Pre_asrt = Some Post_asrts). {
      unfold Safe_eval.
      destruct (eval_Cexprval z Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
      - unfold Option_move; pose proof SUBGOAL0 Post_asrts.
         destruct (Find_None
         (map
            (fun a : expr_val * list Proposition * assertion =>
             match safe_checker (snd a) (snd (fst a)) with
             | Some b => if b then Some (fst (fst a), snd a) else None
             | None => None
             end) l1)) eqn:?; simpl in *; try tauto ; try discriminate.
      - pose proof SUBGOAL0 Post_asrts.
        discriminate.
    }
    pose proof CType H H0 H5.
    pose proof SUBGOAL0 Post_asrts.
    try tauto; try discriminate.
    pose proof SUBGOAL0 Post_asrts.
    try tauto; try discriminate.
   (* 4 *)
   - clear eval_sound eval_l_sound.
      intros; simpl in *.
      destruct H2 as [?[??]].
      assert (Safe_eval safe_checker z Pre_asrt = Some Post_asrts). {
         unfold Safe_eval.
         destruct (eval_Cexprval z Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate
         ;pose proof SUBGOAL0 Post_asrts.
         - unfold Option_move.
            destruct ((map
            (fun a : expr_val * list Proposition * assertion =>
             match safe_checker (snd a) (snd (fst a)) with
             | Some b => if b then Some (fst (fst a), snd a) else None
             | None => None
             end) l)) eqn:?; simpl in *; try tauto.
            + discriminate.
            + discriminate.
         - discriminate.
      }
      assert (eval_Cexprval_denote env callees z Pre_st v Post_st). {
         induction z; simpl in *; try tauto; try discriminate; pose proof SUBGOAL0 Post_asrts.
         - split; [discriminate|].
            tauto.
         - discriminate.
         - destruct H2 as [?[??]].
            destruct H6 as [?[?[?[??]]]].
            exists x0.
            split; try tauto.
            exists x.
            split; try tauto.
            split; try tauto.
            + discriminate.
            + exists x1.
               unfold Option_move in H5.
               simpl in H5.
               discriminate.
         - destruct H2 as [?[??]].
         destruct H6 as [?[?[?[??]]]].
         exists x0.
         split; try tauto.
         exists x.
         split; try tauto.
         split; try tauto.
         + discriminate.
         + exists x1.
            unfold Option_move in H5.
            simpl in H5.
            discriminate. 
      }
      specialize (CType v J).
      tauto.
   (* 5 *)
   - clear eval_sound eval_l_sound.
      intros; simpl in *.
      destruct H2 as [?[??]].
      assert (Safe_eval safe_checker CType Pre_asrt = Some Post_asrts). {
         unfold Safe_eval.
         destruct (eval_Cexprval CType Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
         - unfold Option_move. pose proof SUBGOAL0 nil.
            destruct (Find_None
            (map
               (fun a : expr_val * list Proposition * assertion =>
                match safe_checker (snd a) (snd (fst a)) with
                | Some b => if b then Some (fst (fst a), snd a) else None
                | None => None
                end) l)) eqn:?; simpl in *; try tauto; try discriminate.
         - pose proof SUBGOAL0 nil.
            discriminate.
      }
      assert (eval_Cexprval_denote env callees CType Pre_st v Post_st ). {
         pose proof SUBGOAL0 nil; discriminate.
      }
      specialize (IHCType v J).
      tauto.
   (* 6 *)
   - clear eval_sound eval_l_sound.
      intros; simpl in *.
      destruct H2 as [?[??]].
      assert (Safe_eval safe_checker CType Pre_asrt = Some Post_asrts). {
         unfold Safe_eval.
         destruct (eval_Cexprval CType Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
         - unfold Option_move. pose proof SUBGOAL0 nil.
            destruct (Find_None
            (map
               (fun a : expr_val * list Proposition * assertion =>
               match safe_checker (snd a) (snd (fst a)) with
               | Some b => if b then Some (fst (fst a), snd a) else None
               | None => None
               end) l)) eqn:?; simpl in *; try tauto; try discriminate.
         - pose proof SUBGOAL0 nil.
            discriminate.
      }
      assert (eval_Cexprval_denote env callees CType Pre_st v Post_st ). {
         pose proof SUBGOAL0 nil; discriminate.
      }
      specialize (IHCType v J).
      tauto.
   (* 7 *)
   - clear eval_sound eval_l_sound.
      intros; simpl in *.
      destruct H2 as [?[??]].
      assert (Safe_eval safe_checker z Pre_asrt = Some Post_asrts). {
         unfold Safe_eval.
         destruct (eval_Cexprval z Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
         - unfold Option_move. pose proof SUBGOAL0 nil.
            destruct (Find_None
            (map
               (fun a : expr_val * list Proposition * assertion =>
               match safe_checker (snd a) (snd (fst a)) with
               | Some b => if b then Some (fst (fst a), snd a) else None
               | None => None
               end) l)) eqn:?; simpl in *; try tauto; try discriminate.
         - pose proof SUBGOAL0 nil.
            discriminate.
      }
      assert (eval_Cexprval_denote env callees z Pre_st v Post_st ). {
         pose proof SUBGOAL0 nil; discriminate.
      }
      specialize (CType v J).
      tauto.
   (* 8 *)
   - clear eval_sound eval_l_sound.
      intros; simpl in *.
      destruct H2 as [?[??]].
      assert (Safe_eval safe_checker z Pre_asrt = Some Post_asrts). {
         unfold Safe_eval.
         destruct (eval_Cexprval z Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
         - unfold Option_move. pose proof SUBGOAL0 nil.
            destruct (Find_None
            (map
               (fun a : expr_val * list Proposition * assertion =>
               match safe_checker (snd a) (snd (fst a)) with
               | Some b => if b then Some (fst (fst a), snd a) else None
               | None => None
               end) l)) eqn:?; simpl in *; try tauto; try discriminate.
         - pose proof SUBGOAL0 nil.
            discriminate.
      }
      assert (eval_Cexprval_denote env callees z Pre_st v Post_st ). {
         pose proof SUBGOAL0 nil; discriminate.
      }
      specialize (CType v J).
      tauto.
   (* 9 *)
   - clear eval_sound eval_l_sound.
      intros; simpl in *.
      destruct H2 as [?[??]].
      assert (Safe_eval safe_checker z Pre_asrt = Some Post_asrts). {
         unfold Safe_eval.
         destruct (eval_Cexprval z Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
         - unfold Option_move. pose proof SUBGOAL0 nil.
            destruct (Find_None
            (map
               (fun a : expr_val * list Proposition * assertion =>
               match safe_checker (snd a) (snd (fst a)) with
               | Some b => if b then Some (fst (fst a), snd a) else None
               | None => None
               end) l)) eqn:?; simpl in *; try tauto; try discriminate.
         - pose proof SUBGOAL0 nil.
            discriminate.
      }
      assert (eval_Cexprval_denote env callees z Pre_st v Post_st ). {
         pose proof SUBGOAL0 nil; discriminate.
      }
      specialize (CType v J).
      tauto.
   (* 10 *)
   - intros.
   unfold Safe_eval in H1.
   simpl in H1.
   discriminate.
   (* 11 *)
   - intros.
   unfold Safe_eval in H1.
   simpl in H1.
   discriminate.
   (* 12 *)
   - intros.
   unfold Safe_eval in H1.
   simpl in H1.
   discriminate.
+ induction x as [z CType|i CType|z CType|z CType|z CType|z CType|z CType|z CType|z CType|z CType|z CType|z CType]. 
  -intros.
   unfold Safe_eval_l in H1.
   simpl in H1.
   discriminate.
   (* 2 *)
  - pose proof SUBGOAL0 nil. discriminate.
  (* 3 *)
  - clear eval_sound eval_l_sound.
    intros; simpl in *.
    unfold Post_denote.
    unfold Safe_eval in H1; simpl in *.
    destruct (eval_Cexprval z Pre_asrt); simpl in *; try discriminate.
    destruct (Option_move
    (map
       (fun a : expr_val * list Proposition * assertion =>
        match eval_val (Sep_list (Split_assert (snd a))) (fst (fst a)) with
        | Some v => Some (v, snd (fst a), snd a)
        | None => None
        end) l)) eqn:?; simpl in *; try tauto; try discriminate.
    unfold Option_move in Heqo.
    destruct (Find_None
    (map
       (fun a : expr_val * list Proposition * assertion =>
        match eval_val (Sep_list (Split_assert (snd a))) (fst (fst a)) with
        | Some v => Some (v, snd (fst a), snd a)
        | None => None
        end) l)) eqn:?; simpl in *; try tauto; try discriminate.
    injection Heqo as Heqo. 
    unfold Option_move in H1.
    destruct (Find_None
    (map
       (fun a : expr_val * list Proposition * assertion =>
        match safe_checker (snd a) (snd (fst a)) with
        | Some b => if b then Some (fst (fst a), snd a) else None
        | None => None
        end)
       (Clear_option
          (map
             (fun a : expr_val * list Proposition * assertion =>
              match eval_val (Sep_list (Split_assert (snd a))) (fst (fst a)) with
              | Some v => Some (v, snd (fst a), snd a)
              | None => None
              end) l)))) eqn:?; simpl in *; try discriminate; try tauto.
    destruct (Find_None
    (map
       (fun a : expr_val * list Proposition * assertion =>
        match safe_checker (snd a) (snd (fst a)) with
        | Some b => if b then Some (fst (fst a), snd a) else None
        | None => None
        end) l0)) eqn:?; simpl in *; try discriminate; try tauto.
    specialize (CType v J).
    pose proof CType H H0.
    assert (Safe_eval safe_checker z Pre_asrt = Some Post_asrts). {
      unfold Safe_eval.
      destruct (eval_Cexprval z Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
      - unfold Option_move; pose proof SUBGOAL0 Post_asrts.
         destruct (Find_None
         (map
            (fun a : expr_val * list Proposition * assertion =>
             match safe_checker (snd a) (snd (fst a)) with
             | Some b => if b then Some (fst (fst a), snd a) else None
             | None => None
             end) l1)) eqn:?; simpl in *; try tauto; try discriminate.
      - pose proof SUBGOAL0 Post_asrts.
        discriminate.
    }
    pose proof SUBGOAL0 Post_asrts.
    try tauto; try discriminate.
    pose proof SUBGOAL0 Post_asrts.
    try tauto; try discriminate.
    pose proof SUBGOAL0 Post_asrts.
    try tauto; try discriminate.
    pose proof SUBGOAL0 Post_asrts.
    try tauto; try discriminate.
    pose proof SUBGOAL0 Post_asrts.
    try tauto; try discriminate.
   (* 4 *)
   - intros.
   unfold Safe_eval_l in H1.
   simpl in H1.
   discriminate.
  (* 5 *)
   -intros.
   unfold Safe_eval_l in H1.
   simpl in H1.
   discriminate.
   (* 6 *)
   -intros.
   unfold Safe_eval_l in H1.
   simpl in H1.
   discriminate.
   (* 7 *)
   -intros.
   unfold Safe_eval_l in H1.
   simpl in H1.
   discriminate.
   (* 8 *)
   - clear eval_sound eval_l_sound.
      intros; simpl in *.
      assert (Safe_eval_l safe_checker z Pre_asrt = Some Post_asrts). {
         unfold Safe_eval_l.
         destruct (eval_Cexprval_l z Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
         destruct H2 as [?[??]].
         destruct H3 as [?[?[?[??]]]].
         unfold Option_move.
         destruct (Find_None
         (map
            (fun a : expr_val * list Proposition * assertion =>
             match safe_checker (snd a) (snd (fst a)) with
             | Some b => if b then Some (fst (fst a), snd a) else None
             | None => None
             end) l)) eqn:?; simpl in *; try tauto; try discriminate.
         + pose proof SUBGOAL0 Post_asrts. discriminate.
         + pose proof SUBGOAL0 Post_asrts. discriminate.
         + pose proof SUBGOAL0 Post_asrts. discriminate.
      }
      assert (eval_Cexprval_l_denote env callees z Pre_st v Post_st). {
         induction z; simpl in *; try tauto; try discriminate.
         - destruct H2 as [?[??]].
            destruct H4 as [?[?[?[??]]]].
            split; try tauto; try discriminate.
            pose proof SUBGOAL0 Post_asrts. try tauto; try discriminate.
         - pose proof SUBGOAL0 Post_asrts. try tauto; try discriminate.
         - pose proof SUBGOAL0 Post_asrts. try tauto; try discriminate.
         - pose proof SUBGOAL0 Post_asrts. try tauto; try discriminate.
      }
      specialize (CType v J).
      tauto.
   (* 9 *)
   - clear eval_sound eval_l_sound.
      intros; simpl in *.
      assert (Safe_eval_l safe_checker z Pre_asrt = Some Post_asrts). {
         unfold Safe_eval_l.
         destruct (eval_Cexprval_l z Pre_asrt) eqn:?; simpl in *; try tauto; try discriminate.
         destruct H2 as [?[??]].
         destruct H3 as [?[?[?[??]]]].
         unfold Option_move.
         destruct (Find_None
         (map
            (fun a : expr_val * list Proposition * assertion =>
             match safe_checker (snd a) (snd (fst a)) with
             | Some b => if b then Some (fst (fst a), snd a) else None
             | None => None
             end) l)) eqn:?; simpl in *; try tauto; try discriminate.
         + pose proof SUBGOAL0 Post_asrts. discriminate.
         + pose proof SUBGOAL0 Post_asrts. discriminate.
         + pose proof SUBGOAL0 Post_asrts. discriminate.
      }
      assert (eval_Cexprval_l_denote env callees z Pre_st v Post_st). {
         induction z; simpl in *; try tauto; try discriminate.
         - destruct H2 as [?[??]].
            destruct H4 as [?[?[?[??]]]].
            split; try tauto; try discriminate.
            pose proof SUBGOAL0 Post_asrts. try tauto; try discriminate.
         - pose proof SUBGOAL0 Post_asrts. try tauto; try discriminate.
         - pose proof SUBGOAL0 Post_asrts. try tauto; try discriminate.
         - pose proof SUBGOAL0 Post_asrts. try tauto; try discriminate.
      }
      specialize (CType v J).
      tauto.
   (* 10 *)
   -intros.
   unfold Safe_eval_l in H1.
   simpl in H1.
   discriminate.
   (* 11 *)
   -intros.
   unfold Safe_eval_l in H1.
   simpl in H1.
   discriminate.
   (* 12 *)
   -intros.
   unfold Safe_eval_l in H1.
   simpl in H1.
   discriminate.
Qed. *)
