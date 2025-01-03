Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
From SetsClass Require Import SetsClass.
From AUXLib Require Import relations Axioms. 
From StateMonad.monadnrm Require Import monadbasic safeexec_lib.
From RecordUpdate Require Import RecordSet.


Import SetsNotation.
Local Open Scope sets.

Import MonadNotation.
Local Open Scope stmonad.


Record mergest :Type := mk_mergest {
  xl: list Z; (* x list*)
  yl: list Z; (* y list*)
  pl: list Z;
  ql: list Z;
}.

#[local] Instance eta_r : Settable mergest := settable! mk_mergest <xl; yl; pl; ql>.


Definition update_x (record: mergest) (v: list Z) : mergest := 
  set xl (fun _ => v) record.
Definition update_y (record: mergest) (v: list Z) : mergest := 
  set yl (fun _ => v) record.
Definition update_p (record: mergest) (v: list Z) : mergest := 
  set pl (fun _ => v) record.
Definition update_q (record: mergest) (v: list Z) : mergest := 
  set ql (fun _ => v) record.


#[local] Instance merge_state  : stateclass := {|
  Σ := mergest
|}.



Definition fieldstorev x (v:list Z) : mergest -> Prop := fun st => st.(x) = v.
Notation "x ↦ₕ v" := (fieldstorev x v) (at level 35, no associativity).

Ltac destruct_st σ :=
  let xl := fresh "xl" in let yl := fresh "yl" in 
  let pl := fresh "pl" in let yl := fresh "ql" in  destruct σ as [xl yl pl ql].


Section  merge_monad.

  Definition merge_cond : (bool * (list Z)) -> program bool :=
    fun '(brkflag,  retl) => return brkflag. 
  
  Definition get_xlist : program (list Z) :=
    s <- get ;;  return s.(xl).

  Definition get_ylist : program (list Z) :=
    s <- get ;;  return s.(yl).

  Definition update_xlist l: program unit :=
    s <- get ;; (put (update_x s l)).

  Definition update_ylist l: program unit :=
    s <- get ;; (put (update_y s l)).

  Definition merge_body : (bool * (list Z)) -> program (bool * (list Z)) :=
    fun '(brkflag,  retl) =>
      x <- get_xlist ;; 
        match x with 
        | nil => (y <- get_ylist ;; return (true, retl ++ y))
        | z :: l => 
          y <- get_ylist ;; 
          match y with 
          | nil => return (true, retl ++ x)
          | z0 :: l0 => 
            if Z.ltb z z0 
            then (update_xlist l) ;; return (false, retl ++ z :: nil)
            else (update_ylist l0);; return (false, retl ++ z0 :: nil)
          end
        end.

  Definition merge := 
    whileret merge_cond merge_body (true, nil).

  Section safeexec_lemmas.


    Lemma get_xlist_eval: forall l l0, 
      (fun st => (xl ↦ₕ l) st /\ (yl ↦ₕ l0) st) -@ get_xlist -⥅ 
      (fun st =>(xl ↦ₕ l) st /\ (yl ↦ₕ l0) st) ♯ l. 
    Proof.
      unfold hs_eval,  fieldstorev.
      intros.
      exists σₕ.
      split;auto.
      do 2 exists σₕ. 
      destruct_st σₕ.
      cbn in *.
      unfold get_xlist, M_to_program, getst, bind, ret.
      cbn.
      splits;auto.
      destruct H. auto.
    Qed.

    Lemma get_ylist_eval: forall l l0, 
      (fun st => (xl ↦ₕ l) st /\ (yl ↦ₕ l0) st) -@ get_ylist -⥅ 
      (fun st =>(xl ↦ₕ l) st /\ (yl ↦ₕ l0) st) ♯ l0. 
    Proof.
      unfold hs_eval,  fieldstorev.
      intros.
      exists σₕ.
      split;auto.
      do 2 exists σₕ. 
      destruct_st σₕ.
      cbn in *.
      unfold get_ylist, M_to_program, getst, bind, ret.
      cbn.
      splits;auto.
      destruct H. auto.
    Qed.

    Lemma merge_body_eval_xlnil: forall brkflag retl l,
      (fun st =>(xl ↦ₕ nil) st /\ (yl ↦ₕ l) st) -@ (merge_body (brkflag, retl)) -⥅ 
      (fun st => True) ♯ (true, retl ++ l).
    Proof.
      intros.
      unfold merge_body.
      eapply hsevalbind_derive with (Q:= fun _ _ => True) (P':= fun _ => (fun st =>(xl ↦ₕ nil) st /\ (yl ↦ₕ l) st)).
      apply get_xlist_eval.
      cbn.
      eapply hsevalbind_derive with (Q:= fun _ _ => True) (P':= fun _ => (fun st =>(xl ↦ₕ nil) st /\ (yl ↦ₕ l) st)).
      apply get_ylist_eval.
      admit.  (* highret_eval2 *)
    Admitted.


    Lemma merge_body_eval_xlnotnil_ylnil: forall brkflag retl z l ,
      (fun st =>(xl ↦ₕ (z :: l)) st /\ (yl ↦ₕ nil) st) -@ (merge_body (brkflag, retl)) -⥅ 
      (fun st => True) ♯ (true, retl ++ (z :: l)).
    Proof.
      intros.
      unfold merge_body.
      eapply hsevalbind_derive with (Q:= fun _ _ => True) (P':= fun _ => (fun st =>(xl ↦ₕ (z :: l)) st /\ (yl ↦ₕ nil) st)).
      apply get_xlist_eval.
      cbn.
      eapply hsevalbind_derive with (Q:= fun _ _ => True) (P':= fun _ => (fun st =>(xl ↦ₕ (z :: l)) st /\ (yl ↦ₕ nil) st)).
      apply get_ylist_eval.
      cbn.
      admit.  (* highret_eval2 *)
    Admitted.

    
      

      
    


  End safeexec_lemmas.

End  merge_monad.


Section  splitstep_monad.

  Inductive S_step : mergest -> mergest -> Prop :=
  | splitstep_qe2 : forall st1 st2 z z0 z1 xpl pql pql' qel, 
                            pql ++ z::z0 ::nil = z1 :: pql' ->
                            st1.(xl) = xpl ->
                            st1.(pl) = pql -> 
                            st1.(ql) = z :: z0:: qel ->
                            st2 = update_q (update_p (update_x st1 (xpl ++ z1::nil)) pql') qel ->
                            S_step st1 st2.
    
  Definition step_two : program unit :=
    fun st1 _ st2 => S_step st1 st2.

  Inductive S_stepend : mergest -> mergest -> Prop :=
  | splitstep_qe0 : forall st1, 
                            st1.(ql) = (@nil Z) ->
                            S_stepend st1 st1
  | splitstep_qe1 : forall st1 st2 z z0 xpl pql pql', 
                            pql ++ z::nil = z0 :: pql' ->
                            st1.(xl) = xpl ->
                            st1.(pl) = pql -> 
                            st1.(ql) = z ::nil ->
                            st2 = update_q (update_p (update_x st1 (xpl ++ z0::nil)) pql') nil ->
                            S_stepend st1 st2.

  Definition step_end : program unit :=
    fun st1 _ st2 => S_stepend st1 st2.

  Definition splitlist : program unit :=
    (Repeat step_two) ;; step_end.

End  splitstep_monad.



Section splitwhile_monad.

  Definition split_cond : program bool :=
    s <- get ;; match s.(xl) with | nil => return false | _ => return true end.

  Inductive split_step : mergest -> mergest -> Prop  :=
    | splitstep : forall st1 st2 z l l0 l1,
                      st1.(xl) = z::l ->
                      st1.(pl) = l0 ->
                      st1.(ql) = l1 ->
                      st2 =(update_q (update_p (update_x st1 l)  l1) (z::l0)) ->
                      split_step st1 st2.

  Definition split_body : program unit :=
    step_to_program split_step.

  Definition splitwhile : program unit := while split_cond split_body.
  
End splitwhile_monad.



Section mergesort_monad.

  Definition mergesortrec_f  (W :  program (list Z)) 
                        : program (list Z) :=
  splitwhile ;; 
  s <- get ;; match s.(ql) with 
              | nil => return (s.(pl)) 
              | _ =>  put (update_x s (s.(pl))) ;;  p1 <- W ;;  
                      put (update_x s (s.(ql))) ;;  q1 <- W ;;
                      put (update_y (update_x s p1) q1) ;; 
                      '(brkflag,  retl) <- merge ;;
                      return retl
              end.

  Definition mergesortrec := BW_LFix (mergesortrec_f).

  Definition mergsort (x: list Z) : program (list Z) := 
    put (mk_mergest x nil nil nil) ;; mergesortrec.

End mergesort_monad.




