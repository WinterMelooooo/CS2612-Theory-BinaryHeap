Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Local Open Scope sets_scope.
Require Import Coq.Logic.Classical.
Require Import Coq.ZArith.ZArith_dec.
Require Import Lia.
Require Import Coq.Logic.Classical_Pred_Type.
(*********************************************************)
(**                                                      *)
(** Binary Tree                                          *)
(**                                                      *)
(*********************************************************)

Module BinaryTree.

Record BinaryTree (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex;
  go_left: Edge -> Prop;

  (* 每个节点最多一个父节点 *)
  single_parent: forall v e1 e2,
  evalid e1 -> evalid e2 ->
  dst e1 = v -> dst e2 = v -> 
  e1 = e2;

  (* 每个节点最多两个子节点
  at_most_two_children: forall v e1 e2 e3,
  evalid e1 -> evalid e2 -> evalid e3 ->
  src e1 = v -> src e2 = v -> src e3 = v ->
  go_left e1 -> go_left e2 -> ~ go_left e3 ->
  e1 = e2; *)

  (* 每个节点最多有一个左子节点 *)
  single_left_child: forall v e1 e2,
  evalid e1 -> evalid e2 ->
  src e1 = v -> src e2 = v ->
  go_left e1 -> go_left e2 ->
  e1 = e2;

  (* 每个节点最多有一个右子节点 *)  
  single_right_child: forall v e1 e2,
  evalid e1 -> evalid e2 ->
  src e1 = v -> src e2 = v ->
  ~ go_left e1 -> ~ go_left e2 ->
  e1 = e2;

  (* 无环性质 *)
  (* acyclic: forall v,
    ~ (exists path, path_to_self v path);

  (* 连通性 *)
  connected: forall v1 v2,
    vvalid v1 -> vvalid v2 ->
    exists path, valid_path path v1 v2; *)

}.

Definition go_right (V E: Type) (bt: BinaryTree V E) (e: E): Prop :=
  ~ go_left _ _ bt e. (* == ~ go_left V E bt e *)

Notation "bt '.(vvalid)'" := (vvalid _ _ bt) (at level 1). (* bt.(vvalid) x == vvalid Vertex Edge bt x *)
Notation "bt '.(evalid)'" := (evalid _ _ bt) (at level 1).
Notation "bt '.(src)'" := (src _ _ bt) (at level 1).
Notation "bt '.(dst)'" := (dst _ _ bt) (at level 1).
Notation "bt '.(go_left)'" := (go_left _ _ bt) (at level 1).
Notation "bt '.(go_right)'" := (go_right _ _ bt) (at level 1). 

Record step_aux {V E: Type} (bt: BinaryTree V E) (e: E) (x y: V): Prop := (*V&E可以是传入的任意类型，相当于c++中的template*)
{
  step_evalid: bt.(evalid) e;
  step_src_valid: bt.(vvalid) x;
  step_dst_valid: bt.(vvalid) y;
  step_src: bt.(src) e = x;
  step_dst: bt.(dst) e = y;
}.

Definition step_l {V E: Type} (bt: BinaryTree V E) (x y: V): Prop := (*e=x->y && x -> left -> y*)
  exists e, step_aux bt e x y /\ bt.(go_left) e.

Definition step_r {V E: Type} (bt: BinaryTree V E) (x y: V): Prop :=
  exists e, step_aux bt e x y /\ bt.(go_right) e.

Definition step_u {V E: Type} (bt: BinaryTree V E) (x y: V): Prop := (*e=x->y*)
  exists e, step_aux bt e y x.

Record legal {V E: Type} (bt: BinaryTree V E): Prop :=
{
  step_l_unique: forall x y1 y2, step_l bt x y1 -> step_l bt x y2 -> y1 = y2; (*每个顶点最多有一个左子节点。*)
  step_r_unique: forall x y1 y2, step_r bt x y1 -> step_r bt x y2 -> y1 = y2;
  step_u_unique: forall x y1 y2, step_u bt x y1 -> step_u bt x y2 -> y1 = y2;
}.

End BinaryTree.

Notation "bt '.(vvalid)'" := (BinaryTree.vvalid _ _ bt) (at level 1).
Notation "bt '.(evalid)'" := (BinaryTree.evalid _ _ bt) (at level 1).
Notation "bt '.(src)'" := (BinaryTree.src _ _ bt) (at level 1).
Notation "bt '.(dst)'" := (BinaryTree.dst _ _ bt) (at level 1).
Notation "bt '.(go_left)'" := (BinaryTree.go_left _ _ bt) (at level 1).
Notation "bt '.(go_right)'" := (BinaryTree.go_right _ _ bt) (at level 1).
Notation "'BinTree'" := (BinaryTree.BinaryTree) (at level 0).

(** * 堆 *)
Record Heap (h: BinTree Z Z): Prop := (*小顶堆*)
{
  heap_l: forall x y: Z, BinaryTree.step_l h x y -> (x <= y)%Z;
  heap_r: forall x y: Z, BinaryTree.step_r h x y -> (x <= y)%Z;
}.
  

(** * leaf *)
Definition Leaf (V E: Type) (bt: BinTree V E) (v: V): Prop :=
  bt.(vvalid) v ->
  (~ exists y, BinaryTree.step_l bt v y) /\
  (~ exists y, BinaryTree.step_r bt v y).

Definition Node (V E: Type) (bt: BinTree V E) (v: V): Prop :=
  ~ Leaf V E bt v.

Definition bintree_connected {V E: Type} (bt: BinTree V E): Prop :=
  exists root: V,
    bt.(vvalid) root /\
    (~ exists e, bt.(evalid) e /\ bt.(dst) e = root) /\
    (forall v, 
      bt.(vvalid) v -> 
      v <> root ->
      exists e, bt.(evalid) e /\ bt.(dst) e = v).


Definition Abs (h: BinTree Z Z) (X: Z -> Prop): Prop :=
  X == h.(vvalid).

Record PartialHeap (h: BinTree Z Z): Prop := {
  (* 最多存在一个节点v违反堆的性质 *)
  exists_violation: forall v1 v2: Z,
    (* 如果v1和v2都违反堆的性质 *)
    (h.(vvalid) v1 /\ 
      exists y1: Z, (BinaryTree.step_l h v1 y1 \/ BinaryTree.step_r h v1 y1) /\ (v1 > y1)%Z) ->
    (h.(vvalid) v2 /\ 
      exists y2: Z, (BinaryTree.step_l h v2 y2 \/ BinaryTree.step_r h v2 y2) /\ (v2 > y2)%Z) ->
    (* 那么v1和v2必须是同一个节点 *)
    v1 = v2;
}.


Record StrictPartialHeap (h: BinTree Z Z): Prop := {
  (* 存在一个节点v违反堆的性质 *)
  exists_violation_strict: exists v: Z,
    (h.(vvalid) v /\ (* v必须是合法节点 *)
    exists y: Z, 
    ((BinaryTree.step_l h v y \/ BinaryTree.step_r h v y) /\ (v > y)%Z)) /\
    (
      forall v2: Z, (h.(vvalid) v2 /\ (* v必须是合法节点 *)
      exists y: Z, 
      ((BinaryTree.step_l h v2 y \/ BinaryTree.step_r h v2 y) /\ (v2 > y)%Z)) -> 
      (v2 = v)
    )
}.

(*大于两个孩子*)
(*
Record StrictPartialHeap1 (h: BinTree Z Z): Prop := {
  (* 存在一个节点v同时违反左右子节点的堆性质 *)
  exists_violation_strict1: exists v: Z,
    (h.(vvalid) v /\ (* v必须是合法节点 *)
    (* v必须同时有左右子节点，并且比两个子节点都大 *)
    (exists yl yr: Z,
      BinaryTree.step_l h v yl /\ 
      BinaryTree.step_r h v yr /\ 
      (v > yl)%Z /\ 
      (v > yr)%Z)) /\ (forall v2: Z, (h.(vvalid) v2 /\ (* v必须是合法节点 *)
      (* v必须同时有左右子节点，并且比两个子节点都大 *)
      (exists yl yr: Z,
        BinaryTree.step_l h v2 yl /\ 
        BinaryTree.step_r h v2 yr /\ 
        (v2 > yl)%Z /\ 
        (v2 > yr)%Z)) -> (v2 = v))
}.*)


Record StrictPartialHeap1 (h: BinTree Z Z): Prop := {
  (* 存在一个节点v同时违反左右子节点的堆性质 *)
  exists_violation_strict1: exists v: Z,
    (h.(vvalid) v /\ (* v必须是合法节点 *)
    (* v必须同时有左右子节点，并且比两个子节点都大 *)
    (exists yl yr: Z,
      BinaryTree.step_l h v yl /\ 
      BinaryTree.step_r h v yr /\ 
      (v > yl)%Z /\ 
      (v > yr)%Z)) /\ 
      (forall v2, (exists y2, ((BinaryTree.step_l h v2 y2 \/ BinaryTree.step_l h v2 y2) /\ (v2 > y2)%Z)) -> (v2 = v))
}.


Record StrictPartialHeap2 (h: BinTree Z Z): Prop := {
  forall_no_violation_right: forall v yr: Z,
    BinaryTree.step_r h v yr -> (v <= yr)%Z;
  exists_violation_strict2: exists v yl: Z,
    (BinaryTree.step_l h v yl /\ 
      (v > yl)%Z) /\
    (forall v2, (exists yl2, (BinaryTree.step_l h v2 yl2 /\ (v2 > yl2)%Z)) -> (v2 = v))
}.

Record StrictPartialHeap3 (h: BinTree Z Z): Prop := {
  forall_no_violation_left: forall v yl: Z,
    BinaryTree.step_l h v yl -> (v <= yl)%Z;
  exists_violation_strict3: exists v yr: Z,
    (BinaryTree.step_r h v yr /\ 
      (v > yr)%Z) /\
    (* 其他所有节点都满足堆的性质 *)
    (forall v2,( exists yr2, (BinaryTree.step_r h v2 yr2 /\ (v2 > yr2)%Z))-> (v2 = v))
}.

Theorem strict_partial_heap_classification:
  forall h: BinTree Z Z,
    StrictPartialHeap h -> StrictPartialHeap1 h \/ StrictPartialHeap2 h \/ StrictPartialHeap3 h.
Proof.
  intros.
  destruct H as [v [Hv_valid [ [y [Hstep Hcomp] ] Hothers ] ] ].
  destruct v.
  destruct H.
  destruct H.
  destruct H1 as [x0 [H1][H2]].
  destruct H1.
  (*存在一个左子节点违反性质*)
  - destruct (classic (exists k, BinaryTree.step_r h x k /\ (x > k)%Z)) 
  as [ [k [H_step_r H_vio_r]] | H_right_violation ].
    (*StrictPartialHeap1的情况*)
    + left.
      split.
      exists x.
      split.
      ++ split.
        +++ tauto.
        +++ exists x0, k.
            tauto.
      ++ intros v1.
         specialize (H0 v1).
         intros.
         destruct H2.
         destruct H0.
         +++ split.
            ++++ destruct H2 as [[H4 | H5] H_gt].
                 destruct H4.
                 destruct H0.
                 destruct H0.
                 tauto.
                 destruct H5.
                 destruct H0.
                 destruct H0.
                 tauto.
            ++++ exists x1.
                 tauto.
          +++ tauto.
      (*StrictPartialHeap2的情况*)
      + right. left.
        pose proof not_ex_all_not Z _ H_right_violation.
        simpl in H2.
        split.
        ++  intros.
            specialize (H2 yr).
            apply not_and_or in H2.
            destruct (classic (v=x)) as [left|right].
            +++ destruct H2.  
                ++++ exfalso.   
                     apply H2.
                     rewrite <- left.
                     tauto.
                ++++ lia.
            +++ specialize (H0 v).
                apply imply_to_or in H0.
                destruct H0.
                apply not_and_or in H0.
                destruct H0.
                ++++ destruct H4.
                     destruct H4.
                     destruct H4. 
                     tauto.
                ++++ pose proof not_ex_all_not Z _ H0.
                     simpl in H5.
                     specialize (H5 yr).
                     apply not_and_or in H5.
                     destruct H5.
                     +++++ tauto.
                     +++++ lia.
                ++++ tauto.
        ++ exists x, x0.
           split.
           +++ tauto.
           +++ intros v3.
               specialize (H0 v3).
               apply imply_to_or in H0.
               destruct H0.
               ++++ intros.
                    apply not_and_or in H0.
                    destruct H0.
                    +++++ destruct H4.
                          destruct H4.
                          destruct H4.
                          destruct H4.
                          destruct H4.
                          tauto.
                    +++++ pose proof not_ex_all_not Z _ H0.
                          simpl in H5.
                          destruct H4.
                          specialize (H5 x1).
                          exfalso.
                          apply H5.
                          tauto.
               ++++ intros.
                    tauto.
  (*存在一个右子节点违反性质*)
  - destruct (classic (exists k, BinaryTree.step_l h x k /\ (x > k)%Z)) 
  as [ [k [H_step_l H_vio_l]] | H_left_violation ].
    (*StrictPartialHeap1的情况*)
    + left.
      split.
      exists x.
      split.
      ++ split.
        +++ tauto.
        +++ exists k, x0.
            tauto.
      ++ intros v1.
         specialize (H0 v1).
         intros.
         destruct H2.
         destruct H0.
         +++ split.
            ++++ destruct H2 as [[H4 | H5] H_gt].
                 destruct H4.
                 destruct H0.
                 destruct H0.
                 tauto.
                 destruct H5.
                 destruct H0.
                 destruct H0.
                 tauto.
            ++++ exists x1.
                 tauto.
          +++ tauto.
      (*StrictPartialHeap3的情况*)
      + right. right.
        pose proof not_ex_all_not Z _ H_left_violation.
        simpl in H2.
        split.
        ++  intros.
            specialize (H2 yl).
            apply not_and_or in H2.
            destruct (classic (v=x)) as [left|right].
            +++ destruct H2.  
                ++++ exfalso.   
                     apply H2.
                     rewrite <- left.
                     tauto.
                ++++ lia.
            +++ specialize (H0 v).
                apply imply_to_or in H0.
                destruct H0.
                apply not_and_or in H0.
                destruct H0.
                ++++ destruct H4.
                     destruct H4.
                     destruct H4. 
                     tauto.
                ++++ pose proof not_ex_all_not Z _ H0.
                     simpl in H5.
                     specialize (H5 yl).
                     apply not_and_or in H5.
                     destruct H5.
                     +++++ tauto.
                     +++++ lia.
                ++++ tauto.
        ++ exists x, x0.
           split.
           +++ tauto.
           +++ intros v3.
               specialize (H0 v3).
               apply imply_to_or in H0.
               destruct H0.
               ++++ intros.
                    apply not_and_or in H0.
                    destruct H0.
                    +++++ destruct H4.
                          destruct H4.
                          destruct H4.
                          destruct H4.
                          destruct H4.
                          tauto.
                    +++++ pose proof not_ex_all_not Z _ H0.
                          simpl in H5.
                          destruct H4.
                          specialize (H5 x1).
                          exfalso.
                          apply H5.
                          tauto.
               ++++ intros.
                    tauto.

Qed.



    (* intros.
    
    (* 分解 StrictPartialHeap 的假设 *)
    destruct H as [v [Hv_valid [ [y [Hstep Hcomp] ] Hothers ] ] ].
    
    (* Hstep: BinaryTree.step_l h v y \/ BinaryTree.step_r h v y
       Hcomp: v > y *)
    destruct v.
    destruct H.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.
    (*情况1：左儿子比父亲小，即StrictPartialHeap1或StrictPartialHeap2*)
    - destruct (classic (exists k, BinaryTree.step_r h x k /\ (x > k)%Z)) 
    as [ [k [Hstep_r_e_r Hv_gt_e_r]] | Hno_right_violation ].
      (*StrictPartialHeap1的情况*)
      + left.
      split.
      exists x.
      split.
          ++ apply H.
          ++ split.
              +++ exists x0, k.
                  tauto.
              +++ apply H1.
      (*StrictPartialHeap3的情况*)
      + right. left.
        split.
        exists x.
        split.
            ++ apply H.
            ++ split.
                +++ exists x0.
                    split.
                    ++++ apply H0.
                    ++++ split.
                      +++++ apply H2.
                      +++++
                        intros.
                        assert (Hno_right_violation' : forall k : Z, ~ (BinaryTree.step_r h x k /\ (x > k)%Z)).
                        {
                          intros k [Hrl Hgt].
                          apply Hno_right_violation.
                          exists k. split; assumption.
                        }
                        specialize (Hno_right_violation' yr).
                        tauto.

                +++ apply H1.
    (*情况2：右儿子比父亲小，即StrictPartialHeap1或StrictPartialHeap3*)
    - destruct (classic (exists k, BinaryTree.step_l h x k /\ (x > k)%Z)) 
    as [ [k [Hstep_r_e_r Hv_gt_e_r]] | Hno_left_violation ].
      (*StrictPartialHeap1的情况*)
      + left.
      split.
      exists x.
      split.
          ++ apply H.
          ++ split.
              +++ exists k, x0.
                  tauto.
              +++ apply H1.
      (*StrictPartialHeap3的情况*)
      + right. right.
        split.
        exists x.
        split.
            ++ apply H.
            ++ split.
                +++ exists x0.
                    split.
                    ++++ apply H0.
                    ++++ split.
                      +++++ apply H2.
                      +++++
                        intros.
                        assert (Hno_left_violation' : forall k : Z, ~ (BinaryTree.step_l h x k /\ (x > k)%Z)).
                        {
                          intros k [Hrl Hgt].
                          apply Hno_left_violation.
                          exists k. split; assumption.
                        }
                        specialize (Hno_left_violation' yl).
                        tauto.

                +++ apply H1.

Qed. *)

Theorem inverse_strict_partial_heap_classification:
  forall h: BinTree Z Z,
    StrictPartialHeap1 h \/ StrictPartialHeap2 h \/ StrictPartialHeap3 h -> StrictPartialHeap h.
Proof.
Admitted.

Theorem partial_heap_classification:
  forall h: BinTree Z Z,
    PartialHeap h -> StrictPartialHeap h \/ Heap h.
Proof.
Admitted.
(* Proof.
  intros h PH.
  destruct (classic (exists v: Z,
    h.(vvalid) v /\
    exists y: Z,
      (BinaryTree.step_l h v y \/ BinaryTree.step_r h v y) /\ (v > y)%Z
  )) as [Hviol | Hnoviol].
    (*有局部破坏*)
    - left.
      split.
      destruct PH.
      destruct Hviol.
      exists x.
      split.
      + apply H.
      + split.
        ++ apply H.
        ++ intros.
            destruct H as [Hvx [Hy [Hstep Hx_gt_y]]].
            destruct H1 as [Hstep_l | Hstep_r]. 
            +++ specialize exists_violation0 with x0 x.
                destruct (Z.compare_spec x0 y) as [Hlt | Heq | Hgt].
                ++++ rewrite Hlt.
                    reflexivity.
                ++++ apply Z.lt_le_incl.
                    assumption.
                ++++ destruct exists_violation0.
                    +++++ split.
                        ++++++ destruct Hstep_l.
                              destruct H.
                              destruct H.
                              apply step_src_valid.
                        ++++++ exists y.
                              split.
                              +++++++ tauto.
                              +++++++ lia. 
                    +++++ split.
                        ++++++ apply Hvx.
                        ++++++ exists Hy.
                              tauto.
                    +++++ lia.
            +++ specialize exists_violation0 with x0 x.
                destruct (Z.compare_spec x0 y) as [Hlt | Heq | Hgt].
                ++++ rewrite Hlt.
                    reflexivity.
                ++++ apply Z.lt_le_incl.
                    assumption.
                ++++ destruct exists_violation0.
                    +++++ split.
                        ++++++ destruct Hstep_r.
                              destruct H.
                              destruct H.
                              apply step_src_valid.
                        ++++++ exists y.
                              split.
                              +++++++ tauto.
                              +++++++ lia. 
                    +++++ split.
                        ++++++ apply Hvx.
                        ++++++ exists Hy.
                              tauto.
                    +++++ lia.
    (*无局部破坏*)
    - right.
    Search "not_ex_all_not".
    Locate not_ex_all_not.
    pose proof not_ex_all_not Z _ Hnoviol.
    simpl in H.
    split.
      + intros.
      specialize H with x.
      apply not_and_or in H.
      destruct H.
        ++ destruct H0.
          destruct H0.
          destruct H0.
          tauto.
        ++ pose proof not_ex_all_not Z _ H.
          simpl in H1.
          specialize (H1 y).
          apply not_and_or in H1.
          destruct H1.
          +++ tauto.
          +++ lia.
      + intros.
      specialize H with x.
      apply not_and_or in H.
      destruct H.
        ++ destruct H0.
          destruct H0.
          destruct H0.
          tauto.
        ++ pose proof not_ex_all_not Z _ H.
          simpl in H1.
          specialize (H1 y).
          apply not_and_or in H1.
          destruct H1.
          +++ tauto.
          +++ lia.
Qed.                           *)

Theorem inverse_partial_heap_classification:
  forall h: BinTree Z Z,
    StrictPartialHeap h \/ Heap h -> PartialHeap h.
Proof.
Admitted.

Theorem eq_PH_SHH:
  forall h: BinTree Z Z,
    PartialHeap h <-> StrictPartialHeap h \/ Heap h.
Proof.
Admitted.

Theorem eq_SH_SH123:
  forall h: BinTree Z Z,
    StrictPartialHeap h <-> StrictPartialHeap1 h \/ StrictPartialHeap2 h \/ StrictPartialHeap3 h.
Proof.
Admitted.

Definition Root (h: BinTree Z Z) (v: Z): Prop :=
  h.(vvalid) v ->
  (~ exists y, BinaryTree.step_u h v y).

Require Import PL.Monad.
Require Import PL.StateRelMonad.
Import Monad SetMonad StateRelMonad.

(* 节点有效性保持不变 *)
Definition preserve_vvalid (bt bt': BinTree Z Z) : Prop :=
  BinaryTree.vvalid _ _ bt' == BinaryTree.vvalid _ _ bt.

(* 边有效性保持不变 *)
Definition preserve_evalid (bt bt': BinTree Z Z) : Prop :=
  BinaryTree.evalid _ _ bt' == BinaryTree.evalid _ _ bt.

(* 交换源节点 *)
Definition swap_src (v1 v2: Z) (bt bt': BinTree Z Z) : Prop := 
  (forall e, 
    BinaryTree.src _ _ bt' e = 
      if Z.eq_dec (BinaryTree.src _ _ bt e) v1 then v2 
      else if Z.eq_dec (BinaryTree.src _ _ bt e) v2 then v1 
      else BinaryTree.src _ _ bt e) /\
  
  (* Ensure step relations are updated accordingly *)
  (forall x y, 
    BinaryTree.step_l bt x y <-> 
    BinaryTree.step_l bt' (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) 
                       (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y)) /\
  
  (forall x y, 
    BinaryTree.step_r bt x y <-> 
    BinaryTree.step_r bt' (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) 
                       (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y)).

(* 交换目标节点 *)
Definition swap_dst (v1 v2: Z) (bt bt': BinTree Z Z) : Prop :=
  forall e, BinaryTree.dst _ _ bt' e = 
    if Z.eq_dec (BinaryTree.dst _ _ bt e) v1 then v2 
    else if Z.eq_dec (BinaryTree.dst _ _ bt e) v2 then v1 
    else BinaryTree.dst _ _ bt e.

(* 组合所有操作 *)
Definition swap_nodes (v1 v2: Z) : StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt: BinTree Z Z) (_:unit) (bt': BinTree Z Z) =>
    preserve_vvalid bt bt' /\
    preserve_evalid bt bt' /\
    swap_src v1 v2 bt bt' /\
    swap_dst v1 v2 bt bt' /\
    BinaryTree.go_left _ _ bt' = BinaryTree.go_left _ _ bt.

Definition move_up (v: Z): StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
    (* 检查节点 v 是合法的 *)
    BinaryTree.vvalid Z Z bt1 v /\ (
    (* 存在父节点 parent *)
    exists parent, BinaryTree.step_u bt1 v parent ->
      (* 使用新的 swap_nodes_rel 交换节点 *)
      (swap_nodes v parent) bt1 tt bt2).

Definition move_down (v: Z): StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
    BinaryTree.vvalid Z Z bt1 v /\(
    exists child,
      (BinaryTree.step_l bt1 v child \/ BinaryTree.step_r bt1 v child) ->
      (swap_nodes v child) bt1 tt bt2).

Definition move_up_in_partial_heap: StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
    (* 首先确保输入是一个 PartialHeap *)
    PartialHeap bt1 /\
    (* 如果是完整的堆，保持不变 *)
    ((Heap bt1 /\ bt1 = bt2) \/
    (* 如果是 StrictPartialHeap2，找到其唯一的违反堆性质的节点 *)
    (StrictPartialHeap2 bt1 /\
      exists v yl,
        (* 从 StrictPartialHeap2 的定义中获取违反性质的节点 v *)
        BinaryTree.vvalid Z Z bt1 v /\
        BinaryTree.vvalid Z Z bt1 yl /\
        BinaryTree.step_l bt1 v yl /\ (v > yl)%Z /\
        (swap_nodes v yl) bt1 tt bt2) \/
    (* 如果是 StrictPartialHeap3，类似处理 *)
    (StrictPartialHeap3 bt1 /\
      exists v yr,
        (* 从 StrictPartialHeap3 的定义中获取违反性质的节点 v *)
        BinaryTree.vvalid Z Z bt1 v /\
        BinaryTree.vvalid Z Z bt1 yr /\
        BinaryTree.step_r bt1 v yr /\ (v > yr)%Z /\
        (forall yl, BinaryTree.step_l bt1 v yl -> (v <= yl)%Z) /\
        (swap_nodes v yr) bt1 tt bt2)).

Definition move_down_in_partial_heap: StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
    (* 首先确保输入是一个 PartialHeap *)
    PartialHeap bt1 /\
    (* 如果是完整的堆，保持不变 *)
    ((Heap bt1 /\ bt1 = bt2) \/
    (* 如果是 StrictPartialHeap1，交换 v 和较小的子节点 *)
    (StrictPartialHeap1 bt1 /\
      exists v yl yr,
        BinaryTree.vvalid Z Z bt1 v /\
        BinaryTree.vvalid Z Z bt1 yl /\
        BinaryTree.vvalid Z Z bt1 yr /\
        BinaryTree.step_l bt1 v yl /\ 
        BinaryTree.step_r bt1 v yr /\ 
        (v > yl)%Z /\ 
        (v > yr)%Z /\
        (* 选择较小的子节点进行交换 *)
        ((yl <= yr)%Z /\ (swap_nodes v yl) bt1 tt bt2 \/
          (yr < yl)%Z /\ (swap_nodes v yr) bt1 tt bt2)) \/
    (* 如果是 StrictPartialHeap2，交换 v 和其左子节点 *)
    (StrictPartialHeap2 bt1 /\
      exists v yl,
        BinaryTree.vvalid Z Z bt1 v /\
        BinaryTree.vvalid Z Z bt1 yl /\
        BinaryTree.step_l bt1 v yl /\
        (v > yl)%Z /\
        (forall yr, BinaryTree.step_r bt1 v yr -> (v <= yr)%Z) /\
        (swap_nodes v yl) bt1 tt bt2) \/
    (* 如果是 StrictPartialHeap3，交换 v 和其右子节点 *)
    (StrictPartialHeap3 bt1 /\
      exists v yr,
        BinaryTree.vvalid Z Z bt1 v /\
        BinaryTree.vvalid Z Z bt1 yr /\
        BinaryTree.step_r bt1 v yr /\
        (v > yr)%Z /\
        (forall yl, BinaryTree.step_l bt1 v yl -> (v <= yl)%Z) /\
        (swap_nodes v yr) bt1 tt bt2)).
 
 (** ----------------------------------------------------- **)
 (**   辅助引理1: 处理 StrictPartialHeap2 交换后的情况   **)
 (** ----------------------------------------------------- **)

 Lemma uni_strictheap3:
 forall bt1 (v yr : Z),
   StrictPartialHeap3 bt1 ->
   (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
   BinaryTree.vvalid Z Z bt1 v ->
   BinaryTree.vvalid Z Z bt1 yr ->
   BinaryTree.step_r bt1 v yr ->
   (v > yr)%Z ->
   (forall yl, BinaryTree.step_l bt1 v yl -> (v <= yl)%Z) ->
   (BinaryTree.vvalid Z Z bt1 v ->
   (BinaryTree.vvalid Z Z bt1 v /\ (* v必须是合法节点 *)
    (* v必须有右孩子且大于右孩子，左孩子如果存在则不大于左孩子 *)
    (exists yr: Z,
      BinaryTree.step_r bt1 v yr /\ 
      (v > yr)%Z /\
      (forall yl: Z, 
        BinaryTree.step_l bt1 v yl -> 
        (v <= yl)%Z)))).
Proof.
intros bt1 v yr H H0 H1 H2 H3 H4.
destruct H as [H].
destruct H as [].
assert (x = v).
{
  destruct H as [H].
  destruct H5 as [].
  assert (BinaryTree.vvalid Z Z bt1 v /\
  (exists yr : Z,
     BinaryTree.step_r bt1 v yr /\
     (v > yr)%Z /\ (forall yl : Z, BinaryTree.step_l bt1 v yl -> (v <= yl)%Z))).
{
split.
- (* 证明第一部分：BinaryTree.vvalid Z Z bt1 v *)
exact H0.  (* 或 apply H0 *)

- (* 证明第二部分：exists yr... *)
exists yr.
split.
+ (* BinaryTree.step_r bt1 v yr *)
exact H2.
+ split.
* (* (v > yr)%Z *)
  exact H3.
* (* forall yl : Z, BinaryTree.step_l bt1 v yl -> (v <= yl)%Z *)
  intros yl H_step_l.
  apply H4.
  exact H_step_l.
 }
 assert (v = x).
 {
  apply H6.
  exact H7.
 }
 lia.
 }
 intros H6.  (* 引入前提 *)
 split.
 - (* 证明第一部分：BinaryTree.vvalid Z Z bt1 v *)
   exact H6.
 
 - (* 证明第二部分：exists yr0... *)
   exists yr.  (* 使用已知的 yr *)
   split.
   + (* 证明 BinaryTree.step_r bt1 v yr *)
     exact H2.
   + split.
     * (* 证明 (v > yr)%Z *)
       exact H3.
     * (* 证明 forall yl : Z, BinaryTree.step_l bt1 v yl -> (v <= yl)%Z *)
       exact H4.
Qed.



(** 下面是需要的引理：交换后仍是PartialHeap **)


Lemma preserve_partial_heap_after_swap_strict2:
  forall bt1 bt2 (v yl : Z),
    StrictPartialHeap2 bt1 ->
    BinaryTree.vvalid Z Z bt1 v ->
    BinaryTree.vvalid Z Z bt1 yl ->
    BinaryTree.step_l bt1 v yl ->
    (v > yl)%Z ->
    (swap_nodes v yl) bt1 tt bt2 ->
    PartialHeap bt2.
Proof.
Admitted.

Lemma simplify_if :
  forall (v yr : Z),
    (if Z.eq_dec v v then yr else if Z.eq_dec v yr then v else v) = yr.
Proof.
intros v yr.
  
(* Destruct the first Z.eq_dec v v *)
destruct (Z.eq_dec v v) as [H_eq | H_neq].

- (* Case 1: v = v (which is always true) *)
  (* The expression simplifies to yr *)
  reflexivity.

- (* Case 2: v <> v (impossible, contradiction) *)
  exfalso. apply H_neq. reflexivity.
Qed.

Lemma simplify_if2 :
  forall (v yr : Z),
    (if Z.eq_dec yr v
    then yr
    else if Z.eq_dec yr yr then v else yr) = v.
Proof.
intros v yr.
  
  (* Destruct the first Z.eq_dec yr v *)
  destruct (Z.eq_dec yr v) as [H_eq | H_neq].
  
  - (* Case 1: yr = v *)
    (* In this case, the expression simplifies to yr, which is v *)
    lia.
  
  - (* Case 2: yr <> v *)
    (* The second if is always true, so the expression simplifies to v *)
    destruct (Z.eq_dec yr yr) as [H_eq' | H_neq'].
    + (* Case 2a: yr = yr (trivially true) *)
      reflexivity.
    + (* Case 2b: yr <> yr (impossible, contradiction) *)
      exfalso. apply H_neq'. reflexivity.
Qed.


 (** ----------------------------------------------------- **)
 (**   辅助引理2: 处理 StrictPartialHeap3 交换后的情况   **)
 (** ----------------------------------------------------- **)

Lemma preserve_partial_heap_after_swap_strict3:
  forall bt1 bt2 (v yr : Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    StrictPartialHeap3 bt1 ->
    (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
    BinaryTree.vvalid Z Z bt1 v ->
    BinaryTree.vvalid Z Z bt1 yr ->
    BinaryTree.step_r bt1 v yr ->
    (v > yr)%Z ->
    (swap_nodes v yr) bt1 tt bt2 ->
    (* 结论：交换后 bt2 仍然是 PartialHeap *)
    PartialHeap bt2.
Proof.
  intros bt1 bt2 v yr H_heap Hv_valid_v Hv_valid_yr H_step H_gt H_swap.

  destruct H_heap as [SH].
  unfold swap_nodes in H_swap.
  destruct H_swap as [H1[H2[H3[H4[]]]]].
  unfold swap_src in H3.
  unfold swap_dst in H4.
  assert ( BinaryTree.vvalid Z Z bt2 v).
  - unfold preserve_vvalid in H1. apply H1, Hv_valid_v.
  - assert ( BinaryTree.vvalid Z Z bt2 yr).
    + unfold preserve_vvalid in H1. apply H1, Hv_valid_yr.
    + assert (BinaryTree.step_r bt2 yr v).
      -- destruct H3 as [H5[H6]].
         unfold preserve_evalid in H2.
         apply H3 in H_step.
         simpl in H_step.
         assert ((if Z.eq_dec v v
         then yr
         else if Z.eq_dec v yr then v else v) = yr) by apply simplify_if.
         assert ((if Z.eq_dec yr v
         then yr
         else if Z.eq_dec yr yr then v else yr) = v) by apply simplify_if2.
         rewrite H7, H8 in H_step.
         apply H_step.
      -- split.
      Admitted.
         (* exists v.
         assert ((exists yr0 : Z,
         BinaryTree.step_r bt2 v yr0 /\
         (v > yr0)%Z /\
         (forall yl : Z,
          BinaryTree.step_l bt2 v yl -> (v <= yl)%Z))).
          ---
         apply H.
         destruct.
      * exists v.
        split.
        -- apply H.
        -- split.
           ++ apply H0.
           ++ intros B1.
              assert (BinaryTree.vvalid Z Z bt2 yr).
              ** apply H, Hv_valid_yr.
              ** assert (v > yr)%Z by tauto.
                 assert (BinaryTree.step_r bt2 v yr).
                 ---apply H_step, .
                    left.
                 tauto.
                 exists yr.
                 assert ()
  split.
  apply NNPP.
  intro.
  destruct swap_nodes as [].
  - intros B0. destruct SH.
    destruct H.
    apply NNPP.
    intro.
    apply SH.   

  (* Now, we have the violation node v' and its properties. *)
  apply v in v'.
  (* destruct Hx as [H_valid_x [H_step_r_and_gt H_other_x]]. *)

  destruct (classic (v = x)) as [H_eq_v | H_diff].
  unfold swap_nodes in H_swap.
  destruct H_swap as [].
  destruct H0 as [].
  destruct H1 as [].
  -
    split.
    exists v.

    intros B1.
    assert (BinaryTree.vvalid Z Z bt2 yr).
    -- apply H, Hv_valid_yr.
    -- assert (v > yr)%Z by tauto.
       assert (BinaryTree.step_r bt2 v yr).
       ---apply H_step, .
          left.
       tauto.
       exists yr.
       assert ()
    
    -- tauto.
    exists yr. *)
 (** ----------------------------------------------------- **)
 (**   辅助引理2: 处理 StrictPartialHeap3 交换后的情况   **)
 (** ----------------------------------------------------- **)
 
Lemma preserve_partial_heap_after_swap_strict3_2:
  forall bt1 bt2 (v yr : Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    StrictPartialHeap3 bt1 ->
    (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
    BinaryTree.vvalid Z Z bt1 v ->
    BinaryTree.vvalid Z Z bt1 yr ->
    BinaryTree.step_r bt1 v yr ->
    (v > yr)%Z ->
    (swap_nodes v yr) bt1 tt bt2 ->
    (* 结论：交换后 bt2 仍然是 PartialHeap *)
    PartialHeap bt2.
Proof.
(* intros bt1 bt2 v yr H_heap Hv_valid_v Hv_valid_yr H_step H_gt H_swap.

destruct H_heap as [v' [Hv_valid' [H_step_r_or_l [H_gt' H_other]]]].

(* Now, we have the violation node v' and its properties. *)
destruct v' as [x Hx].
destruct Hx as [H_valid_x [H_step_r_and_gt H_other_x]].

destruct (classic (v = x)) as [H_eq_v | H_diff].
unfold swap_nodes in H_swap.
destruct H_swap as [].
destruct H0 as [].
destruct H1 as [].
destruct H2 as [].

- 
  split.
  intros v1 v2 [H_valid_v1 H_step_v1] [H_valid_v2 H_step_v2].

  (* 进一步分解存在量词 *)
  destruct H_step_v1 as [y1 [H_step_v1' H_gt_v1_y1]].
  destruct H_step_v2 as [y2 [H_step_v2' H_gt_v2_y2]].

  apply H.
  
(* Case 2: If the violation occurs between different nodes, we rely on the uniqueness property. *)
- (* The uniqueness of the violation in StrictPartialHeap3 implies no new violation can occur. *)
apply H_other.
Qed. *)
Admitted.
 
 (** ----------------------------------------------------- **)
 (**   主定理: move_up_in_partial_heap 后仍是 PartialHeap  **)
 (** ----------------------------------------------------- **)
 
 Theorem move_up_in_partial_heap_preserves_partial_heap:
   forall bt1 bt2,
     PartialHeap bt1 ->
     move_up_in_partial_heap bt1 tt bt2 ->
     PartialHeap bt2.
 Proof.
Admitted.

Theorem move_down_in_partial_heap_preserves_partial_heap:
  forall bt1 bt2,
    PartialHeap bt1 ->
    move_down_in_partial_heap bt1 tt bt2 ->
    PartialHeap bt2.
Proof.
Admitted.

(** ----------------------------------------------------- **)
(**  集合不变性  **)
(** ----------------------------------------------------- **)

Theorem move_up_in_partial_heap_preserves_set_of_nodes:
  forall bt1 bt2 X,
    PartialHeap bt1 ->
    move_up_in_partial_heap bt1 tt bt2 ->
    Abs bt1 X ->
    Abs bt2 X.
Proof.
Admitted.

Theorem move_down_in_partial_heap_preserves_set_of_nodes:
  forall bt1 bt2 X,
    PartialHeap bt1 ->
    move_down_in_partial_heap bt1 tt bt2 ->
    Abs bt1 X ->
    Abs bt2 X.
Proof.
Admitted.

(** ----------------------------------------------------- **)
(** ----------------------------------------------------- **)
(** level 2 3 **)
(** ----------------------------------------------------- **)
(** ----------------------------------------------------- **)
 
Require Import Classical.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.

Inductive Depth (bt: BinTree Z Z): Z -> Z -> Prop :=
  | depth_invalid: 
      forall v,
      ~BinaryTree.vvalid Z Z bt v -> 
      Depth bt v 0
  | depth_leaf:
      forall v,
      BinaryTree.vvalid Z Z bt v ->
      (forall y, ~BinaryTree.step_l bt v y) ->
      (forall y, ~BinaryTree.step_r bt v y) ->
      Depth bt v 1
  | depth_left:
      forall v cl d1,
      BinaryTree.vvalid Z Z bt v ->
      BinaryTree.step_l bt v cl ->
      (~exists cr, BinaryTree.step_r bt v cr) ->
      Depth bt cl d1 ->
      Depth bt v (d1 + 1%Z)
  | depth_right:
      forall v cr d1,
      BinaryTree.vvalid Z Z bt v ->
      BinaryTree.step_r bt v cr ->
      (~exists cl, BinaryTree.step_l bt v cl) ->
      Depth bt cr d1 ->
      Depth bt v (d1 + 1%Z)
  | depth_left_right:
      forall v cl cr d1 d2,
      BinaryTree.vvalid Z Z bt v ->
      BinaryTree.step_l bt v cl ->
      BinaryTree.step_r bt v cr ->
      Depth bt cl d1 ->
      Depth bt cr d2 ->
      Depth bt v ((Z.max d1 d2) + 1%Z).

Inductive Index (bt: BinTree Z Z): Z -> Z -> Prop :=
  | index_invalid: 
      forall v,
      ~BinaryTree.vvalid Z Z bt v -> 
      Index bt v 0
  | index_root:
      forall v,
      BinaryTree.vvalid Z Z bt v ->
      Root bt v ->
      Index bt v 1
  | index_left:
      forall v cl d1,
      BinaryTree.vvalid Z Z bt v ->
      BinaryTree.step_l bt v cl ->
      Index bt v d1 ->
      Index bt cl (2 * d1)
  | index_right:
      forall v cr d1,
      BinaryTree.vvalid Z Z bt v ->
      BinaryTree.step_r bt v cr ->
      Index bt v d1 ->
      Index bt cr (2 * d1 + 1%Z).


Inductive NumNodes (bt: BinTree Z Z): Z -> Z -> Prop :=
  | num_nodes_invalid:
      forall v,
      ~BinaryTree.vvalid Z Z bt v ->
      NumNodes bt v 0
  | num_nodes_leaf:
      forall v,
      BinaryTree.vvalid Z Z bt v ->
      (forall y, ~BinaryTree.step_l bt v y) ->
      (forall y, ~BinaryTree.step_r bt v y) ->
      NumNodes bt v 1
  | num_nodes_left:
    forall v cl n1,
    BinaryTree.vvalid Z Z bt v ->
    BinaryTree.step_l bt v cl ->
    (~exists cr, BinaryTree.step_r bt v cr) ->
    NumNodes bt cl n1 ->
    NumNodes bt v (n1 + 1%Z)
  | num_nodes_right:
    forall v cr n1,
    BinaryTree.vvalid Z Z bt v ->
    BinaryTree.step_r bt v cr ->
    (~exists cl, BinaryTree.step_l bt v cl) ->
    NumNodes bt cr n1 ->
    NumNodes bt v (n1 + 1%Z)
  | num_nodes_left_right:
    forall v cl cr n1 n2,
    BinaryTree.vvalid Z Z bt v ->
    BinaryTree.step_l bt v cl ->
    BinaryTree.step_r bt v cr ->
    NumNodes bt cl n1 ->
    NumNodes bt cr n2 ->
    NumNodes bt v (n1 + n2 + 1%Z).

Definition MaxIndex (bt: BinTree Z Z) (index: Z): Prop :=
  exists largest_v,
  Index bt largest_v index ->
  forall v index_v,
  v <> largest_v ->
  Index bt v index_v ->
  (index > index_v)%Z.

Record FullHeap (bt: BinTree Z Z) :=
  {
    full_heap_heap: Heap bt;
    full_heap_connected: bintree_connected bt;
    full_heap_full: exists root root_num max_index, 
      Root bt root /\
      NumNodes bt root root_num /\
      MaxIndex bt max_index /\
      max_index = root_num
  }.


(* Definition RemoveMin (bt: BinTree Z Z) (v: Z) (bt': BinTree Z Z): Prop :=
  exists root,
  Root bt root /\
  (forall v, BinaryTree.vvalid Z Z bt' v -> (v = root) \/ (exists y, BinaryTree.step_u bt v y)) *)



  