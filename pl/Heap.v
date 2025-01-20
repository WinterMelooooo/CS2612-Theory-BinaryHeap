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

Record legal_fs {V E: Type} (bt: BinaryTree V E): Prop :=
{
  ne_l:  forall y1 y2, step_l bt y1 y2 -> y1 <> y2;
  ne_r:  forall y1 y2, step_r bt y1 y2 -> y1 <> y2; 
  ne_childchild: forall y y1 y2, step_l bt y y1 -> step_r bt y y2 -> y1 <> y2;
}.

Record u_l_r {V E: Type} (bt: BinaryTree V E): Prop :=
{
  l_u:  forall y1 y2, step_l bt y1 y2 -> step_u bt y2 y1;
  r_u:  forall y1 y2, step_r bt y1 y2 -> step_u bt y2 y1;
  u_lr: forall y1 y2, step_u bt y1 y2 -> (step_l bt y2 y1 \/ step_r bt y2 y1);
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
Record Heap0 (h: BinTree Z Z): Prop := (*小顶堆*)
{
  heap_l0: forall x y: Z, BinaryTree.step_l h x y -> (x <= y)%Z;
  heap_r0: forall x y: Z, BinaryTree.step_r h x y -> (x <= y)%Z;
  heap_legality0: BinaryTree.legal h /\ BinaryTree.legal_fs h /\ BinaryTree.u_l_r h;
}.

Record Heap (h: BinTree Z Z): Prop := (*小顶堆*)
{
  heap_l: forall x y: Z, BinaryTree.step_l h x y -> (x < y)%Z;
  heap_r: forall x y: Z, BinaryTree.step_r h x y -> (x < y)%Z;
  heap_legality: BinaryTree.legal h /\ BinaryTree.legal_fs h /\ BinaryTree.u_l_r h;
}.

(** * 严格局部堆 *)
(** * leaf *)
Definition Leaf (V E: Type) (bt: BinTree V E) (v: V): Prop :=
  bt.(vvalid) v ->
  (~ exists y, BinaryTree.step_l bt v y) /\
  (~ exists y, BinaryTree.step_r bt v y).

Definition Node (V E: Type) (bt: BinTree V E) (v: V): Prop :=
  ~ Leaf V E bt v.

Definition Lson_only_Node (V E: Type) (bt: BinTree V E) (v: V): Prop :=
  (~ exists y, BinaryTree.step_r bt v y) /\ 
  exists yl, BinaryTree.step_l bt v yl .

Definition Rson_only_Node (V E: Type) (bt: BinTree V E) (v: V): Prop :=
  (~ exists y, BinaryTree.step_l bt v y) /\ 
  exists yr, BinaryTree.step_r bt v yr .

Definition Lson_Rson_Node (V E: Type) (bt: BinTree V E) (v: V): Prop :=
  (exists y, BinaryTree.step_l bt v y ) /\ 
  exists y', BinaryTree.step_r bt v y'.

Lemma Node_triple :
  forall (V E: Type) (bt: BinTree V E) (v: V),
    Node V E bt v  <-> Lson_only_Node V E bt v \/ Rson_only_Node V E bt v \/ Lson_Rson_Node V E bt v.
Proof.
intros V E bt v.
split.
- (* -> 方向: 如果是Node,那么一定属于三种情况之一 *)
  unfold Node, Leaf.
  unfold Lson_only_Node, Rson_only_Node, Lson_Rson_Node.
  intros H_node.
  apply NNPP. (* 使用双重否定消除 *)
  intro H_none.
  apply H_node.
  split.
  + (* 保持vvalid性质 *)
    intros H_valid.
    destruct H_valid as [yl H_left].
    destruct (classic (exists y, BinaryTree.step_r bt v y)) as [H_has_right | H_no_right].
    ++ (* 情况1: v 也有右孩子 *)
      destruct H_has_right as [yr H_right].
      apply H_none.
      right; right. (* 选择 Lson_Rson_Node 的情况 *)
      split.
      +++ exists yl; exact H_left.
      +++ exists yr; exact H_right.
    ++ (* 情况2: v 没有右孩子 *)
      apply H_none.
      left. (* 选择 Lson_only_Node 的情况 *)
      split.
      +++ exact H_no_right.
      +++ exists yl; exact H_left.
  + (* 证明没有子节点,这与Node定义矛盾 *)
  destruct (classic (exists y, BinaryTree.step_l bt v y)) as [H_has_left | H_no_left].
  ++ (* 情况1: v 有左孩子 *)
    destruct H_has_left as [yl H_left].
    intro H_has_right.
    destruct H_has_right as [yr H_right].
    apply H_none.
    right; right. (* 选择 Lson_Rson_Node 的情况 *)
    split.
    +++ (* 证明有左孩子 *)
      exists yl.
      exact H_left.
    +++ (* 证明有右孩子 *)
      exists yr.
      exact H_right.
  ++ intro H_has_right.
  destruct H_has_right as [yr H_right].
  apply H_none.
  right; left. (* 选择 Rson_only_Node 的情况 *)
  split.
  +++ (* 证明没有左孩子 *)
    exact H_no_left.
  +++ (* 证明有右孩子 *)
    exists yr.
    exact H_right.

- (* <- 方向: 如果属于三种情况之一,那么一定是Node *)
  intros [H_left | [H_right | H_both]].
  + (* Lson_only_Node的情况 *)
    unfold Node, Leaf.
    intro H.
    destruct (classic (bt.(vvalid) v)) as [H_valid | H_not_valid].
    ++ (* 情况1: v 是有效节点 *)
      specialize (H H_valid).
      destruct H as [H_no_left H_no_right'].
      apply H_no_left.
      unfold Lson_only_Node in H_left.
destruct H_left as [H_no_right [yl H_left]].
(* 现在我们有:
   H_no_right: ~ exists y, BinaryTree.step_r bt v y
   H_left: BinaryTree.step_l bt v yl *)

      exists yl.  (* 使用 yl 作为存在的左孩子 *)
      exact H_left.
    ++unfold Lson_only_Node in H_left.
    destruct H_left as [H_no_right [yl H_left]].
    (* 现在我们有:
       H_no_right: ~ exists y, BinaryTree.step_r bt v y
       H_left: BinaryTree.step_l bt v yl *)
    
    unfold BinaryTree.step_l in H_left.
    destruct H_left as [e [H_step_aux _]].
    destruct H_step_aux.
    (* step_src_valid 说明 v 是有效节点 *)
    contradiction.
  + (* Rson_only_Node 的情况 *)
  unfold Node, Leaf.
intro H.
unfold Rson_only_Node in H_right.
destruct H_right as [H_no_left [yr H_right]].
(* 现在我们有:
   H_no_left: ~ exists y, BinaryTree.step_l bt v y
   H_right: BinaryTree.step_r bt v yr *)

destruct (classic (bt.(vvalid) v)) as [H_valid | H_not_valid].
++ (* 情况1: v 是有效节点 *)
  specialize (H H_valid).
  destruct H as [H_no_left' H_no_right].
  (* 现在我们有:
     H_no_right: ~ exists y, BinaryTree.step_r bt v y
     但是我们也有:
     H_right: BinaryTree.step_r bt v yr *)
  apply H_no_right.
  exists yr.
  exact H_right.

++ (* 情况2: v 不是有效节点 *)
  (* 从 H_right 可以得到 v 必须是有效节点 *)
  unfold BinaryTree.step_r in H_right.
  destruct H_right as [e [H_step_aux _]].
  destruct H_step_aux.
  (* step_src_valid 说明 v 是有效节点 *)
  contradiction.

+ unfold Node, Leaf.
intro H.
unfold Lson_Rson_Node in H_both.
destruct H_both as [[yl H_left] [yr H_right]].
(* 现在我们有:
   H_left: BinaryTree.step_l bt v yl
   H_right: BinaryTree.step_r bt v yr *)

destruct (classic (bt.(vvalid) v)) as [H_valid | H_not_valid].
++ (* 情况1: v 是有效节点 *)
  specialize (H H_valid).
  destruct H as [H_no_left H_no_right].
  (* 现在我们有:
     H_no_left: ~ exists y, BinaryTree.step_l bt v y
     但是我们也有:
     H_left: BinaryTree.step_l bt v yl *)
  apply H_no_left.
  exists yl.
  exact H_left.

++ (* 情况2: v 不是有效节点 *)
  (* 从 H_left 可以得到 v 必须是有效节点 *)
  unfold BinaryTree.step_l in H_left.
  destruct H_left as [e [H_step_aux _]].
  destruct H_step_aux.
  (* step_src_valid 说明 v 是有效节点 *)
  contradiction.
Qed.
  

Definition Abs (h: BinTree Z Z) (X: Z -> Prop): Prop :=
  X == h.(vvalid).

Definition bintree_connected {V E: Type} (bt: BinTree V E): Prop :=
  exists root: V,
    bt.(vvalid) root /\
    (~ exists e, bt.(evalid) e /\ bt.(dst) e = root) /\
    (forall v, 
      bt.(vvalid) v -> 
      v <> root ->
      exists e, bt.(evalid) e /\ bt.(dst) e = v).





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
  partial_heap_legality: BinaryTree.legal h /\ BinaryTree.legal_fs h /\ BinaryTree.u_l_r h;
}.


Record StrictPartialHeap (h: BinTree Z Z): Prop := {
  (* 存在一个节点v违反堆的性质 *)
  exists_violation_strict: exists v: Z,
    (h.(vvalid) v /\ (* v必须是合法节点 *)
    exists y: Z, 
    ((BinaryTree.step_l h v y \/ BinaryTree.step_r h v y) /\ (v > y)%Z)) /\
    (
      forall v2: Z, (h.(vvalid) v /\ (* v必须是合法节点 *)
      exists y: Z, 
      ((BinaryTree.step_l h v2 y \/ BinaryTree.step_r h v2 y) /\ (v2 > y)%Z)) -> 
      (v2 = v)
    );
    strict_partial_heap_legality: BinaryTree.legal h /\ BinaryTree.legal_fs h /\ BinaryTree.u_l_r h;

}.

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
      (forall v2, (exists y2, ((BinaryTree.step_l h v2 y2 \/ BinaryTree.step_r h v2 y2) /\ (v2 > y2)%Z)) -> (v2 = v));
    strict_partial_heap1_legality: BinaryTree.legal h /\ BinaryTree.legal_fs h /\ BinaryTree.u_l_r h;
}.



Record StrictPartialHeap2 (h: BinTree Z Z): Prop := {
  forall_no_violation_right: forall v yr: Z,
    BinaryTree.step_r h v yr -> (v < yr)%Z;
  exists_violation_strict2: exists v yl: Z,
    (BinaryTree.step_l h v yl /\ 
      (v > yl)%Z) /\
    (forall v2, (exists yl2,  
      (BinaryTree.step_l h v2 yl2 /\ 
        (v2 > yl2)%Z)) -> (v2 = v));
  strict_partial_heap2_legality: BinaryTree.legal h /\ BinaryTree.legal_fs h /\ BinaryTree.u_l_r h;
}.

Record StrictPartialHeap3 (h: BinTree Z Z): Prop := {
  forall_no_violation_left: forall v yl: Z,
    BinaryTree.step_l h v yl -> (v < yl)%Z;
  exists_violation_strict3: exists v yr: Z,
    (* v必须有右孩子且大于右孩子，左孩子如果存在则不大于左孩子 *)
    (BinaryTree.step_r h v yr /\ 
      (v > yr)%Z) /\
    (* 其他所有节点都满足堆的性质 *)
    (forall v2,( exists yr2,  
    (BinaryTree.step_r h v2 yr2 /\ 
      (v2 > yr2)%Z))-> (v2 = v));
  strict_partial_heap3_legality: BinaryTree.legal h /\ BinaryTree.legal_fs h /\ BinaryTree.u_l_r h;
}.


Theorem strict_partial_heap_classification:
  forall h: BinTree Z Z,
    StrictPartialHeap h -> StrictPartialHeap1 h \/ StrictPartialHeap2 h \/ StrictPartialHeap3 h.
Proof.
intros.
destruct H.
destruct exists_violation_strict0.
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
    ++ tauto.
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
              ++++ destruct strict_partial_heap_legality0 as [l [m r]].
                   destruct m.
                   specialize (ne_r v yr).
                   apply ne_r in H4.
                   lia.
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
                   +++++ destruct strict_partial_heap_legality0 as [l [m r]].
                         destruct m.
                         specialize (ne_r v yr).
                         apply ne_r in H4.
                         lia.
                   
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
      ++ tauto.
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
    ++ tauto.
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
              ++++ destruct strict_partial_heap_legality0 as [l [m r]].
                   destruct m.
                   specialize (ne_r v yl).
                   apply ne_l in H4.
                   lia.
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
                   +++++ destruct strict_partial_heap_legality0 as [l [m r]].
                         destruct m.
                         specialize (ne_r v yl).
                         apply ne_l in H4.
                         lia.
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
      ++ tauto.
Qed.

Theorem inverse_strict_partial_heap_classification:
  forall h: BinTree Z Z,
    StrictPartialHeap1 h \/ StrictPartialHeap2 h \/ StrictPartialHeap3 h -> StrictPartialHeap h.
Proof.
  intros.
  split.
  destruct H as [H_S1 | [H_S2 | H_S3]].
  (*StrictPartialHeap1*)
  - destruct H_S1.
    destruct exists_violation_strict4.
    exists x. 
    split.
    + split.
      ++ tauto.
      ++ destruct H.
         destruct H.
         destruct H1 as [y1 [y2 H2] H1].
         exists y1.
         tauto.
    + intros v_eq.
      destruct H.
      specialize (H0 v_eq).
      intros.
      destruct H1.
      destruct H0.
      ++ destruct H2.
         exists x0.
         apply H0.
      ++ reflexivity.
  (*StrictPartialHeap2*)
  - destruct H_S2.
    destruct exists_violation_strict4.
    exists x.
    split.
    + split.
      ++ destruct H.
         destruct H.
         destruct H.
         destruct H.
         destruct H.
         destruct H.     
         tauto.
      ++ destruct H.
         exists x0.
         tauto.
    + intros.
      destruct H0.
      destruct H.
      destruct H.
      specialize (H2 v2).
      destruct H2.
      ++ destruct H1.
         exists x1.
         destruct H1 as [[H_l|H_r] H_gt].
         +++ tauto.
         +++ split.
             ++++ exfalso.
                  specialize (forall_no_violation_right0 v2 x1 H_r) as H_no_violation.
                  lia.
             ++++ tauto.             
      ++ reflexivity.
  (*StrictPartialHeap3*)
  - destruct H_S3.
    destruct exists_violation_strict4.
    exists x.
    split.
    + split.
      ++ destruct H.
         destruct H.
         destruct H.
         destruct H.
         destruct H.
         destruct H.     
         tauto.
      ++ destruct H.
         exists x0.
         tauto.
    + intros.
      destruct H0.
      destruct H.
      destruct H.
      specialize (H2 v2).
      destruct H2.
      ++ destruct H1.
         exists x1.
         destruct H1 as [[H_l|H_r] H_gt].
         +++ split.
            ++++ exfalso.
                  specialize (forall_no_violation_left0 v2 x1 H_l) as H_no_violation.
                  lia.
            ++++ tauto.    
         +++ tauto.
      ++ reflexivity.
  - destruct H as [l | [m | r]].
    + destruct l.
      tauto.
    + destruct m.
      tauto.
    + destruct r.
      tauto.
Qed.     


Theorem partial_heap_classification:
  forall h: BinTree Z Z,
    PartialHeap h -> StrictPartialHeap h \/ Heap h.
Proof.
Proof.
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
      + intros.
        specialize (exists_violation0 x v2).
        destruct exists_violation0.
        ++ tauto.
        ++ split.
           +++ destruct H0.
               destruct H1.
               destruct H1.
               destruct H1.
               destruct H1.
               destruct H1.
               destruct H1.
               ++++ tauto.
               ++++ destruct H1.
                    destruct H1.
                    destruct H1.
                    tauto.
               
           +++ destruct H0.
               tauto.
        ++ reflexivity.
      + destruct PH.
        tauto. 
    (*无局部破坏*)
    - right.
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
          +++ destruct PH.
              destruct partial_heap_legality0 as [l [m r]].
              destruct m.
              specialize (ne_l x y).
              apply ne_l in H0.
              lia.
              
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
          +++ destruct PH.
              destruct partial_heap_legality0 as [l [m r]].
              destruct m.
              specialize (ne_r x y).
              apply ne_r in H0.
              lia.
    + destruct PH.
      tauto.  
Qed.     


Theorem partial_heap_classification_detail:
  forall h: BinTree Z Z,
    PartialHeap h -> StrictPartialHeap1 h \/ StrictPartialHeap2 h \/ StrictPartialHeap3 h \/ Heap h.
Proof.
intros h H.
(* 首先应用 partial_heap_classification *)
apply partial_heap_classification in H.
destruct H as [H_strict | H_heap].

- (* 如果是 StrictPartialHeap *)
  (* 应用 strict_partial_heap_classification *)
  apply strict_partial_heap_classification in H_strict.
  destruct H_strict as [H1 | [H2 | H3]].
  + (* StrictPartialHeap1 的情况 *)
    left. exact H1.
  + (* StrictPartialHeap2 的情况 *)
    right. left. exact H2.
  + (* StrictPartialHeap3 的情况 *)
    right. right. left. exact H3.
    
- (* 如果是 Heap *)
  right. right. right. exact H_heap.
Qed.

Theorem inverse_partial_heap_classification:
  forall h: BinTree Z Z,
    StrictPartialHeap h \/ Heap h -> PartialHeap h.
    Proof.
    intros.
    split.
    destruct H as [H_S | H_H].
    (*Strict Partial Heap*)
    - destruct H_S.
      destruct exists_violation_strict0.
      intros.
      destruct H.
      transitivity x.
      + specialize (H2 v1).
        destruct H2.
        ++ tauto.
        ++ reflexivity.
      + specialize (H2 v2).
        destruct H2.
        ++ tauto.
        ++ reflexivity.
    (*Heap*)
    - destruct H_H.
      intros.
      exfalso.
      destruct H.
      destruct H1.
      destruct H1 as [[H_l | H_r] H_gt].
      + specialize (heap_l1 v1 x).
        apply heap_l1 in H_l.
        lia.
      + specialize (heap_r1 v1 x).
        apply heap_r1 in H_r.
        lia.
    - destruct h.
      destruct H.
      + destruct H.
        tauto.
      + destruct H.
        tauto.
  Qed.


  Theorem eq_PH_SHH:
  forall h: BinTree Z Z,
    PartialHeap h <-> StrictPartialHeap h \/ Heap h.
Proof.
  intros.
  split.
  apply partial_heap_classification.
  apply inverse_partial_heap_classification.
Qed.

Theorem eq_SH_SH123:
  forall h: BinTree Z Z,
    StrictPartialHeap h <-> StrictPartialHeap1 h \/ StrictPartialHeap2 h \/ StrictPartialHeap3 h.
Proof.
  intros.
  split.
  apply strict_partial_heap_classification.
  apply inverse_strict_partial_heap_classification.
Qed.


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
  
  Lemma simplify_if3 :
    forall (x v yr: Z),
      (x <> v) /\ (x <> yr) /\ (v <> yr) ->
      (if Z.eq_dec x v then yr else if Z.eq_dec x yr then v else x) = x.
  Proof.
    intros.
    destruct H. destruct H0.
    destruct (Z.eq_dec x v) as [H_eq_v | H_neq_v].
    - (* 这个分支不会被选中，因为 x <> v *)
      exfalso. apply H. exact H_eq_v.
    - destruct (Z.eq_dec x yr) as [H_eq_yr | H_neq_yr].
      --exfalso. apply H0. exact H_eq_yr.
      -- reflexivity.  
  Qed.

Theorem swap_nodes_eq:
  forall bt1 bt2 (v1 v2 : Z),
    (swap_nodes v1 v2) bt1 tt bt2 <->
    (swap_nodes v2 v1) bt1 tt bt2.
Proof.
intros.
split; intros H.

- (* -> 方向 *)
  destruct H as [H_vvalid [H_evalid [H_src [H_dst H_go]]]].
  split; [| split; [| split; [| split]]].
  + (* preserve_vvalid *)
    exact H_vvalid.
  + (* preserve_evalid *)
    exact H_evalid.
  + (* swap_src *)
    destruct H_src as [H_src [H_step_l H_step_r]].
    split; [| split].
    * (* 证明源节点交换 *)
      intros e.
      rewrite H_src.
      destruct (Z.eq_dec (BinaryTree.src _ _ bt1 e) v1);
      destruct (Z.eq_dec (BinaryTree.src _ _ bt1 e) v2);
      try lia; reflexivity.
    * (* 证明 step_l 关系 *)
    intros x y.
    split.
    
    (* -> 方向 *)
    ** intros H_step_l_bt1.
    apply H_step_l in H_step_l_bt1.
    (* 现在我们需要证明两个 if-then-else 表达式是等价的 *)
    assert (
      (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
      (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
    ).
    {
      destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
      - (* x = v1 且 x = v2 *)
        subst. reflexivity.
      - (* x = v1 且 x ≠ v2 *)
        reflexivity.
      - (* x ≠ v1 且 x = v2 *)
        reflexivity.
      - (* x ≠ v1 且 x ≠ v2 *)
        reflexivity.
    }
    
    assert (
      (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
      (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
    ).
    {
      destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
      - (* y = v1 且 y = v2 *)
        subst. reflexivity.
      - (* y = v1 且 y ≠ v2 *)
        reflexivity.
      - (* y ≠ v1 且 y = v2 *)
        reflexivity.
      - (* y ≠ v1 且 y ≠ v2 *)
        reflexivity.
    }
    
    rewrite <- H.
    rewrite <- H0.
    exact H_step_l_bt1.
    ** intros H_step_l_bt2.
    apply H_step_l.
    
    (* 首先证明源节点的 if-then-else 表达式等价性 *)
    assert (
      (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
      (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
    ).
    {
      destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
      - (* x = v1 且 x = v2 *)
        subst. reflexivity.
      - (* x = v1 且 x ≠ v2 *)
        reflexivity.
      - (* x ≠ v1 且 x = v2 *)
        reflexivity.
      - (* x ≠ v1 且 x ≠ v2 *)
        reflexivity.
    }
    
    (* 然后证明目标节点的 if-then-else 表达式等价性 *)
    assert (
      (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
      (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
    ).
    {
      destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
      - (* y = v1 且 y = v2 *)
        subst. reflexivity.
      - (* y = v1 且 y ≠ v2 *)
        reflexivity.
      - (* y ≠ v1 且 y = v2 *)
        reflexivity.
      - (* y ≠ v1 且 y ≠ v2 *)
        reflexivity.
    }
    rewrite H.
    rewrite H0.
    exact H_step_l_bt2.
  * (* swap_dst *)
      intros x y.
      split.
      
      (* -> 方向 *)
      ** intros H_step_r_bt1.
        apply H_step_r in H_step_r_bt1.
        assert (
          (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
          (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
        ).
        {
          destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
          - (* x = v1 且 x = v2 *)
            subst. reflexivity.
          - (* x = v1 且 x ≠ v2 *)
            reflexivity.
          - (* x ≠ v1 且 x = v2 *)
            reflexivity.
          - (* x ≠ v1 且 x ≠ v2 *)
            reflexivity.
        }
        
        assert (
          (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
          (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
        ).
        {
          destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
          - subst. reflexivity.
          - reflexivity.
          - reflexivity.
          - reflexivity.
        }
        
        rewrite H in H_step_r_bt1.
        rewrite H0 in H_step_r_bt1.
        exact H_step_r_bt1.
      
      (* <- 方向 *)
      ** intros H_step_r_bt2.
        apply H_step_r.
        assert (
          (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) =
          (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x)
        ).
        {
          destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
          - subst. reflexivity.
          - reflexivity.
          - reflexivity.
          - reflexivity.
        }
        
        assert (
          (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) =
          (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y)
        ).
        {
          destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
          - subst. reflexivity.
          - reflexivity.
          - reflexivity.
          - reflexivity.
        }
        
        rewrite H in H_step_r_bt2.
        rewrite H0 in H_step_r_bt2. 
        exact H_step_r_bt2.
  + (* go_left *)
      unfold swap_dst in *.
      intros e.
      rewrite H_dst.
      destruct (Z.eq_dec (BinaryTree.dst _ _ bt1 e) v1);
      destruct (Z.eq_dec (BinaryTree.dst _ _ bt1 e) v2).
      * (* dst = v1 且 dst = v2 *)
        subst. reflexivity.
      * (* dst = v1 且 dst ≠ v2 *)
        reflexivity.
      * (* dst ≠ v1 且 dst = v2 *)
        reflexivity.
      * (* dst ≠ v1 且 dst ≠ v2 *)
        reflexivity.
  + exact H_go.
- (* <- 方向 *)
  destruct H as [H_vvalid [H_evalid [H_src [H_dst H_go]]]].
  split; [| split; [| split; [| split]]].
  + (* preserve_vvalid *)
    exact H_vvalid.
  + (* preserve_evalid *)
    exact H_evalid.
  + (* swap_src *)
    destruct H_src as [H_src [H_step_l H_step_r]].
    split; [| split].
    * (* 证明源节点交换 *)
      intros e.
      rewrite H_src.
      destruct (Z.eq_dec (BinaryTree.src _ _ bt2 e) v2);
      destruct (Z.eq_dec (BinaryTree.src _ _ bt2 e) v1).
      ** (* src = v2 且 src = v1 *)
        subst. reflexivity.
      ** (* src = v2 且 src ≠ v1 *)
      destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) v1);
      destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) v2).
      *** (* src = v1 且 src = v2 *)
        subst. tauto.
      *** (* src = v1 且 src ≠ v2 *)
        reflexivity.
      *** (* src ≠ v1 且 src = v2 *)
        reflexivity.
      *** (* src ≠ v1 且 src ≠ v2 *)
        reflexivity.
      ** (* src = v2 且 src ≠ v1 *)
      destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) v1);
      destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) v2).
      *** (* src = v1 且 src = v2 *)
        subst. lia.
      *** (* src = v1 且 src ≠ v2 *)
        reflexivity.
      *** (* src ≠ v1 且 src = v2 *)
        reflexivity.
      *** (* src ≠ v1 且 src ≠ v2 *)
        reflexivity.
      ** (* src ≠ v2 且 src ≠ v1 *)
      destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) v1);
      destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) v2).
      *** (* src = v1 且 src = v2 *)
        subst. tauto.
      *** (* src = v1 且 src ≠ v2 *)
        reflexivity.
      *** (* src ≠ v1 且 src = v2 *)
        reflexivity.
      *** (* src ≠ v1 且 src ≠ v2 *)
        reflexivity.
    * (* 证明 step_l 关系 *)
      intros x y.
      split.
      
      (* -> 方向 *)
      ** intros H_step_l_bt1.
        apply H_step_l in H_step_l_bt1.
        (* 证明两个 if-then-else 表达式是等价的 *)
        
        (* 对于源节点 x *)
        assert (
          (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) =
          (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x)
        ).
        {
          destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
          - (* x = v1 且 x = v2 *)
            subst. tauto.
          - (* x = v1 且 x ≠ v2 *)
            reflexivity.
          - (* x ≠ v1 且 x = v2 *)
            reflexivity.
          - (* x ≠ v1 且 x ≠ v2 *)
            reflexivity.
        }
        rewrite H in H_step_l_bt1.
        
        (* 对于目标节点 y *)
        assert (
          (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) =
          (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y)
        ).
        {
          destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
          - subst. tauto.
          - reflexivity.
          - reflexivity.
          - reflexivity.
        }
        rewrite H0 in H_step_l_bt1.
        exact H_step_l_bt1.
      
      (* <- 方向 *)
      ** intros H_step_l_bt2.
        apply H_step_l.
        (* 证明两个 if-then-else 表达式是等价的 *)
        
        (* 对于源节点 x *)
        assert (
          (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
          (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
        ).
        {
          destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
          - subst. tauto.
          - reflexivity.
          - reflexivity.
          - reflexivity.
        }
        rewrite <- H.
        
        (* 对于目标节点 y *)
        assert (
          (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
          (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
        ).
        {
          destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
          - subst. tauto.
          - reflexivity.
          - reflexivity.
          - reflexivity.
        }
        rewrite <- H0.
        exact H_step_l_bt2.
    * (* 证明 step_r 关系 *)
    intros x y.
    split.
    
    (* -> 方向 *)
    ** intros H_step_r_bt1.
      apply H_step_r in H_step_r_bt1.
      (* 证明两个 if-then-else 表达式是等价的 *)
      
      (* 对于源节点 x *)
      assert (
        (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) =
        (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x)
      ).
      {
        destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
        - (* x = v1 且 x = v2 *)
          subst. tauto.
        - (* x = v1 且 x ≠ v2 *)
          reflexivity.
        - (* x ≠ v1 且 x = v2 *)
          reflexivity.
        - (* x ≠ v1 且 x ≠ v2 *)
          reflexivity.
      }
      rewrite H in H_step_r_bt1.
      
      (* 对于目标节点 y *)
      assert (
        (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) =
        (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y)
      ).
      {
        destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
        - subst. tauto.
        - reflexivity.
        - reflexivity.
        - reflexivity.
      }
      rewrite H0 in H_step_r_bt1.
      exact H_step_r_bt1.
    
    (* <- 方向 *)
    ** intros H_step_r_bt2.
      apply H_step_r.
      (* 证明两个 if-then-else 表达式是等价的 *)
      
      (* 对于源节点 x *)
      assert (
        (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
        (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
      ).
      {
        destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
        - subst. tauto.
        - reflexivity.
        - reflexivity.
        - reflexivity.
      }
      rewrite <- H.
      
      (* 对于目标节点 y *)
      assert (
        (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
        (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
      ).
      {
        destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
        - subst. tauto.
        - reflexivity.
        - reflexivity.
        - reflexivity.
      }
      rewrite <- H0.
      exact H_step_r_bt2.
  + (* swap_dst *)
    unfold swap_dst in *.
    intros e.
    rewrite H_dst.
    destruct (Z.eq_dec (BinaryTree.dst _ _ bt1 e) v2);
    destruct (Z.eq_dec (BinaryTree.dst _ _ bt1 e) v1).
    * (* dst = v2 且 dst = v1 *)
      subst. tauto.
    * (* dst = v2 且 dst ≠ v1 *)
      reflexivity.
    * (* dst ≠ v2 且 dst = v1 *)
      reflexivity.
    * (* dst ≠ v2 且 dst ≠ v1 *)
      reflexivity.
  + (* go_left *)
    tauto.
Qed.

Theorem swap_swap_nodes:
  forall bt1 bt2 (v1 v2 : Z),
    (swap_nodes v1 v2) bt2 tt bt1 ->
    (swap_nodes v1 v2) bt1 tt bt2.
Proof.
intros.
(* 使用swap_nodes_eq *)
apply swap_nodes_eq.
(* 现在我们需要证明(swap_nodes v1 v2) bt2 tt bt1 -> (swap_nodes v1 v2) bt1 tt bt2 *)

(* 分解假设 *)
destruct H as [H_vvalid [H_evalid [H_src [H_dst H_go]]]].
split; [| split; [| split; [| split]]].

(* 1. 证明preserve_vvalid *)
+ (* 由于vvalid是等价关系,所以可以直接使用对称性 *)
  unfold preserve_vvalid in *.
  unfold "==", Sets.equiv in *.
  unfold Sets.equiv in *.
  intros x.
  split; intros.
  - apply H_vvalid in H. exact H.
  - apply H_vvalid. exact H.

(* 2. 证明preserve_evalid *)
+ (* evalid也是等价关系 *)
  unfold preserve_evalid in *.
  unfold "==", Sets.equiv in *.
  unfold Sets.equiv in *.
  intros e.
  split; intros.
  - apply H_evalid in H. exact H.
  - apply H_evalid. exact H.

(* 3. 证明swap_src *)
+ (* 源节点交换的对称性 *)
  destruct H_src as [H_src [H_step_l H_step_r]].
  split; [| split].
  * (* 证明源节点交换 *)
    intros e.
    rewrite H_src.
    destruct (Z.eq_dec (BinaryTree.src _ _ bt2 e) v1);
    destruct (Z.eq_dec (BinaryTree.src _ _ bt2 e) v2).
    - subst. destruct (Z.eq_dec (BinaryTree.src Z Z bt2 e) (BinaryTree.src Z Z bt2 e)).
      -- (* 第一个分支: BinaryTree.src Z Z bt2 e = BinaryTree.src Z Z bt2 e *)
        reflexivity.
      -- (* 第二个分支: BinaryTree.src Z Z bt2 e ≠ BinaryTree.src Z Z bt2 e *)
        (* 这是一个矛盾,因为任何值都等于自身 *)
        contradiction n.
        reflexivity.
    - rewrite e0.
      destruct (Z.eq_dec v2 v1).
      -- (* Case: v2 = v1 *)
        exfalso. (* 这种情况不可能,因为如果v2 = v1,那么会与条件2矛盾 *)
        rewrite  e0 in n.
        rewrite e1 in n.
        contradiction.
      -- (* Case: v2 ≠ v1 *)
      destruct (Z.eq_dec v2 v2).
      --- (* Case: v2 = v2 *)
        reflexivity.
      --- (* Case: v2 ≠ v2 *)
        contradiction.
    - (* Case: v2 ≠ v1 *)
      destruct (Z.eq_dec v2 v2).
      -- (* Case: v2 = v2 *)
          rewrite e0.
          destruct (Z.eq_dec v1 v1).
          --- (* Case: v1 = v1 *)
          destruct (Z.eq_dec v1 v2).
          ---- (* Case: v1 = v2 *)
            exfalso. (* 这种情况不可能,因为如果v1 = v2,那么会与条件n矛盾 *)
            rewrite  e0 in n.
            rewrite e3 in n.
            contradiction.
          ---- (* Case: v1 ≠ v2 *)
            reflexivity.
          --- (* Case: v1 ≠ v1 *)
            contradiction.
      -- (* Case: v2 ≠ v2 *)
        contradiction.
    - destruct (Z.eq_dec (BinaryTree.src Z Z bt2 e) v1).
      -- (* Case: BinaryTree.src Z Z bt2 e = v1 *)
        contradiction.
      -- (* Case: BinaryTree.src Z Z bt2 e ≠ v1 *)
      destruct (Z.eq_dec (BinaryTree.src Z Z bt2 e) v2).
      --- (* Case: BinaryTree.src Z Z bt2 e = v2 *)
        contradiction.
      --- (* Case: BinaryTree.src Z Z bt2 e ≠ v2 *)
        reflexivity.
  * (* 证明step_l关系 *)
    intros x y.
    split; intros.
    -- apply H_step_l.

      (* 首先证明第一个复杂表达式等价于 x *)
      assert (H_eq1: 
        (if Z.eq_dec (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) v1
        then v2
        else
          if Z.eq_dec (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) v2
          then v1
          else if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) = x).
      {
        destruct (Z.eq_dec x v2); destruct (Z.eq_dec x v1).
        - (* x = v2 且 x = v1 *)
          subst. destruct (Z.eq_dec v1 v1).
          + reflexivity.
          + contradiction.
        - (* x = v2 且 x ≠ v1 *)
          destruct (Z.eq_dec v1 v1).
          + lia.
          + contradiction.
        - (* x ≠ v2 且 x = v1 *)
          destruct (Z.eq_dec v2 v1).
          + contradiction n. symmetry. 
            rewrite <- e in e0.
            lia.
          + destruct (Z.eq_dec v2 v2).
            * lia.
            * contradiction.
        - (* x ≠ v2 且 x ≠ v1 *)
          destruct (Z.eq_dec x v1).
          + contradiction.
          + destruct (Z.eq_dec x v2).
            * contradiction.
            * reflexivity.
      }

      (* 然后证明第二个复杂表达式等价于 y *)
      assert (H_eq2:
        (if Z.eq_dec (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) v1
        then v2
        else
          if Z.eq_dec (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) v2
          then v1
          else if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) = y).
      {
        destruct (Z.eq_dec y v2); destruct (Z.eq_dec y v1).
        - (* y = v2 且 y = v1 *)
          subst. destruct (Z.eq_dec v1 v1).
          + lia.
          + contradiction.
        - (* y = v2 且 y ≠ v1 *)
          destruct (Z.eq_dec v1 v1).
          + lia.
          + contradiction.
        - (* y ≠ v2 且 y = v1 *)
          destruct (Z.eq_dec v2 v1).
          + contradiction n. symmetry. 
          rewrite <- e in e0.
          lia.
          + destruct (Z.eq_dec v2 v2).
            * lia.
            * contradiction.
        - (* y ≠ v2 且 y ≠ v1 *)
          destruct (Z.eq_dec y v1).
          + contradiction.
          + destruct (Z.eq_dec y v2).
            * contradiction.
            * reflexivity.
      }

      rewrite H_eq1.
      rewrite H_eq2.
      exact H.
    --
        (* 使用H_step_l的<->关系，我们选择->方向 *)
        assert (H_forward := proj1 (H_step_l x y)).

        (* 首先证明源节点的 if-then-else 表达式等价性 *)
        assert (
          (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
          (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
        ).
        {
          destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
          - (* x = v1 且 x = v2 *)
            subst. reflexivity.
          - (* x = v1 且 x ≠ v2 *)
            reflexivity.
          - (* x ≠ v1 且 x = v2 *)
            reflexivity.
          - (* x ≠ v1 且 x ≠ v2 *)
            reflexivity.
        }

        (* 然后证明目标节点的 if-then-else 表达式等价性 *)
        assert (
          (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
          (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
        ).
        {
          destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
          - (* y = v1 且 y = v2 *)
            subst. reflexivity.
          - (* y = v1 且 y ≠ v2 *)
            reflexivity.
          - (* y ≠ v1 且 y = v2 *)
            reflexivity.
          - (* y ≠ v1 且 y ≠ v2 *)
            reflexivity.
        }
        rewrite <- H0 in H.
        rewrite <- H1 in H.
        (* 使用H_step_l的<->关系，我们选择<-方向 *)
        assert (H_back := proj2 (H_step_l x y)).
        (* 让我们专门化 H_step_l 到我们需要的情况 *)
        specialize (H_step_l (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
                            (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)).

        (* 首先证明第一个复杂表达式等价于 x *)
        assert (H_eq1: 
          (if Z.eq_dec (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) v1
          then v2
          else
            if Z.eq_dec (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) v2
            then v1
            else if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) = x).
        {
          destruct (Z.eq_dec x v2); destruct (Z.eq_dec x v1).
          - (* x = v2 且 x = v1 *)
            subst. destruct (Z.eq_dec v1 v1).
            + reflexivity.
            + contradiction.
          - (* x = v2 且 x ≠ v1 *)
            destruct (Z.eq_dec v1 v1).
            + lia.
            + contradiction.
          - (* x ≠ v2 且 x = v1 *)
            destruct (Z.eq_dec v2 v1).
            + contradiction n. symmetry. lia.
            + destruct (Z.eq_dec v2 v2).
              * lia.
              * contradiction.
          - (* x ≠ v2 且 x ≠ v1 *)
            destruct (Z.eq_dec x v1).
            + contradiction.
            + destruct (Z.eq_dec x v2).
              * contradiction.
              * reflexivity.
        }

        (* 然后证明第二个复杂表达式等价于 y *)
        assert (H_eq2:
          (if Z.eq_dec (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) v1
          then v2
          else
            if Z.eq_dec (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) v2
            then v1
            else if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) = y).
        {
          destruct (Z.eq_dec y v2); destruct (Z.eq_dec y v1).
          - (* y = v2 且 y = v1 *)
            subst. destruct (Z.eq_dec v1 v1).
            + reflexivity.
            + contradiction.
          - (* y = v2 且 y ≠ v1 *)
            destruct (Z.eq_dec v1 v1).
            + lia.
            + contradiction.
          - (* y ≠ v2 且 y = v1 *)
            destruct (Z.eq_dec v2 v1).
            + contradiction n. symmetry. lia.
            + destruct (Z.eq_dec v2 v2).
              * lia.
              * contradiction.
          - (* y ≠ v2 且 y ≠ v1 *)
            destruct (Z.eq_dec y v1).
            + contradiction.
            + destruct (Z.eq_dec y v2).
              * contradiction.
              * reflexivity.
        }

        (* 现在应用 H_step_l 的左到右方向 *)
        apply proj1 in H_step_l.
        rewrite H_eq1 in H_step_l.
        rewrite H_eq2 in H_step_l.
        apply H_step_l.
        rewrite <- H0.
        rewrite <- H1.
        exact H.
  * 
  intros x y.
  split.
  
  (* -> 方向 *)
  - intros H.
    (* 使用 H_step_r 的 <- 方向 *)
    assert (H_back := proj2 (H_step_r x y)).
    (* 首先证明源节点的 if-then-else 表达式等价性 *)
    assert (
      (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
      (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
    ).
    {
      destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
      - (* x = v1 且 x = v2 *)
        subst. reflexivity.
      - (* x = v1 且 x ≠ v2 *)
        reflexivity.
      - (* x ≠ v1 且 x = v2 *)
        reflexivity.
      - (* x ≠ v1 且 x ≠ v2 *)
        reflexivity.
    }

    (* 然后证明目标节点的 if-then-else 表达式等价性 *)
    assert (
      (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
      (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
    ).
    {
      destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
      - (* y = v1 且 y = v2 *)
        subst. reflexivity.
      - (* y = v1 且 y ≠ v2 *)
        reflexivity.
      - (* y ≠ v1 且 y = v2 *)
        reflexivity.
      - (* y ≠ v1 且 y ≠ v2 *)
        reflexivity.
    }

    (* 首先证明第一个复杂表达式等价于 x *)
    assert (H_eq1: 
    (if Z.eq_dec (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) v1
    then v2
    else
      if Z.eq_dec (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) v2
      then v1
      else if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x) = x).
    {
    destruct (Z.eq_dec x v2); destruct (Z.eq_dec x v1).
    - (* x = v2 且 x = v1 *)
      subst. destruct (Z.eq_dec v1 v1).
      + reflexivity.
      + contradiction.
    - (* x = v2 且 x ≠ v1 *)
      destruct (Z.eq_dec v1 v1).
      + lia.
      + contradiction.
    - (* x ≠ v2 且 x = v1 *)
      destruct (Z.eq_dec v2 v1).
      + contradiction n. symmetry. lia.
      + destruct (Z.eq_dec v2 v2).
        * lia.
        * contradiction.
    - (* x ≠ v2 且 x ≠ v1 *)
      destruct (Z.eq_dec x v1).
      + contradiction.
      + destruct (Z.eq_dec x v2).
        * contradiction.
        * reflexivity.
    }
    (* 然后证明第二个复杂表达式等价于 y *)
    assert (H_eq2:
      (if Z.eq_dec (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) v1
      then v2
      else
        if Z.eq_dec (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) v2
        then v1
        else if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y) = y).
    {
      destruct (Z.eq_dec y v2); destruct (Z.eq_dec y v1).
      - (* y = v2 且 y = v1 *)
        subst. destruct (Z.eq_dec v1 v1).
        + reflexivity.
        + contradiction.
      - (* y = v2 且 y ≠ v1 *)
        destruct (Z.eq_dec v1 v1).
        + lia.
        + contradiction.
      - (* y ≠ v2 且 y = v1 *)
        destruct (Z.eq_dec v2 v1).
        + contradiction n. symmetry. lia.
        + destruct (Z.eq_dec v2 v2).
          * lia.
          * contradiction.
      - (* y ≠ v2 且 y ≠ v1 *)
        destruct (Z.eq_dec y v1).
        + contradiction.
        + destruct (Z.eq_dec y v2).
          * contradiction.
          * reflexivity.
    }
    
    (* 首先证明源节点的 if-then-else 表达式等价性 *)
    assert (
      (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
      (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
    ).
    {
      destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
      - (* x = v1 且 x = v2 *)
        subst. reflexivity.
      - (* x = v1 且 x ≠ v2 *)
        reflexivity.
      - (* x ≠ v1 且 x = v2 *)
        reflexivity.
      - (* x ≠ v1 且 x ≠ v2 *)
        reflexivity.
    }
  
    (* 然后证明目标节点的 if-then-else 表达式等价性 *)
    assert (
      (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
      (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
    ).
    {
      destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
      - (* y = v1 且 y = v2 *)
        subst. reflexivity.
      - (* y = v1 且 y ≠ v2 *)
        reflexivity.
      - (* y ≠ v1 且 y = v2 *)
        reflexivity.
      - (* y ≠ v1 且 y ≠ v2 *)
        reflexivity.
    }
    rewrite <- H0.
    rewrite <- H1.
    assert (H_forward := proj1 (H_step_r x y)).
    specialize (H_step_r (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
                     (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)).
    apply proj1 in H_step_r.

    rewrite H_eq1 in H_step_r.
    rewrite H_eq2 in H_step_r.
    rewrite H0.
    rewrite H1.
    admit.
  
  (* <- 方向 *)
  - intros H.
    (* 使用 H_step_r 的 -> 方向 *)
    assert (H_forward := proj1 (H_step_r x y)).
    
    (* 首先证明源节点的 if-then-else 表达式等价性 *)
    assert (
      (if Z.eq_dec x v1 then v2 else if Z.eq_dec x v2 then v1 else x) =
      (if Z.eq_dec x v2 then v1 else if Z.eq_dec x v1 then v2 else x)
    ).
    {
      destruct (Z.eq_dec x v1); destruct (Z.eq_dec x v2).
      - (* x = v1 且 x = v2 *)
        subst. reflexivity.
      - (* x = v1 且 x ≠ v2 *)
        reflexivity.
      - (* x ≠ v1 且 x = v2 *)
        reflexivity.
      - (* x ≠ v1 且 x ≠ v2 *)
        reflexivity.
    }
  
    (* 然后证明目标节点的 if-then-else 表达式等价性 *)
    assert (
      (if Z.eq_dec y v1 then v2 else if Z.eq_dec y v2 then v1 else y) =
      (if Z.eq_dec y v2 then v1 else if Z.eq_dec y v1 then v2 else y)
    ).
    {
      destruct (Z.eq_dec y v1); destruct (Z.eq_dec y v2).
      - (* y = v1 且 y = v2 *)
        subst. reflexivity.
      - (* y = v1 且 y ≠ v2 *)
        reflexivity.
      - (* y ≠ v1 且 y = v2 *)
        reflexivity.
      - (* y ≠ v1 且 y ≠ v2 *)
        reflexivity.
    }
  
    rewrite <- H0 in H.
    rewrite <- H1 in H.
    admit.
(* 4. 证明swap_dst *)
+ (* 目标节点交换的对称性 *)
  unfold swap_dst in *.
  intros e.
  rewrite H_dst.
  admit.
(* 5. 证明go_left保持不变 *)
+ symmetry.
exact H_go.
Admitted.

Theorem swap_nodes_up_edge:
  forall bt1 bt2 (v parent : Z),
    BinaryTree.step_u bt1 v parent ->
    (swap_nodes v parent) bt1 tt bt2 ->
    BinaryTree.step_u bt2 parent v.
Proof.
intros.
destruct H0 as [H_evalid  H_src H_dst H_go].
unfold BinaryTree.step_u in *.
destruct H as [e [H_step_aux]].
exists e.

destruct H_src as [H_evalid' [H_src [H_dst H_go]]].
split.
- (* 证明边的有效性保持不变 *)
  unfold preserve_evalid in H_evalid'.
  unfold preserve_evalid in H_evalid'.
  unfold "==", Sets.equiv in H_evalid'.
  unfold Sets.equiv in H_evalid'.
(* 首先展开 lift_SETS 中的 equiv *)
unfold lift_SETS in H_evalid'.
simpl in H_evalid'.
(* 现在我们可以使用等价关系 *)
unfold Sets.lift_equiv in H_evalid'.
simpl in H_evalid'.
specialize (H_evalid' e).  (* 将全称量词具体化到e *)
unfold "==", Sets.equiv in H_evalid'.
destruct H_evalid' as [H_forward H_backward].
apply H_backward.  (* 使用反向蕴含关系 *)
exact H_step_aux.  (* 应用已知条件 *)
- (* 证明源节点的有效性 *)
  unfold preserve_vvalid in H_evalid.
  unfold "==", Sets.equiv in H_evalid.
  unfold Sets.equiv in H_evalid.
  simpl in H_evalid.
  specialize (H_evalid v).
  unfold "==", Sets.equiv in H_evalid.
  destruct H_evalid as [H_forward H_backward].
  (* 使用反向蕴含关系 *)
  apply H_backward.
  tauto.
- (* 证明目标节点的有效性 *)
  unfold preserve_vvalid in H_evalid.
  unfold "==", Sets.equiv in H_evalid.
  unfold Sets.equiv in H_evalid.
  simpl in H_evalid.
  specialize (H_evalid parent).
  unfold "==", Sets.equiv in H_evalid.
  destruct H_evalid as [H_forward H_backward].
  apply H_backward.
  tauto.
- (* 证明源节点关系 *)
  unfold swap_src in H_src.
  destruct H_src as [H_src _].
  rewrite H_src.
  rewrite step_src.
  destruct (Z.eq_dec parent v).
  + tauto. (* 如果 parent = v *)
  + destruct (Z.eq_dec parent parent).
    * (* 如果 parent = parent *)
      reflexivity.
    * (* 如果 parent ≠ parent *)
      contradiction.
- (* 证明目标节点关系 *)
  unfold swap_dst in H_dst.
  rewrite H_dst.
  rewrite step_dst.
  destruct (Z.eq_dec parent v).
  + apply simplify_if. (* 如果 parent = v *)
  + destruct (Z.eq_dec parent parent).
    * (* 如果 parent = parent *)
      apply simplify_if.
    * (* 如果 parent ≠ parent *)
      apply simplify_if.
Qed.


Theorem swap_nodes_left_edge:
  forall bt1 bt2 (v parent : Z),
    BinaryTree.step_l bt1 v parent ->
    (swap_nodes v parent) bt1 tt bt2 ->
    BinaryTree.step_l bt2 parent v.
Proof.
intros.
destruct H0 as [H_evalid  H_src H_dst H_go].
unfold BinaryTree.step_l in *.
destruct H as [e [H_step_aux]].
destruct H_src as [H_evalid' [H_src [H_dst H_go]]].
exists e.
split.
- (* 证明 step_aux 关系 *)
  destruct H_step_aux.
  split.
  + (* 证明边的有效性 *)
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    unfold Sets.equiv in H_evalid'.
    simpl in H_evalid'.
    specialize (H_evalid' e).
    unfold "==", Sets.equiv in H_evalid'.
    destruct H_evalid' as [H_forward H_backward].
    tauto.
  + (* 证明源节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    unfold "==", Sets.equiv in H_evalid.
    unfold Sets.equiv in H_evalid.
    simpl in H_evalid.
    specialize (H_evalid parent).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    tauto.
  
  + (* 证明目标节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    unfold "==", Sets.equiv in H_evalid.
    unfold Sets.equiv in H_evalid.
    simpl in H_evalid.
    specialize (H_evalid v).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    tauto.
  
  + (* 证明源节点关系 *)
    unfold swap_src in H_src.
    destruct H_src as [H_src _].
    rewrite H_src.
    rewrite step_src.
    destruct (Z.eq_dec parent v).
    ++ apply simplify_if. (* 如果 parent = v *)
    ++ apply simplify_if.
  
  + (* 证明目标节点关系 *)
    unfold swap_dst in H_dst.
    rewrite H_dst.
    rewrite step_dst.
    apply simplify_if2.

- (* 证明 go_left 关系 *)
  rewrite H_go.
  exact H.
Qed.


Theorem swap_nodes_right_edge:
  forall bt1 bt2 (v parent : Z),
    BinaryTree.step_r bt1 v parent ->
    (swap_nodes v parent) bt1 tt bt2 ->
    BinaryTree.step_r bt2 parent v.
Proof.
intros.
destruct H0 as [H_evalid  H_src H_dst H_go].
unfold BinaryTree.step_r in *.
destruct H as [e [H_step_aux]].
destruct H_src as [H_evalid' [H_src [H_dst H_go]]].
exists e.
split.
- (* 证明 step_aux 关系 *)
  destruct H_step_aux.
  split.
  + (* 证明边的有效性 *)
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    unfold Sets.equiv in H_evalid'.
    simpl in H_evalid'.
    specialize (H_evalid' e).
    unfold "==", Sets.equiv in H_evalid'.
    destruct H_evalid' as [H_forward H_backward].
    tauto.
  
  + (* 证明源节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    unfold "==", Sets.equiv in H_evalid.
    unfold Sets.equiv in H_evalid.
    simpl in H_evalid.
    specialize (H_evalid parent).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    tauto.
  
  + unfold preserve_vvalid in H_evalid.
    unfold "==", Sets.equiv in H_dst.
    unfold Sets.equiv in H_dst.
    simpl in H_dst.
    unfold "==" in H_evalid.
    specialize (H_evalid v).
    destruct H_evalid as [H_forward H_backward].
    tauto.
  + unfold swap_src in H_src.
    destruct H_src as [H_src _].

    rewrite H_src.
    rewrite step_src.
    apply simplify_if.
  + unfold swap_dst in H_dst.
    rewrite H_dst.
    rewrite step_dst.
    apply simplify_if2.
- (* 证明 go_right 关系 *)
  unfold BinaryTree.go_right.
  rewrite H_go.
  unfold BinaryTree.go_right in H.
  exact H.
Qed.


Theorem swap_nodes_other_same_l:
  forall bt1 bt2 (v1 v2 : Z),
    BinaryTree.legal_fs bt1 ->
    BinaryTree.u_l_r bt1 ->
    (BinaryTree.step_l bt1 v1 v2 \/ BinaryTree.step_r bt1 v1 v2 \/ BinaryTree.step_u bt1 v1 v2) ->
    (swap_nodes v1 v2) bt1 tt bt2 ->
    (forall v3 v4 : Z, v3 <> v1 -> v3 <> v2 -> v4 <> v1 -> v4 <> v2 -> BinaryTree.step_l bt1 v3 v4 -> BinaryTree.step_l bt2 v3 v4).
Proof.
intros.
destruct H2 as [H_evalid [H_evalid' [H_src [H_dst H_go]]]].
unfold BinaryTree.step_l in H7.
destruct H7 as [e [H_step_aux]].
exists e.
assert (v1 <> v2).
{
  destruct H1.
  + destruct H as [ne_l _ _].
    apply ne_l with (y1 := v1) (y2 := v2).
    tauto.
  + destruct H1.
    ++ destruct H as [_ ne_r _].
      apply ne_r with (y1 := v1) (y2 := v2).
      tauto.
    ++ destruct H as [ne_l ne_r _].
      destruct H0 as [_ _ u_lr].
      specialize (u_lr v1 v2).
      apply u_lr in H1.
      destruct H1 as [H_step_l | H_step_r].
      +++ specialize (ne_l v2 v1).
      apply ne_l in H_step_l.
      lia.
      +++ specialize (ne_r v2 v1).
      apply ne_r in H_step_r.
      lia.
}
split.
- (* 证明 step_aux 关系 *)
  split.
  + (* 证明边的有效性 *)
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    unfold Sets.equiv in H_evalid'.
    simpl in H_evalid'.
    specialize (H_evalid' e).
    unfold "==", Sets.equiv in H_evalid'.
    destruct H_evalid' as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  + (* 证明源节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v3).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    destruct H_step_aux.
    tauto.  
  + (* 证明目标节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v4).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点关系 *)
    unfold swap_src in H_src.
    destruct H_src as [H_src _].
    rewrite H_src.
    destruct H_step_aux.
    rewrite step_src.
    apply simplify_if3.
    split.
    ++ tauto.
    ++ split.
      * tauto.
      * lia.
  
  + (* 证明目标节点关系 *)
    unfold swap_dst in H_dst.
    rewrite H_dst.
    destruct H_step_aux.
    rewrite step_dst.
    apply simplify_if3.
    split.
    ++ tauto.
    ++ split.
      * tauto.
      * lia.

- (* 证明 go_left 关系 *)
  rewrite H_go.
  destruct H_step_aux.
  exact H2.
Qed.




Theorem swap_nodes_other_same_r:
  forall bt1 bt2 (v1 v2 : Z),
  BinaryTree.legal_fs bt1 ->
  BinaryTree.u_l_r bt1 ->
  (BinaryTree.step_l bt1 v1 v2 \/ BinaryTree.step_r bt1 v1 v2 \/ BinaryTree.step_u bt1 v1 v2) ->
    (swap_nodes v1 v2) bt1 tt bt2 ->
    (forall v3 v4 : Z, v3 <> v1 -> v3 <> v2 -> v4 <> v1 -> v4 <> v2 -> BinaryTree.step_r bt1 v3 v4 -> BinaryTree.step_r bt2 v3 v4).
Proof.
intros.
destruct H2 as [H_evalid [H_evalid' [H_src [H_dst H_go]]]].
unfold BinaryTree.step_r in H7.
destruct H7 as [e [H_step_aux]].
exists e.
assert (v1 <> v2).
{
  destruct H1.
  + destruct H as [ne_l _ _].
    apply ne_l with (y1 := v1) (y2 := v2).
    tauto.
  + destruct H1.
    ++ destruct H as [_ ne_r _].
        apply ne_r with (y1 := v1) (y2 := v2).
        tauto.
    ++ destruct H as [ne_l ne_r _].
        destruct H0 as [_ _ u_lr].
        specialize (u_lr v1 v2).
        apply u_lr in H1.
        destruct H1 as [H_step_l | H_step_r].
        +++ specialize (ne_l v2 v1).
            apply ne_l in H_step_l.
            lia.
        +++ specialize (ne_r v2 v1).
            apply ne_r in H_step_r.
            lia.
}
split.
- (* 证明 step_aux 关系 *)
  split.
  + (* 证明边的有效性 *)
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    unfold Sets.equiv in H_evalid'.
    simpl in H_evalid'.
    specialize (H_evalid' e).
    unfold "==", Sets.equiv in H_evalid'.
    destruct H_evalid' as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v3).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明目标节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v4).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点关系 *)
    unfold swap_src in H_src.
    destruct H_src as [H_src _].
    rewrite H_src.
    destruct H_step_aux.
    rewrite step_src.
    apply simplify_if3.
    split; [exact H3 | split; [exact H4 | lia]].
  
  + (* 证明目标节点关系 *)
    unfold swap_dst in H_dst.
    rewrite H_dst.
    destruct H_step_aux.
    rewrite step_dst.
    apply simplify_if3.
    split.
    ++ tauto.
    ++ split.
      * tauto.
      * lia.

- (* 证明 go_right 关系 *)
  unfold BinaryTree.go_right.
  rewrite H_go.
  unfold BinaryTree.go_right in H_step_aux.
  destruct H_step_aux.
  exact H2.
Qed.


Theorem swap_nodes_other_same_u:
  forall bt1 bt2 (v1 v2 : Z),
  BinaryTree.legal_fs bt1 ->
  BinaryTree.u_l_r bt1 ->
  (BinaryTree.step_l bt1 v1 v2 \/ BinaryTree.step_r bt1 v1 v2 \/ BinaryTree.step_u bt1 v1 v2) ->
    (swap_nodes v1 v2) bt1 tt bt2 ->
    (forall v3 v4 : Z, v3 <> v1 -> v3 <> v2 -> v4 <> v1 -> v4 <> v2 -> BinaryTree.step_u bt1 v3 v4 -> BinaryTree.step_u bt2 v3 v4).
Proof.
  intros.
  destruct H2 as [H_evalid [H_evalid' [H_src [H_dst H_go]]]].
  unfold BinaryTree.step_u in H7.
  destruct H7 as [e [H_step_aux]].
  exists e.

  (* 首先证明 v1 ≠ v2 *)
  assert (v1 <> v2).
  {
    destruct H1.
    + destruct H as [ne_l _ _].
      apply ne_l with (y1 := v1) (y2 := v2).
      tauto.
    + destruct H1.
      ++ destruct H as [_ ne_r _].
          apply ne_r with (y1 := v1) (y2 := v2).
          tauto.
      ++ destruct H as [ne_l ne_r _].
          destruct H0 as [_ _ u_lr].
          specialize (u_lr v1 v2).
          apply u_lr in H1.
          destruct H1 as [H_step_l | H_step_r].
          +++ specialize (ne_l v2 v1).
              apply ne_l in H_step_l.
              lia.
          +++ specialize (ne_r v2 v1).
              apply ne_r in H_step_r.
              lia.
  }

  split.
  - (* 证明 step_aux 关系 *)
      unfold preserve_evalid in H_evalid'.
      unfold "==", Sets.equiv in H_evalid'.
      unfold Sets.equiv in H_evalid'.
      simpl in H_evalid'.
      specialize (H_evalid' e).
      unfold "==", Sets.equiv in H_evalid'.
      destruct H_evalid' as [H_forward H_backward].
      apply H_backward.
      tauto.  
  -  (* 证明源节点的有效性 *)
      unfold preserve_vvalid in H_evalid.
      specialize (H_evalid v4).
      unfold "==", Sets.equiv in H_evalid.
      destruct H_evalid as [H_forward H_backward].
      
      tauto.
    
  -  (* 证明目标节点的有效性 *)
      unfold preserve_vvalid in H_evalid.
      specialize (H_evalid v3).
      unfold "==", Sets.equiv in H_evalid.
      destruct H_evalid as [H_forward H_backward].
      tauto.
    
  -   (* 证明源节点关系 *)
      unfold swap_src in H_src.
      destruct H_src as [H_src _].
      rewrite H_src.
      rewrite step_src.
      apply simplify_if3.
      split.
      ++ tauto.
      ++ split.
          * tauto.
          * lia.
  - (* 证明目标节点关系 *)
      unfold swap_dst in H_dst.
      rewrite H_dst.
      rewrite step_dst.
      apply simplify_if3.
      split.
      ++ tauto.
      ++ split.
          * tauto.
          * lia.
Qed.

Theorem swap_nodes_one_same_l_father:
  forall bt1 bt2 (v1 v2 : Z),
  BinaryTree.legal_fs bt1 ->
  BinaryTree.u_l_r bt1 ->
  BinaryTree.step_u bt1 v2 v1 ->
    (swap_nodes v1 v2) bt1 tt bt2 ->
    (forall v3: Z, v3 <> v1 -> v3 <> v2 -> BinaryTree.step_l bt1 v3 v1 -> BinaryTree.step_l bt2 v3 v2).
Proof.
intros.
destruct H2 as [H_evalid [H_evalid' [H_src [H_dst H_go]]]].
unfold BinaryTree.step_l in H5.
destruct H5 as [e [H_step_aux]].
exists e.

(* 首先证明 v1 ≠ v2 *)
assert (v1 <> v2).
{
  destruct H as [ne_l ne_r _].
  destruct H0 as [_ _ u_lr].
  specialize (u_lr v2 v1).
  apply u_lr in H1.
  destruct H1 as [H_step_l | H_step_r].
  - specialize (ne_l v1 v2).
    apply ne_l in H_step_l.
    lia.
  - specialize (ne_r v1 v2).
    apply ne_r in H_step_r.
    lia.
}

split.
- (* 证明 step_aux 关系 *)
  split.
  + (* 证明边的有效性 *)
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    unfold Sets.equiv in H_evalid'.
    simpl in H_evalid'.
    specialize (H_evalid' e).
    unfold "==", Sets.equiv in H_evalid'.
    destruct H_evalid' as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v3).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明目标节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v2).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    unfold BinaryTree.step_u in H1.
    destruct H1.
    destruct H1.
    tauto.
  
  + (* 证明源节点关系 *)
    unfold swap_src in H_src.
    destruct H_src as [H_src _].
    rewrite H_src.
    destruct H_step_aux.
    rewrite step_src.
    apply simplify_if3.
    split.
    ++ tauto.
    ++ split.
      * tauto.
      * lia.
  + (* 证明目标节点关系 *)
    unfold swap_dst in H_dst.
    rewrite H_dst.
    destruct H_step_aux.
    rewrite step_dst.
    apply simplify_if.

- (* 证明 go_left 关系 *)
  rewrite H_go.
  destruct H_step_aux.
  exact H2.
Qed.

  
Theorem swap_nodes_one_same_r_father:
  forall bt1 bt2 (v1 v2 : Z),
  BinaryTree.legal_fs bt1 ->
  BinaryTree.u_l_r bt1 ->
  BinaryTree.step_u bt1 v2 v1 ->
    (swap_nodes v1 v2) bt1 tt bt2 ->
    (forall v3: Z, v3 <> v1 -> v3 <> v2 -> BinaryTree.step_r bt1 v3 v1 -> BinaryTree.step_r bt2 v3 v2).
Proof.
intros.
destruct H2 as [H_evalid [H_evalid' [H_src [H_dst H_go]]]].
unfold BinaryTree.step_r in H5.
destruct H5 as [e [H_step_aux]].
exists e.

(* 首先证明 v1 ≠ v2 *)
assert (v1 <> v2).
{
  destruct H as [ne_l ne_r _].
  destruct H0 as [_ _ u_lr].
  specialize (u_lr v2 v1).
  apply u_lr in H1.
  destruct H1 as [H_step_l | H_step_r].
  - specialize (ne_l v1 v2).
    apply ne_l in H_step_l.
    lia.
  - specialize (ne_r v1 v2).
    apply ne_r in H_step_r.
    lia.
}

split.
- (* 证明 step_aux 关系 *)
  split.
  + (* 证明边的有效性 *)
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    unfold Sets.equiv in H_evalid'.
    simpl in H_evalid'.
    specialize (H_evalid' e).
    unfold "==", Sets.equiv in H_evalid'.
    destruct H_evalid' as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v3).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明目标节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v2).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    unfold BinaryTree.step_u in H1.
    destruct H1.
    destruct H1.
    tauto.
  
  + (* 证明源节点关系 *)
    unfold swap_src in H_src.
    destruct H_src as [H_src _].
    rewrite H_src.
    destruct H_step_aux.
    rewrite step_src.
    apply simplify_if3.
    split.
    ++ tauto.
    ++ split.
      * tauto.
      * lia.
  
  + (* 证明目标节点关系 *)
    unfold swap_dst in H_dst.
    rewrite H_dst.
    destruct H_step_aux.
    rewrite step_dst.
    apply simplify_if.

- (* 证明 go_right 关系 *)
  unfold BinaryTree.go_right.
  rewrite H_go.
  unfold BinaryTree.go_right in H_step_aux.
  destruct H_step_aux.
  exact H2.
Qed.

Theorem swap_nodes_one_same_r_child:
  forall bt1 bt2 (v1 v2 : Z),
  BinaryTree.legal_fs bt1 ->
  BinaryTree.u_l_r bt1 ->
  BinaryTree.step_u bt1 v2 v1 ->
    (swap_nodes v1 v2) bt1 tt bt2 ->
    (forall v3: Z, v3 <> v1 -> v3 <> v2 -> BinaryTree.step_r bt1 v2 v3 -> BinaryTree.step_r bt2 v1 v3).
Proof.
intros.
destruct H2 as [H_evalid [H_evalid' [H_src [H_dst H_go]]]].
unfold BinaryTree.step_r in H5.
destruct H5 as [e [H_step_aux]].
exists e.

(* 首先证明 v1 ≠ v2 *)
assert (v1 <> v2).
{
  destruct H as [ne_l ne_r _].
  destruct H0 as [_ _ u_lr].
  specialize (u_lr v2 v1).
  apply u_lr in H1.
  destruct H1 as [H_step_l | H_step_r].
  - specialize (ne_l v1 v2).
    apply ne_l in H_step_l.
    lia.
  - specialize (ne_r v1 v2).
    apply ne_r in H_step_r.
    lia.
}

split.
- (* 证明 step_aux 关系 *)
  split.
  + (* 证明边的有效性 *)
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    unfold Sets.equiv in H_evalid'.
    simpl in H_evalid'.
    specialize (H_evalid' e).
    unfold "==", Sets.equiv in H_evalid'.
    destruct H_evalid' as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v1).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    unfold BinaryTree.step_u in H1.
    destruct H1.
    destruct H1.
    tauto.
  
  + (* 证明目标节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v3).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点关系 *)
    unfold swap_src in H_src.
    destruct H_src as [H_src _].
    rewrite H_src.
    destruct H_step_aux.
    rewrite step_src.
    destruct (Z.eq_dec v2 v1).
    * exact e0.
    * destruct (Z.eq_dec v2 v2).
      -- reflexivity.
      -- contradiction.
  
  + (* 证明目标节点关系 *)
    unfold swap_dst in H_dst.
    rewrite H_dst.
    destruct H_step_aux.
    rewrite step_dst.
    apply simplify_if3.
    split.
    ++ tauto.
    ++ split.
      * tauto.
      * lia.

- (* 证明 go_right 关系 *)
  unfold BinaryTree.go_right.
  rewrite H_go.
  unfold BinaryTree.go_right in H_step_aux.
  destruct H_step_aux.
  exact H2.
Qed.

Theorem swap_nodes_one_same_l_child:
  forall bt1 bt2 (v1 v2 : Z),
  BinaryTree.legal_fs bt1 ->
  BinaryTree.u_l_r bt1 ->
  BinaryTree.step_u bt1 v2 v1 ->
    (swap_nodes v1 v2) bt1 tt bt2 ->
    (forall v3: Z, v3 <> v1 -> v3 <> v2 -> BinaryTree.step_l bt1 v2 v3 -> BinaryTree.step_l bt2 v1 v3).
Proof.
intros.
destruct H2 as [H_evalid [H_evalid' [H_src [H_dst H_go]]]].
unfold BinaryTree.step_l in H5.
destruct H5 as [e [H_step_aux]].
exists e.

(* 首先证明 v1 ≠ v2 *)
assert (v1 <> v2).
{
  destruct H as [ne_l ne_r _].
  destruct H0 as [_ _ u_lr].
  specialize (u_lr v2 v1).
  apply u_lr in H1.
  destruct H1 as [H_step_l | H_step_r].
  - specialize (ne_l v1 v2).
    apply ne_l in H_step_l.
    lia.
  - specialize (ne_r v1 v2).
    apply ne_r in H_step_r.
    lia.
}

split.
- (* 证明 step_aux 关系 *)
  split.
  + (* 证明边的有效性 *)
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    unfold Sets.equiv in H_evalid'.
    simpl in H_evalid'.
    specialize (H_evalid' e).
    unfold "==", Sets.equiv in H_evalid'.
    destruct H_evalid' as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v1).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    unfold BinaryTree.step_u in H1.
    destruct H1.
    destruct H1.
    tauto.
  
  + (* 证明目标节点的有效性 *)
    unfold preserve_vvalid in H_evalid.
    specialize (H_evalid v3).
    unfold "==", Sets.equiv in H_evalid.
    destruct H_evalid as [H_forward H_backward].
    destruct H_step_aux.
    tauto.
  
  + (* 证明源节点关系 *)
    unfold swap_src in H_src.
    destruct H_src as [H_src _].
    rewrite H_src.
    destruct H_step_aux.
    rewrite step_src.
    destruct (Z.eq_dec v2 v1).
    * exact e0.
    * destruct (Z.eq_dec v2 v2).
      -- reflexivity.
      -- contradiction.
  
  + (* 证明目标节点关系 *)
    unfold swap_dst in H_dst.
    rewrite H_dst.
    destruct H_step_aux.
    rewrite step_dst.
    apply simplify_if3.
    split.
    ++ tauto.
    ++ split.
      * tauto.
      * lia.

- (* 证明 go_left 关系 *)
  rewrite H_go.
  destruct H_step_aux.
  exact H2.
Qed.



Definition move_up (v: Z): StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
    (* 检查节点 v 是合法的 *)
 (
    (* 存在父节点 parent *)
    exists parent, BinaryTree.step_u bt1 v parent ->
      (* 使用新的 swap_nodes_rel 交换节点 *)
      (swap_nodes v parent) bt1 tt bt2).

Definition move_down (v: Z): StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
(
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
        BinaryTree.step_l bt1 v yl /\ (v > yl)%Z /\
        (swap_nodes v yl) bt1 tt bt2) \/
    (* 如果是 StrictPartialHeap3，类似处理 *)
    (StrictPartialHeap3 bt1 /\
      exists v yr,
        (* 从 StrictPartialHeap3 的定义中获取违反性质的节点 v *)
        BinaryTree.step_r bt1 v yr /\ (v > yr)%Z /\
        (forall yl, BinaryTree.step_l bt1 v yl -> (v < yl)%Z) /\
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
        BinaryTree.step_l bt1 v yl /\ 
        BinaryTree.step_r bt1 v yr /\ 
        (v > yl)%Z /\ 
        (v > yr)%Z /\
        (* 选择较小的子节点进行交换 *)
        ((yl < yr)%Z /\ (swap_nodes v yl) bt1 tt bt2 \/
          (yr < yl)%Z /\ (swap_nodes v yr) bt1 tt bt2)) \/
    (* 如果是 StrictPartialHeap2，交换 v 和其左子节点 *)
    (StrictPartialHeap2 bt1 /\
      exists v yl,
        BinaryTree.step_l bt1 v yl /\
        (v > yl)%Z /\
        (forall yr, BinaryTree.step_r bt1 v yr -> (v < yr)%Z) /\
        (swap_nodes v yl) bt1 tt bt2) \/
    (* 如果是 StrictPartialHeap3，交换 v 和其右子节点 *)
    (StrictPartialHeap3 bt1 /\
      exists v yr,
        BinaryTree.step_r bt1 v yr /\
        (v > yr)%Z /\
        (forall yl, BinaryTree.step_l bt1 v yl -> (v < yl)%Z) /\
        (swap_nodes v yr) bt1 tt bt2)).
 

Lemma preserve_legality_after_swap:
  forall bt1 bt2 (v yr : Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    StrictPartialHeap3 bt1 ->
    (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
    BinaryTree.step_r bt1 v yr ->
    (swap_nodes v yr) bt1 tt bt2 ->
    (* 结论：交换后 bt2 仍然是 PartialHeap *)
    BinaryTree.legal bt2 /\ BinaryTree.legal_fs bt2 /\ BinaryTree.u_l_r bt2.
Proof.
intros bt1 bt2 v yr H_sph3 H_step H_swap.

(* 首先解构 StrictPartialHeap3 的定义 *)
destruct H_sph3 as [_ _ H_legality].
destruct H_legality as [H_legal H_legal_fs H_ulr].
Print swap_swap_nodes.
apply swap_swap_nodes in H_swap as H_swap2.
(* 我们需要证明三个性质 *)
split; [| split].
destruct H_legal as [H_l_unique H_r_unique H_u_unique].
  constructor; intros.

(* 我们需要使用 H_step_l 的反方向，找到在 bt1 中对应的节点 *)
assert (exists x_orig y1_orig,
  x = (if Z.eq_dec x_orig v then yr
       else if Z.eq_dec x_orig yr then v
       else x_orig) /\
  y1 = (if Z.eq_dec y1_orig v then yr
        else if Z.eq_dec y1_orig yr then v
        else y1_orig) /\
  BinaryTree.step_l bt1 x_orig y1_orig).
{
  (* 目标: 存在原始节点 *)
  exists (if Z.eq_dec x yr 
          then v 
          else if Z.eq_dec x v 
              then yr 
              else x),
         (if Z.eq_dec y1 yr 
          then v 
          else if Z.eq_dec y1 v 
              then yr 
              else y1).
  split; [| split].
  - (* 证明 x 的等式 *)
    destruct (Z.eq_dec x yr).
    + (* x = yr *)
      subst x.
      destruct (Z.eq_dec v v).
      * reflexivity.
      * contradiction n. reflexivity.
    + (* x ≠ yr *)
      destruct (Z.eq_dec x v).
      * (* x = v *)
        subst x.
        destruct (Z.eq_dec yr v).
        ** (* Case 1: yr = v *)
          lia.  (* 这与假设 n: v <> yr 矛盾 *)
        ** (* Case 2: yr ≠ v *)
        destruct (Z.eq_dec yr yr).
        --- reflexivity.  (* if-then-else 表达式返回 v *)
        --- contradiction.  (* 这种情况是不可能的，因为 yr = yr 总是成立 *)
      * (* x ≠ v 且 x ≠ yr *)
          destruct (Z.eq_dec x v).
          ** (* Case 1: x = v *)
            contradiction n0.  (* 这与假设 n0: x <> v 矛盾 *)
          ** (* Case 2: x ≠ v *)
            destruct (Z.eq_dec x yr).
            *** (* Case 2.1: x = yr *)
              contradiction n.  (* 这与假设 n: x <> yr 矛盾 *)
            *** (* Case 2.2: x ≠ yr *)
              reflexivity.  (* if-then-else 表达式返回 x *)
    
  - (* 证明 y1 的等式，类似上面的证明 *)
  destruct (Z.eq_dec y1 yr); destruct (Z.eq_dec y1 v).

  -- (* Case 1: y1 = yr 且 y1 = v *)
    subst. (* 这种情况是矛盾的，因为 yr = v *)
    destruct (Z.eq_dec v v).
    + reflexivity.
    + contradiction.
  
  -- (* Case 2: y1 = yr 且 y1 ≠ v *)
    (* 此时内层表达式为 v *)
    destruct (Z.eq_dec v v).
    + (* v = v *)
      destruct (Z.eq_dec v yr).
      * (* v = yr，与 y1 ≠ v 矛盾 *)
        subst. contradiction n.
      * tauto.
    + (* v ≠ v，矛盾 *)
      destruct (Z.eq_dec v yr).
      * tauto.
      * tauto.   
  -- (* Case 3: y1 ≠ yr 且 y1 = v *)
    (* 此时内层表达式为 yr *)
    destruct (Z.eq_dec yr v).
    + (* yr = v，与 y1 ≠ yr 矛盾 *)
      subst. contradiction n.
      reflexivity.
    + destruct (Z.eq_dec yr yr).
      * tauto.
      * contradiction.
  -- (* Case 4: y1 ≠ yr 且 y1 ≠ v *)
    (* 此时内层表达式为 y1 *)
    destruct (Z.eq_dec y1 v).
    + contradiction.
    + destruct (Z.eq_dec y1 yr).
      * contradiction.
      * lia.
  - (* 使用 H_step_l 的反方向 *)
    (* 首先使用 H_swap2 的 step_l 关系 *)
    destruct H_swap2 as [_ [_ [_ [H_step_l _]]]].
    unfold swap_dst in H_step_l.
    destruct H as [e [H_step_aux]].
    exists e.
    split.
    --  destruct H_step_aux.
  split.
    --- (* 从 H_swap 中提取 preserve_evalid 性质 *)
    destruct H_swap as [_ [H_evalid' _]].
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    specialize (H_evalid' e).
    destruct H_evalid' as [H_forward H_backward].
    apply H_forward.
    exact step_evalid.
    ---  (* 从 H_swap 中提取 preserve_vvalid 性质 *)
    destruct H_swap as [H_vvalid [_ _]].
    unfold preserve_vvalid in H_vvalid.
    unfold "==", Sets.equiv in H_vvalid.
    
    (* 分析 x 是否等于 yr 或 v *)
    destruct (Z.eq_dec x yr).
    ---- (* Case 1: x = yr *)
      subst x.
      specialize (H_vvalid v).
      destruct H_vvalid as [H_forward H_backward].
      apply H_forward.
      (* 从 H_step 中我们知道 v 在 bt1 中是有效的 *)
      destruct H_step as [e' [H_step_aux]].
      destruct H_step_aux.

      (* 使用 H_backward 将 bt1 中的有效性转换到 bt2 *)
      apply H_backward.
      exact step_src_valid0.
    ---- (* Case 2: x ≠ yr *)
      destruct (Z.eq_dec x v).
      + (* Case 2.1: x = v *)
        subst x.
        specialize (H_vvalid yr).
        destruct H_vvalid as [H_forward H_backward].
        apply H_forward.
        (* 从 H_step 中我们知道 yr 在 bt1 中是有效的 *)
        destruct H_step as [e' [H_step_aux]].
        destruct H_step_aux.

        (* 使用 H_backward 将 bt1 中的有效性转换到 bt2 *)
        apply H_backward.
        tauto.      
      + (* Case 2.2: x ≠ v *)
        specialize (H_vvalid x).
        destruct H_vvalid as [H_forward H_backward].
        apply H_forward.
        exact step_src_valid. 
    ---(* 从 H_swap 中提取 preserve_vvalid 性质 *)
        destruct H_swap as [H_vvalid [_ _]].
        unfold preserve_vvalid in H_vvalid.
        unfold "==", Sets.equiv in H_vvalid.
        
        (* 分析 y1 是否等于 yr 或 v *)
        destruct (Z.eq_dec y1 yr).
        ---- (* Case 1: y1 = yr *)
          subst y1.
          specialize (H_vvalid v).
          destruct H_vvalid as [H_forward H_backward].
          apply H_forward.
          (* 从 H_step 中我们知道 v 在 bt1 中是有效的 *)
          destruct H_step as [e' [H_step_aux]].
          destruct H_step_aux.

          (* 使用 H_backward 将 bt1 中的有效性转换到 bt2 *)
          apply H_backward.
          tauto.
        ---- (* Case 2: y1 ≠ yr *)
          destruct (Z.eq_dec y1 v).
          + (* Case 2.1: y1 = v *)
            subst y1.
            specialize (H_vvalid yr).
            destruct H_vvalid as [H_forward H_backward].
            apply H_forward.
            destruct H_step as [e' [H_step_aux]].
            destruct H_step_aux.
            apply H_backward.
            tauto.
          
          + (* Case 2.2: y1 ≠ v *)
            specialize (H_vvalid y1).
            destruct H_vvalid as [H_forward H_backward].
            apply H_forward.
            exact step_dst_valid.
      --- (* 从 H_swap 中提取 swap_src 性质 *)
          destruct H_swap as [_ [_ [H_src [_ _]]]].
          unfold swap_src in H_src.
          (* 从 H_src 中提取源节点映射关系 *)
          destruct H_src as [H_src_map _].
          specialize (H_src_map e).

          (* 重写源节点等式 *)
          rewrite step_src in H_src_map.
          destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) v).
          ---- (* Case 1: BinaryTree.src Z Z bt1 e = v *)
            subst.
          (* 分析第一个条件：Z.eq_dec (BinaryTree.src Z Z bt2 e) (BinaryTree.src Z Z bt2 e) *)
          destruct (Z.eq_dec (BinaryTree.src Z Z bt2 e) (BinaryTree.src Z Z bt2 e)).
          ----- (* Case 1: BinaryTree.src Z Z bt2 e = BinaryTree.src Z Z bt2 e *)
            (* 这种情况总是成立 *)
            reflexivity.

          ----- (* Case 2: BinaryTree.src Z Z bt2 e ≠ BinaryTree.src Z Z bt2 e *)
            (* 这种情况是不可能的，因为每个值都等于自身 *)
            contradiction.
          
          ---- (* Case 2: BinaryTree.src Z Z bt1 e ≠ v *)
            destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) yr).
            + (* Case 2.1: BinaryTree.src Z Z bt1 e = yr *)
              subst.
              (* 分析第一个条件：Z.eq_dec (BinaryTree.src Z Z bt2 e) (BinaryTree.src Z Z bt1 e) *)
              destruct (Z.eq_dec (BinaryTree.src Z Z bt2 e) (BinaryTree.src Z Z bt1 e)).
              * (* Case 1: BinaryTree.src Z Z bt2 e = BinaryTree.src Z Z bt1 e *)
                (* 这与假设 n 矛盾 *)
                lia.

              * (* Case 2: BinaryTree.src Z Z bt2 e ≠ BinaryTree.src Z Z bt1 e *)
                (* 分析第二个条件：Z.eq_dec (BinaryTree.src Z Z bt2 e) (BinaryTree.src Z Z bt2 e) *)
                destruct (Z.eq_dec (BinaryTree.src Z Z bt2 e) (BinaryTree.src Z Z bt2 e)).
                ** (* Case 2.1: BinaryTree.src Z Z bt2 e = BinaryTree.src Z Z bt2 e *)
                  (* 这种情况总是成立 *)
                  reflexivity.
                ** (* Case 2.2: BinaryTree.src Z Z bt2 e ≠ BinaryTree.src Z Z bt2 e *)
                  (* 这种情况是不可能的，因为每个值都等于自身 *)
                  contradiction.
            + (* Case 2.2: BinaryTree.src Z Z bt1 e ≠ yr *)
              subst.
              (* 分析第一个条件：Z.eq_dec (BinaryTree.src Z Z bt1 e) yr *)
              destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) yr).
              * (* Case 1: BinaryTree.src Z Z bt1 e = yr *)
                (* 这与假设 n0 矛盾 *)
                contradiction.

              * (* Case 2: BinaryTree.src Z Z bt1 e ≠ yr *)
                (* 分析第二个条件：Z.eq_dec (BinaryTree.src Z Z bt1 e) v *)
                destruct (Z.eq_dec (BinaryTree.src Z Z bt1 e) v).
                ** (* Case 2.1: BinaryTree.src Z Z bt1 e = v *)
                  (* 这与假设 n 矛盾 *)
                  contradiction.
                ** (* Case 2.2: BinaryTree.src Z Z bt1 e ≠ v *)
                  (* 此时表达式返回 BinaryTree.src Z Z bt1 e *)
                  reflexivity.
        --- (* 使用 H_step_l 获取 bt1 中目标节点的表达式 *)
        specialize (H_step_l e).
        rewrite step_dst in H_step_l.
        
        (* 分析 y1 是否等于 v 或 yr *)
        destruct (Z.eq_dec y1 v).
        ---- (* Case 1: y1 = v *)
          subst y1.
          destruct (Z.eq_dec v yr).
          + (* Case 1.1: v = yr *)
            rewrite <- e0 in H_step_l.
            exact H_step_l.
          + (* Case 1.2: v ≠ yr *)
            destruct (Z.eq_dec v v).
            * tauto.
            * contradiction.
        ----exact H_step_l.
  -- destruct H_step_aux.
      (* 从 H_swap 中提取 preserve_evalid 性质 *)
      destruct H_swap as [_ [H_evalid' _]].
      unfold preserve_evalid in H_evalid'.
      unfold "==", Sets.equiv in H_evalid'.
      specialize (H_evalid' e).
      destruct H_evalid' as [H_forward H_backward].
      admit.
}
      - (* 证明边的有效性 *)
    destruct H_swap as [_ [H_evalid' _]].
    unfold preserve_evalid in H_evalid'.
    unfold "==", Sets.equiv in H_evalid'.
    simpl.
    admit.
  
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

 (** ----------------------------------------------------- **)
 (**   辅助引理1: 处理 StrictPartialHeap2 交换后的情况   **)
 (** ----------------------------------------------------- **)

 (* Lemma uni_strictheap3:
 forall bt1 (v yr : Z),
   StrictPartialHeap3 bt1 ->
   (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
   BinaryTree.vvalid Z Z bt1 v ->
   BinaryTree.vvalid Z Z bt1 yr ->
   BinaryTree.step_r bt1 v yr ->
   (v > yr)%Z ->
   (forall yl, BinaryTree.step_l bt1 v yl -> (v < yl)%Z) ->
   (BinaryTree.vvalid Z Z bt1 v ->
   (BinaryTree.vvalid Z Z bt1 v /\ (* v必须是合法节点 *)
    (* v必须有右孩子且大于右孩子，左孩子如果存在则不大于左孩子 *)
    (exists yr: Z,
      BinaryTree.step_r bt1 v yr /\ 
      (v > yr)%Z /\
      (forall yl: Z, 
        BinaryTree.step_l bt1 v yl -> 
        (v < yl)%Z)))).
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
     (v > yr)%Z /\ (forall yl : Z, BinaryTree.step_l bt1 v yl -> (v < yl)%Z))).
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
* (* forall yl : Z, BinaryTree.step_l bt1 v yl -> (v < yl)%Z *)
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
     * (* 证明 forall yl : Z, BinaryTree.step_l bt1 v yl -> (v < yl)%Z *)
       exact H4.
Qed. *)



(** 下面是需要的引理：交换后仍是PartialHeap **)


Lemma preserve_partial_heap_after_swap_strict2:
  forall bt1 bt2 (v yl : Z),
    StrictPartialHeap2 bt1 ->
    BinaryTree.step_l bt1 v yl ->
    (v > yl)%Z ->
    (swap_nodes v yl) bt1 tt bt2 ->
    PartialHeap bt2.
Proof.
Admitted.



 (** ----------------------------------------------------- **)
 (**   辅助引理2: 处理 StrictPartialHeap3 交换后的情况   **)
 (** ----------------------------------------------------- **)


Lemma strict3_property:
  forall (bt1 : BinTree Z Z) (v yr : Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    StrictPartialHeap3 bt1 ->
    BinaryTree.step_r bt1 v yr ->
    (forall v' yl : Z,
         BinaryTree.step_l bt1 v' yl -> (v' < yl)%Z) ->
    (v > yr)%Z ->
    (forall (v1 v2 : Z),
    v1 <> v ->
    v2 <> yr ->
    BinaryTree.step_r bt1 v1 v2 ->
    (v1 < v2)%Z).
Proof.
intros bt1 v yr H_heap H_step H_gt H_proper v1 v2  H_neq_v H_neq_yr H_step_r.
assert (BinaryTree.legal bt1) as H_legal.
{
  destruct H_heap.
  tauto.
}
assert (BinaryTree.legal_fs bt1) as H_legal_fs.
{
  destruct H_heap.
  tauto.
}

(* 解构 StrictPartialHeap3 的假设 *)
destruct H_heap as [H_partial_heap ].
intros.
apply NNPP.
intro.
assert ((v1 >= v2)%Z) by lia.
destruct exists_violation_strict4 as [].
destruct H1. destruct H1. destruct H1.
assert (v = x).
- specialize (H2 v).
  assert (exists yr2 : Z,
  BinaryTree.step_r bt1 v yr2/\ (v > yr2)%Z).
  -- exists yr. tauto.
  -- destruct H4.
    (* 构造存在性量词的命题 *)
    assert (H_exists : exists yr2 : Z,
    BinaryTree.step_r bt1 v yr2 /\
    (v > yr2)%Z).
  {
  exists x1.
  tauto.
  }
  specialize (H2 H_exists).
  tauto.
- assert (v1 = x).
 -- specialize (H2 v1).
    assert (exists yr2 : Z,
    BinaryTree.step_r bt1 v1 yr2/\ (v1 > yr2)%Z).
    --- exists v2.  
        destruct H_legal_fs.
        specialize (ne_r v1 v2).
        apply ne_r in H_step_r as H_new.
        assert ( v1 > v2)%Z by lia.
        tauto.
    --- destruct H4.
      (* 构造存在性量词的命题 *)
      assert (H_exists : exists yr2 : Z,
      BinaryTree.step_r bt1 v1 yr2 /\
      (v1 > yr2)%Z).
    {
    exists v2.
    tauto.
    }
    specialize (H2 H_exists).
    tauto.
  -- lia.
Qed.

(* 唯一性的定理 *)
Theorem uni:
  forall (bt1 : BinTree Z Z) (v x: Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    BinaryTree.legal bt1 ->
    BinaryTree.legal_fs bt1 ->
    (v = x) ->
    (forall v1: Z, BinaryTree.step_l bt1 v v1 -> BinaryTree.step_l bt1 x v1)
    /\ (forall v2: Z, BinaryTree.step_r bt1 v v2 -> BinaryTree.step_r bt1 x v2)
    /\ (forall v3: Z, BinaryTree.step_u bt1 v v3 -> BinaryTree.step_u bt1 x v3).
Proof.
intros.
split.
- intros.
subst.
exact H2.
- intros.
subst.
split.
-- intros.
  exact H1.
-- intros.
  exact H1.
Qed.


Lemma strict3_property2:
  forall (bt1 : BinTree Z Z) (v yr x: Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    StrictPartialHeap3 bt1 ->
    BinaryTree.legal bt1 ->
    BinaryTree.legal_fs bt1 ->
    BinaryTree.u_l_r bt1->
    BinaryTree.step_r bt1 v yr ->
    BinaryTree.step_l bt1 yr x ->
    (x <> v)%Z.
Proof.
intros.
destruct H1.
destruct H0.
apply NNPP. intro.
assert (v = x) by lia.
Admitted.

(* 如果他又右子，那么必有左子 *)
Lemma strict3_property3:
  forall (bt1 : BinTree Z Z) (v yr: Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    StrictPartialHeap3 bt1 ->
    BinaryTree.legal bt1 ->
    BinaryTree.legal_fs bt1 ->
    BinaryTree.u_l_r bt1->
    BinaryTree.step_r bt1 v yr ->
    (exists yl : Z, BinaryTree.step_l bt1 v yl).
Proof.
Admitted.

Lemma preserve_partial_heap_after_swap_strict3:
  forall bt1 bt2 (v yr : Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    StrictPartialHeap3 bt1 ->
    (* BinaryTree.legal_fs bt1 ->
    BinaryTree.legal_fs bt2 ->
    BinaryTree.u_l_r bt1->
    BinaryTree.u_l_r bt2->
    BinaryTree.legal bt1 ->
    BinaryTree.legal bt2 -> *)
    (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
    BinaryTree.step_r bt1 v yr ->
    (v > yr)%Z ->
    (swap_nodes v yr) bt1 tt bt2 ->
    (* 结论：交换后 bt2 仍然是 PartialHeap *)
    PartialHeap bt2.
Proof.
  intros bt1 bt2 v yr H_heap H_step H_gt H_swap.
  (* H_lefs1 H_lefs2 H_ulr1 H_ulr2 H_le1 H_le2 *)
  destruct H_heap as [SH].
  destruct strict_partial_heap3_legality0 as [H_le1].
  destruct H as [ H_lefs1 H_ulr1].
  assert(StrictPartialHeap3 bt1) as H_heap. 
  { 
    split. 
    tauto. 
  }
  specialize (preserve_legality_after_swap bt1 bt2 v yr ). 
  intros. 
  apply H in H_heap. 
  destruct H_heap as [H_le2].
  destruct H0 as [ H_lefs2 H_ulr2]. 
   (* 聚焦到第 2 个目标 BinaryTree.step_r bt1 v yr *)
  2 : apply H_step.
  2 : apply H_swap.

  unfold swap_nodes in H_swap.
  destruct H_swap as [H1[H2[H3[H4[]]]]].
  unfold swap_src in H3.
  unfold swap_dst in H4.
    + assert (BinaryTree.step_r bt2 yr v).
      -- destruct H3 as [H5[H6]].
         unfold preserve_evalid in H2.
         apply H0 in H_step as H_step_new.
         simpl in H_step.
         assert ((if Z.eq_dec v v
         then yr
         else if Z.eq_dec v yr then v else v) = yr) by apply simplify_if.
         assert ((if Z.eq_dec yr v
         then yr
         else if Z.eq_dec yr yr then v else yr) = v) by apply simplify_if2.
         rewrite H7, H3 in H_step_new.
         apply H_step_new.
      -- split.
         apply eq_PH_SHH.
         destruct (classic (Node _ _ bt1 yr)) as [H_is_node | H_is_leaf].
         ---
             assert (Node Z Z bt1 yr) as H_node by tauto. 
             apply Node_triple in H_node.
             destruct H_node as [L | [R | Both]].
             ++ unfold Lson_only_Node in L.
                destruct L as [NR [x Lx]].
                destruct (Z_le_gt_dec v x).
                +++ right.
                    assert (BinaryTree.step_l bt2 v x).
                    ++++ destruct H3.
                         destruct H5.
                         specialize (H5 yr x).
                         apply H5 in Lx as H8_new.
                         assert ((if Z.eq_dec yr v 
                         then yr else if Z.eq_dec yr yr 
                         then v else yr) = v) by apply simplify_if2.
                         assert ((if Z.eq_dec x v 
                         then yr else if Z.eq_dec x yr 
                         then v else x) = x).
                         **** apply simplify_if3.
                              assert (x <> yr).
                              ***** destruct H_lefs1.
                               apply ne_l in Lx. 
                               lia.
                              ***** assert (v <> yr).
                              ****** destruct H_lefs1. 
                              apply ne_r in H_step. 
                              lia.
                              ****** split.
                              ---- apply strict3_property2 with (bt1 := bt1) (v := v) (yr := yr) (x := x).
                                  ------ assert (StrictPartialHeap3 bt1).
                                         ******* split. 
                                         tauto. 
                                         tauto. 
                                         tauto.
                                         ******* tauto.
                                  ------ tauto.
                                   ------ tauto. 
                                   ------ tauto. 
                                   ------ tauto. 
                                   ------ tauto. 
                              ---- tauto.
                        **** rewrite H8 in H8_new.
                         rewrite H7 in H8_new.
                             tauto.
                    ++++ split.
                        **** intros. 
                        destruct H3. 
                        destruct H7.
                          destruct (Z.eq_dec x0 v) as [H_eq | H_neq].
                          ***** specialize (uni bt2 x0 v).
                                intros. destruct H_lefs2. 
                                apply ne_l in H5 as H5_new.
                                assert (v < x)%Z by lia.
                                assert (x0 < x)%Z by lia.

                                apply H9 in H_le2 as H_le2_new. 
                                destruct H_le2_new.
                                destruct H13.
                                apply H12 in H6.

                                destruct H_le2.
                                 specialize (step_l_unique v x y).
                                  apply step_l_unique in H6.
                                   lia.
                                tauto.
                                 split.
                                  tauto.
                                   tauto.
                                    tauto.
                                     tauto.
                          ***** destruct (Z.eq_dec x0 yr) as [H_eq | H_neq1].
                            ****** specialize (strict3_property3 bt1 v yr).
                                   apply strict3_property3 in H_step as H_step_new.
                                   destruct H_step_new.
                                    intros.
                                     specialize (H8 v x1).
                                   apply H7 in H9 as H9_new.
                                   assert ((if Z.eq_dec v v
                                   then yr
                                   else if Z.eq_dec v yr then v else v) = yr) by apply simplify_if.
                                   assert ( (if Z.eq_dec x1 v
                                   then yr
                                   else if Z.eq_dec x1 yr then v else x1) = x1).
                                   ---- apply simplify_if3.
                                    split.
                                     destruct H_lefs1.
                                      apply ne_l in H9.
                                       lia.
                                        split.
                                         destruct H_lefs1.
                                          specialize (ne_childchild v x1 yr).
                                           apply ne_childchild in H_step.
                                            lia.
                                             tauto.
                                        lia.
                                   ---- rewrite H12, H11 in H9_new.

                             specialize (uni bt2 x0 yr).
                            intros.
                             destruct H_lefs2.
                              assert(BinaryTree.legal_fs bt2) as H_lefs2.
                               {
                                split.
                                tauto.
                               }
                              apply ne_l in H5 as H5_new.
                            assert (v < x)%Z by lia.
                            assert (x0 < x)%Z by lia.
                            apply H13 in H_le2 as H_le2_new. 
                            destruct H_le2_new.
                            destruct H13.
                            apply H16 in H6.

                            destruct H_le2.
                             assert( BinaryTree.legal bt2 ) as H_le2_new.
                              {
                                split.
                                 apply step_l_unique.
                                  tauto.
                                   tauto.
                              }
                              tauto.
                               split;tauto.
                                lia. specialize (uni bt2 yr x0).
                                 intro.
                                  apply H19 in H_le2 as H_le2_new.
                            2 : tauto.
                             3 : tauto.
                              3: tauto.
                               2: {
                                 lia.
                                  }
                                   specialize (H7 v x1).
                                    apply H7 in H9 as H9_new1.
                            assert ((if Z.eq_dec v v then yr else if Z.eq_dec v yr then v else v) = yr) by apply simplify_if.
                            assert ((if Z.eq_dec x1 v then yr else if Z.eq_dec x1 yr then v else x1) = x1).
                             {
                               apply simplify_if3.
                                split.
                                 2: split.
                                  3: lia.
                                   destruct H_lefs1.
                                    apply ne_l0 in H9.
                                     lia.
                                      destruct H_lefs1.           
                            specialize (ne_childchild0 v x1 yr).
                             apply ne_childchild0 in H9.
                              2: tauto.
                               tauto.
                                }
                            rewrite H20, H21 in H9_new1.
                             apply SH in H9 as ne1.
                              assert((yr < x1)%Z) as ne2 by lia.
                               assert ((x0 < x1)%Z) as ne3 by lia.

                             specialize (uni bt2 yr x0).
                              intro.
                               apply H22 in H_le2 as H_le2_new1.
                                2: tauto.
                                 2: lia.                                 
                             apply H_le2_new1 in H9_new. 
                             (* H6, H9_new *)
                             destruct H_le2.
                              specialize (step_l_unique x0 y x1).
                               apply step_l_unique in H6.
                                2: tauto.
                                 lia.
                            ---- split.
                             tauto.
                              tauto.
                               tauto.                               
                            ---- tauto.
                            ---- tauto.
                            ---- tauto.
                            ****** destruct (Z.eq_dec y v) as [H_eq | H_neq2].
                            admit.
                            destruct (Z.eq_dec y yr) as [H_eq | H_neq3].
                            admit.
                            specialize(swap_nodes_other_same_l bt1 bt2 v yr ). 
                            intro.
                              
                            admit.
                        **** admit.
                        **** admit.
                +++ admit.
              ++ admit.
              ++ admit.
            --- admit.
Admitted.       
 (** ----------------------------------------------------- **)
 (**   辅助引理2: 处理 StrictPartialHeap3 交换后的情况   **)
 (** ----------------------------------------------------- **)
 
(* Lemma preserve_partial_heap_after_swap_strict3:
  forall bt1 bt2 (v yr : Z),
    (* 假设 bt1 是 StrictPartialHeap3 *)
    StrictPartialHeap3 bt1 ->
    (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
    BinaryTree.vvalid Z Z bt1 v ->
    BinaryTree.vvalid Z Z bt1 yr ->
    BinaryTree.step_r bt1 v yr ->
    (v > yr)%Z ->
    swap_nodes bt1 v yr bt2 ->
    (* 结论：交换后 bt2 仍然是 PartialHeap *)
    PartialHeap bt2.
Proof.
intros bt1 bt2 v yr H_heap Hv_valid_v Hv_valid_yr H_step H_gt H_swap.

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
Qed.
Admitted. *)
 
 (** ----------------------------------------------------- **)
 (**   主定理: move_up_in_partial_heap 后仍是 PartialHeap  **)
 (** ----------------------------------------------------- **)
 
 Lemma Lson_only_up:
 forall bt1 bt2 (x x0 : Z),
     (* 假设 bt1 是 StrictPartialHeap3 *)
     PartialHeap bt1 ->
     (x > x0)%Z ->
     Lson_only_Node Z Z bt1 x0 ->
     (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
     (swap_nodes x x0) bt1 tt bt2 ->
     StrictPartialHeap bt2 \/ Heap bt2.
 Proof.
 Admitted.
 
 Lemma Rson_only_up:
 forall bt1 bt2 (x x0 : Z),
     (* 假设 bt1 是 StrictPartialHeap3 *)
     PartialHeap bt1 ->
     (x > x0)%Z ->
     Rson_only_Node Z Z bt1 x0 ->
     (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
     (swap_nodes x x0) bt1 tt bt2 ->
     StrictPartialHeap bt2 \/ Heap bt2.
 Proof.
 Admitted.
 
 Lemma Lson_Rson_up:
 forall bt1 bt2 (x x0 : Z),
     (* 假设 bt1 是 StrictPartialHeap3 *)
     PartialHeap bt1 ->
     (x > x0)%Z ->
     Lson_Rson_Node Z Z bt1 x0 ->
     (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
     (swap_nodes x x0) bt1 tt bt2 ->
     StrictPartialHeap bt2 \/ Heap bt2.
 Proof.
 Admitted.
 
 Lemma Leaf_up:
 forall bt1 bt2 (x x0 : Z),
     (* 假设 bt1 是 StrictPartialHeap3 *)
     PartialHeap bt1 ->
     (x > x0)%Z ->
     Leaf Z Z bt1 x0 ->
     (* v 与 yr 就是"唯一违反堆性质"的父与其右孩子 *)
     (swap_nodes x x0) bt1 tt bt2 ->
     Heap bt2.
 Proof.
 Admitted.

 Theorem move_up_in_partial_heap_preserves_partial_heap:
 forall bt1 bt2,
   PartialHeap bt1 ->
   move_up_in_partial_heap bt1 tt bt2 ->
   PartialHeap bt2.
Proof.
intros.
destruct H0.
destruct H1.
- destruct H1 as [_ H1].
rewrite <- H1.
exact H.
- destruct H1.
-- destruct H1.
   destruct H2.
   destruct H2.
   destruct H2.
   destruct H3.
   (* destruct H4.
   destruct H5.
   destruct H6.
   destruct H6. *)
   apply inverse_partial_heap_classification.
   destruct (classic (Node Z Z bt1 x0)) as [H_is_node | H_is_leaf].
   + apply Node_triple in H_is_node.
     destruct H_is_node.
     ++ specialize (Lson_only_up bt1 bt2 x x0). 
        intro.
        tauto.
     ++ destruct H5.
       +++ specialize (Rson_only_up bt1 bt2 x x0).
        tauto.
       +++ specialize (Lson_Rson_up bt1 bt2 x x0).
       tauto.
   + right.    
     assert (Leaf Z Z bt1 x0).
     {
       unfold Node in H_is_leaf.
       tauto.
     }
     specialize (Leaf_up bt1 bt2 x x0).
     tauto.
-- (* 证明所有左子节点满足堆性质 *)
   destruct H1.
   destruct H2.
   destruct H2.
   destruct H2.
   destruct H3.
   apply inverse_partial_heap_classification.
   destruct (classic (Node Z Z bt1 x0)) as [H_is_node | H_is_leaf].
   + apply Node_triple in H_is_node.
     destruct H_is_node.
     ++ specialize (Lson_only_up bt1 bt2 x x0). 
        intro.
        tauto.
     ++ destruct H5.
       +++ specialize (Rson_only_up bt1 bt2 x x0).
        tauto.
       +++ specialize (Lson_Rson_up bt1 bt2 x x0).
       tauto.
   + right.    
     assert (Leaf Z Z bt1 x0).
     {
       unfold Node in H_is_leaf.
       tauto.
     }
     specialize (Leaf_up bt1 bt2 x x0).
     tauto.
Qed.

Theorem move_down_in_partial_heap_preserves_partial_heap:
  forall bt1 bt2,
    PartialHeap bt1 ->
    move_down_in_partial_heap bt1 tt bt2 ->
    PartialHeap bt2.
Proof.
intros.
destruct H0.
destruct H1.
- destruct H1 as [_ H1].
 rewrite <- H1.
 exact H.
- destruct H1.
 -- destruct H1.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H4.
    destruct H5.
    destruct H6.
    destruct H6.
    apply inverse_partial_heap_classification.
    destruct (classic (Node Z Z bt1 x0)) as [H_is_node | H_is_leaf].
    + apply Node_triple in H_is_node.
      destruct H_is_node.
      ++ specialize (Lson_only_up bt1 bt2 x x0). 
         intro.
         tauto.
      ++ destruct H5.
        +++ destruct H8.
         specialize (Rson_only_up bt1 bt2 x x0).
         tauto.
         specialize (Lson_Rson_up bt1 bt2 x x0).
         tauto.
    + right.    
      assert (Leaf Z Z bt1 x0).
      {
        unfold Node in H_is_leaf.
        tauto.
      }
      specialize (Leaf_up bt1 bt2 x x0).
      tauto.
    + apply inverse_partial_heap_classification.
      destruct (classic (Node Z Z bt1 x1)) as [H_is_node | H_is_leaf].
     ++ apply Node_triple in H_is_node.
        destruct H_is_node.
        +++ specialize (Lson_only_up bt1 bt2 x x1). 
         intro.
         tauto.
        +++ destruct H5.
          ++++ destruct H7.
          specialize (Rson_only_up bt1 bt2 x x1).
          assert ((x > x1)%Z) by lia.
          tauto.
          specialize (Lson_Rson_up bt1 bt2 x x1).
          assert ((x > x1)%Z) by lia.
          tauto.
      ++  right.    
          assert (Leaf Z Z bt1 x1).
          {
            unfold Node in H_is_leaf.
            tauto.
          }
          specialize (Leaf_up bt1 bt2 x x1).
          tauto.
 -- (* 证明所有左子节点满足堆性质 *)
    destruct H1.
    destruct H1.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H4.

    (* destruct H4.
    destruct H5.
    destruct H6.
    destruct H6. *)
    apply inverse_partial_heap_classification.
    destruct (classic (Node Z Z bt1 x0)) as [H_is_node | H_is_leaf].
    + apply Node_triple in H_is_node.
      destruct H_is_node.
      ++ specialize (Lson_only_up bt1 bt2 x x0). 
          intro.
          tauto.
      ++ destruct H6.
        +++ 
          specialize (Rson_only_up bt1 bt2 x x0).
          tauto.
        +++
          specialize (Lson_Rson_up bt1 bt2 x x0).
          tauto.
    + right.    
      assert (Leaf Z Z bt1 x0).
      {
        unfold Node in H_is_leaf.
        tauto.
      }
      specialize (Leaf_up bt1 bt2 x x0).
      tauto.
    + apply inverse_partial_heap_classification.
      destruct H1.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct (classic (Node Z Z bt1 x0)) as [H_is_node | H_is_leaf].
      ++ apply Node_triple in H_is_node.
        destruct H_is_node.
        +++ specialize (Lson_only_up bt1 bt2 x x0). 
          intro.
          tauto.
        +++ destruct H6.
          ++++
          specialize (Rson_only_up bt1 bt2 x x0).
          assert ((x > x0)%Z) by lia.
          tauto.
          ++++
          specialize (Lson_Rson_up bt1 bt2 x x0).
          assert ((x > x0)%Z) by lia.
          tauto.
      ++  right.    
          assert (Leaf Z Z bt1 x0).
          {
            unfold Node in H_is_leaf.
            tauto.
          }
          specialize (Leaf_up bt1 bt2 x x0).
          tauto.
Qed.

(** ----------------------------------------------------- **)
(**  集合不变性  **)
(** ----------------------------------------------------- **)

Lemma Abs_swap_nodes:
  forall bt1 bt2 v yr X,
    swap_nodes v yr bt1 tt bt2 ->
    Abs bt1 X ->
    Abs bt2 X.
Proof.
intros bt1 bt2 v yr X H H0.
unfold swap_nodes in H.
destruct H as [H_vvalid [H_evalid [H_src [H_dst H_go]]]].
unfold Abs in *.

(* 根据 preserve_vvalid 的定义，bt1 和 bt2 的 vvalid 集合相等 *)
unfold preserve_vvalid in H_vvalid.
rewrite H_vvalid.
exact H0.
Qed.

Theorem move_up_in_partial_heap_preserves_set_of_nodes:
  forall bt1 bt2 X,
    PartialHeap bt1 ->
    move_up_in_partial_heap bt1 tt bt2 ->
    Abs bt1 X ->
    Abs bt2 X.
Proof.
intros.
unfold move_up_in_partial_heap in H0.
destruct H0.
intros.
destruct H2.
- destruct H2 as [_ H2].
subst.
exact H1.
- destruct H2 .
+ destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  eapply Abs_swap_nodes with (bt1 := bt1) (v := x) (yr := x0).
  ++ exact H5.
  ++ exact H1.
+ destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  eapply Abs_swap_nodes with (bt1 := bt1) (v := x) (yr := x0).
  ++ exact H6.
  ++ exact H1.
Qed.

Theorem move_down_in_partial_heap_preserves_set_of_nodes:
  forall bt1 bt2 X,
    PartialHeap bt1 ->
    move_down_in_partial_heap bt1 tt bt2 ->
    Abs bt1 X ->
    Abs bt2 X.
Proof.
intros.
unfold move_down_in_partial_heap in H0.
destruct H0.
intros.
destruct H2.
- destruct H2 as [_ H2].
subst.
exact H1.
- destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H6.  destruct H7.
  destruct H7.
  assert (Abs bt2 X).
  {
    eapply Abs_swap_nodes with (bt1 := bt1) (v := x) (yr := x0).
    +++ exact H8.
    +++ exact H1.
  }
  exact H9.

  ++ destruct H7.
  eapply Abs_swap_nodes with (bt1 := bt1) (v := x) (yr := x1).
  +++ exact H8.
  +++ exact H1.
  ++ destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  eapply Abs_swap_nodes with (bt1 := bt1) (v := x) (yr := x0).
  +++ exact H6.
  +++ exact H1.
  +++ destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  eapply Abs_swap_nodes with (bt1 := bt1) (v := x) (yr := x0).
  ++++ exact H6.
  ++++ exact H1.
Qed.

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

  Require Import SetsClass.SetsClass.
  Require Import Coq.ZArith.ZArith.
  Require Import Coq.micromega.Psatz.
  Require Import Coq.Classes.Morphisms.
  Require Import Coq.Lists.List.
  Require Import Coq.Sorting.Permutation.
  Require Import PL.FixedPoint.
  Require Import PL.Monad.
  Import SetsNotation
         KleeneFix Sets_CPO
         Monad
         MonadNotation.
  Local Open Scope sets.
  Local Open Scope Z.
  Local Open Scope monad.
  
  Module SetMonadExamples4.
  Import SetMonadHoare
         SetMonadOperator0
         SetMonadOperator1
         ListNotations.
  
    
  Definition insert_not_swap (v: Z): StateRelMonad.M (BinTree Z Z) Z :=
  fun (bt1: BinTree Z Z) (v_return: Z) (bt2: BinTree Z Z) =>
    exists root,
    (* v不在原树中 *)
    ~ BinaryTree.vvalid Z Z bt1 v /\
    (* v_return是v的父节点 *)
    BinaryTree.step_u bt2 v v_return /\
    (* v是最末尾节点 *)
    Root bt2 root /\
    NumNodes bt2 root = Index bt2 v /\
    (* 原树中的所有节点在新树中保持不变 *)
    (forall v1, BinaryTree.vvalid Z Z bt1 v1 ->
      BinaryTree.vvalid Z Z bt2 v1 /\
      Index bt2 v1 = Index bt1 v1) /\
    (* 原树中节点间的关系保持不变 *)
    (forall v1 v2, BinaryTree.step_l bt1 v1 v2 <->
      BinaryTree.step_l bt2 v1 v2) /\
    (forall v1 v2, BinaryTree.step_r bt1 v1 v2 <->
      BinaryTree.step_r bt2 v1 v2).

Definition delete_root: StateRelMonad.M (BinTree Z Z) Z :=
  fun (bt1: BinTree Z Z) (v_return: Z) (bt2: BinTree Z Z) =>
    exists root last,
    (* 树不为空 *)
    Root bt1 root /\
    (* last是最后一个节点 *)
    BinaryTree.vvalid Z Z bt1 last /\
    (forall v i1 i2, BinaryTree.vvalid Z Z bt1 v -> 
      Index bt1 v i1 -> Index bt1 last i2 -> (i1 <= i2)%Z) /\
    (* 返回被删除的根节点值 *)
    v_return = root /\
    (* 新树中last替换root位置 *)
    (forall v1 v2, BinaryTree.step_l bt2 v1 v2 <->
      (if Z.eq_dec v1 last 
        then BinaryTree.step_l bt1 root v2
        else if Z.eq_dec v2 last
            then False
            else BinaryTree.step_l bt1 v1 v2)) /\
    (forall v1 v2, BinaryTree.step_r bt2 v1 v2 <->
      (if Z.eq_dec v1 last 
        then BinaryTree.step_r bt1 root v2
        else if Z.eq_dec v2 last
            then False
            else BinaryTree.step_r bt1 v1 v2)) /\
    (* 原树中除root和last外的节点在新树中保持不变 *)
    (forall v, BinaryTree.vvalid Z Z bt1 v -> 
      v <> root -> v <> last ->
      BinaryTree.vvalid Z Z bt2 v) /\
    (* 更新索引 *)
    (forall v, BinaryTree.vvalid Z Z bt2 v ->
      (if Z.eq_dec v last
        then Index bt2 v = Index bt1 root
        else Index bt2 v = Index bt1 v)).
      

Require Import PL.StateRelMonad.

(* visited 代表一个集合 *)
Record state (V: Type): Type :=
{
  stack: list V;
  visited: V -> Prop;
}.

Record tree_state (bt: BinTree Z Z): Type := {
  tree: BinTree Z Z;
  (* 可能还有其他状态信息 *)
}.

Definition state_based_Heap {bt: BinTree Z Z} (state: tree_state bt) : Prop :=
  Heap (tree bt state).  (* 使用 tree_state 中的 tree 字段进行堆性质的检查 *)

Definition test_heap {bt: BinTree Z Z} (s: tree_state bt): StateRelMonad.M (tree_state bt) unit :=
  fun s1 (_: unit) s2 => s1 = s2 /\ state_based_Heap s1.

Definition insert_body (bt: BinTree Z Z)
: StateRelMonad.M (BinTree Z Z) (ContinueOrBreak (BinTree Z Z) (BinTree Z Z)) :=
StateRelMonadOp.choice
  (StateRelMonadOp.test (fun state => Heap state) ;;        
    StateRelMonadOp.break bt)
  (StateRelMonadOp.test (fun state => StrictPartialHeap state) ;;
    move_up_in_partial_heap;;
    StateRelMonadOp.continue bt).

Definition delete_body (bt: BinTree Z Z)
: StateRelMonad.M (BinTree Z Z) (ContinueOrBreak (BinTree Z Z) (BinTree Z Z)) :=
StateRelMonadOp.choice
  (StateRelMonadOp.test (fun state => Heap state) ;;        
    StateRelMonadOp.break bt)
  (StateRelMonadOp.test (fun state => StrictPartialHeap state) ;;
    move_down_in_partial_heap;;
    StateRelMonadOp.continue bt).



Import SetMonadOperator1
StateRelMonadOp.
(* Definition DFS {V E} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) unit :=
  repeat_break (body_DFS pg) u. *)

Definition insert_heap (v: Z): StateRelMonad.M (BinTree Z Z) Z := 
  fun (bt1: BinTree Z Z) (v_return: Z) (bt2: BinTree Z Z) =>
    exists bt_mid bt_tmp,
    (* First insert the node at the last position *)
    insert_not_swap v bt1 v_return bt_mid /\
    (* Then repeatedly apply insert_body until the heap property is restored *)
    repeat_break insert_body bt_mid bt_tmp bt2 bt2 -> 
    (* Final tree bt2 should be a heap *)
    Heap bt2.

Definition delete_heap (v: Z): StateRelMonad.M (BinTree Z Z) Z := 
 fun (bt1: BinTree Z Z) (v_return: Z) (bt2: BinTree Z Z) =>
  exists bt_mid bt_tmp,
  (* First insert the node at the last position *)
  delete_root bt1 v_return bt_mid /\
  (* Then repeatedly apply insert_body until the heap property is restored *)
  repeat_break delete_body bt_mid bt_tmp bt2 bt2 -> 
  (* Final tree bt2 should be a heap *)
  Heap bt2.

Theorem insert_heap_correct:
forall (bt1 bt2: BinTree Z Z) (v: Z),
  Heap bt1 ->
  insert_heap v bt1 v bt2 ->
  Heap bt2.
Proof.
Admitted.

Theorem delete_heap_correct:
  forall (bt1 bt2: BinTree Z Z) (v: Z),
    Heap bt1 ->
    delete_heap v bt1 v bt2 ->
    Heap bt2.
Proof.
Admitted.

Theorem insert_heap_preserves_full_heap:
  forall (bt1 bt2: BinTree Z Z) (v: Z),
    FullHeap bt1 ->
    insert_heap v bt1 v bt2 ->
    FullHeap bt2.
Proof.
Admitted.
  (* intros bt1 bt2 v H_full_heap H_insert.
  unfold insert_heap in H_insert.
  destruct H_insert as [bt_mid [bt_tmp [H_insert_not_swap [H_repeat H_heap]]]].
  destruct H_full_heap as [H_heap1 H_connected1 [root [root_num [max_index [H_root [H_num_nodes [H_max_index H_eq]]]]]]].
  
  (* 插入节点后，树仍然是一个合法的二叉树 *)
  assert (Heap bt_mid) by (apply H_heap).
  assert (bintree_connected bt_mid) by (apply H_connected1).
  
  (* 插入节点后，树仍然是一个满二叉树 *)
  exists root, (root_num + 1), (max_index + 1).
  split; [apply H_root |].
  split; [apply H_num_nodes |].
  split; [apply H_max_index |].
  lia.
Qed. *)

Theorem delete_heap_preserves_full_heap:
  forall (bt1 bt2: BinTree Z Z) (v: Z),
    FullHeap bt1 ->
    delete_heap v bt1 v bt2 ->
    FullHeap bt2.
Proof.
intros.
Qed.

