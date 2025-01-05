Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Local Open Scope sets_scope.

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
  bt.(vvalid) v /\
  (~ exists y, BinaryTree.step_l bt v y) /\
  (~ exists y, BinaryTree.step_r bt v y).

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
    h.(vvalid) v /\ (* v必须是合法节点 *)
    (exists y: Z,
      (BinaryTree.step_l h v y \/ BinaryTree.step_r h v y) /\ (v > y)%Z) /\
    (* 其他所有节点都满足堆的性质 *)
    (forall x y: Z,
      x <> v -> 
      (BinaryTree.step_l h x y \/ BinaryTree.step_r h x y) -> 
      (x <= y)%Z);
}.

Record StrictPartialHeap1 (h: BinTree Z Z): Prop := {
  (* 存在一个节点v同时违反左右子节点的堆性质 *)
  exists_violation_strict1: exists v: Z,
    h.(vvalid) v /\ (* v必须是合法节点 *)
    (* v必须同时有左右子节点，并且比两个子节点都大 *)
    (exists yl yr: Z,
      BinaryTree.step_l h v yl /\ 
      BinaryTree.step_r h v yr /\ 
      (v > yl)%Z /\ 
      (v > yr)%Z) /\
    (* 其他所有节点都满足堆的性质 *)
    (forall x y: Z,
      x <> v -> 
      (BinaryTree.step_l h x y \/ BinaryTree.step_r h x y) -> 
      (x <= y)%Z);
}.

Record StrictPartialHeap2 (h: BinTree Z Z): Prop := {
  exists_violation_strict2: exists v: Z,
    h.(vvalid) v /\ 
    (* v必须有左孩子且大于左孩子，右孩子如果存在则不大于右孩子 *)
    (exists yl: Z,
      BinaryTree.step_l h v yl /\ 
      (v > yl)%Z /\
      (forall yr: Z, 
        BinaryTree.step_r h v yr -> 
        (v <= yr)%Z)) /\
    (* 其他所有节点都满足堆的性质 *)
    (forall x y: Z,
      x <> v -> 
      (BinaryTree.step_l h x y \/ BinaryTree.step_r h x y) -> 
      (x <= y)%Z);
}.

Record StrictPartialHeap3 (h: BinTree Z Z): Prop := {
  exists_violation_strict3: exists v: Z,
    h.(vvalid) v /\ 
    (* v必须有右孩子且大于右孩子，左孩子如果存在则不大于左孩子 *)
    (exists yr: Z,
      BinaryTree.step_r h v yr /\ 
      (v > yr)%Z /\
      (forall yl: Z, 
        BinaryTree.step_l h v yl -> 
        (v <= yl)%Z)) /\
    (* 其他所有节点都满足堆的性质 *)
    (forall x y: Z,
      x <> v -> 
      (BinaryTree.step_l h x y \/ BinaryTree.step_r h x y) -> 
      (x <= y)%Z);
}.

Theorem strict_partial_heap_classification:
  forall h: BinTree Z Z,
    StrictPartialHeap h -> StrictPartialHeap1 h \/ StrictPartialHeap2 h \/ StrictPartialHeap3 h.
Proof.
  Admitted.

Theorem partial_heap_classification:
  forall h: BinTree Z Z,
    PartialHeap h -> StrictPartialHeap h \/ Heap h.
Proof.
  Admitted.
  (* intros h PH.
  (* 先考虑是否存在违反堆性质的节点 *)
  destruct (classic (exists v,
    h.(vvalid) v /\
    exists y, (BinaryTree.step_l h v y \/ BinaryTree.step_r h v y) /\ (v > y)%Z)) as [H_violation | H_no_violation].
  
  - (* 如果存在违反堆性质的节点，证明是 StrictPartialHeap *)
    left.
    destruct H_violation as [v [Hvalid [y [Hstep Hgt]]]].
    constructor.
    exists v.
    split; [exact Hvalid |].
    split; [exists y; split; assumption |].
    intros x y0 Hneq Hstep'.
    (* 利用 PartialHeap 的性质 *)
    destruct PH as [H_unique].
    (* 反证法：假设 x > y0 *)
    destruct (Z.gt_dec x y0) as [Hgt' | Hngt].
    + assert (x = v).
      { apply (H_unique x v); split.
        - split; [assumption |].
          exists y0; split; assumption.
        - split; [assumption |].
          exists y; split; assumption. }
      contradiction.
    + apply Z.gt_ngt in Hngt.
      apply Z.le_lteq in Hngt.
      assumption.

  - (* 如果不存在违反堆性质的节点，证明是 Heap *)
    right.
    constructor; intros x y Hstep.
    + (* 对于左子节点 *)
      apply NNPP.
      intro Hnle.
      apply H_no_violation.
      exists x. split; [|exists y; split].
      * destruct Hstep as [e [Hstep_aux _]].
        destruct Hstep_aux; assumption.
      * left; assumption.
      * apply Z.nle_gt; assumption.
    + (* 对于右子节点 *)
      apply NNPP.
      intro Hnle.
      apply H_no_violation.
      exists x. split; [|exists y; split].
      * destruct Hstep as [e [Hstep_aux _]].
        destruct Hstep_aux; assumption.
      * right; assumption.
      * apply Z.nle_gt; assumption. *)


Definition Root (h: BinTree Z Z) (v: Z): Prop :=
  h.(vvalid) v /\
  (~ exists y, BinaryTree.step_u h v y).

Require Import PL.Monad.
Require Import PL.StateRelMonad.
Import Monad SetMonad StateRelMonad.

Definition swap_nodes (bt: BinTree Z Z) (v1 v2: Z) (bt': BinTree Z Z): Prop :=
  BinaryTree.vvalid _ _ bt' == BinaryTree.vvalid _ _ bt /\
  BinaryTree.evalid _ _ bt' == BinaryTree.evalid _ _ bt /\
  (forall e, BinaryTree.src _ _ bt' e = if Z.eq_dec (BinaryTree.src _ _ bt e) v1 then v2 else if Z.eq_dec (BinaryTree.src _ _ bt e) v2 then v1 else BinaryTree.src _ _ bt e) /\
  (forall e, BinaryTree.dst _ _ bt' e = if Z.eq_dec (BinaryTree.dst _ _ bt e) v1 then v2 else if Z.eq_dec (BinaryTree.dst _ _ bt e) v2 then v1 else BinaryTree.dst _ _ bt e) /\
  BinaryTree.go_left _ _ bt' = BinaryTree.go_left _ _ bt.


Definition move_up (v: Z): StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
    (* 检查节点 v 是合法的 *)
    BinaryTree.vvalid Z Z bt1 v /\
    (* 存在父节点 parent *)
    exists parent,
      (* 在 bt1 中找到 parent *)
      BinaryTree.step_u bt1 v parent /\
      (* 交换节点 v 和 parent，得到新的 bt2 *)
      swap_nodes bt1 v parent bt2.

Definition move_down (v: Z): StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
    BinaryTree.vvalid Z Z bt1 v /\
    exists child,
      BinaryTree.step_l bt1 v child \/ BinaryTree.step_r bt1 v child /\
      swap_nodes bt1 v child bt2.

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
        swap_nodes bt1 v yl bt2) \/
    (* 如果是 StrictPartialHeap3，类似处理 *)
    (StrictPartialHeap3 bt1 /\
      exists v yr,
        (* 从 StrictPartialHeap3 的定义中获取违反性质的节点 v *)
        BinaryTree.vvalid Z Z bt1 v /\
        BinaryTree.vvalid Z Z bt1 yr /\
        BinaryTree.step_r bt1 v yr /\ (v > yr)%Z /\
        (forall yl, BinaryTree.step_l bt1 v yl -> (v <= yl)%Z) /\
        swap_nodes bt1 v yr bt2)).

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
        ((yl <= yr)%Z /\ swap_nodes bt1 v yl bt2 \/
          (yr < yl)%Z /\ swap_nodes bt1 v yr bt2)) \/
    (* 如果是 StrictPartialHeap2，交换 v 和其左子节点 *)
    (StrictPartialHeap2 bt1 /\
      exists v yl,
        BinaryTree.vvalid Z Z bt1 v /\
        BinaryTree.vvalid Z Z bt1 yl /\
        BinaryTree.step_l bt1 v yl /\
        (v > yl)%Z /\
        (forall yr, BinaryTree.step_r bt1 v yr -> (v <= yr)%Z) /\
        swap_nodes bt1 v yl bt2) \/
    (* 如果是 StrictPartialHeap3，交换 v 和其右子节点 *)
    (StrictPartialHeap3 bt1 /\
      exists v yr,
        BinaryTree.vvalid Z Z bt1 v /\
        BinaryTree.vvalid Z Z bt1 yr /\
        BinaryTree.step_r bt1 v yr /\
        (v > yr)%Z /\
        (forall yl, BinaryTree.step_l bt1 v yl -> (v <= yl)%Z) /\
        swap_nodes bt1 v yr bt2)).
