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

Record Heap (h: BinTree Z Z): Prop := (*大顶堆*)
{
  heap_l: forall x y: Z, BinaryTree.step_l h x y -> (x <= y)%Z;
  heap_r: forall x y: Z, BinaryTree.step_r h x y -> (x <= y)%Z;
}.

Definition Abs (h: BinTree Z Z) (X: Z -> Prop): Prop :=
  X == h.(vvalid).

Record PartialHeap (h: BinTree Z Z): Prop := {
  (* 存在一个节点v违反堆的性质 *)
  exists_violation: exists v: Z,
    h.(vvalid) v /\ (* v必须是合法节点 *)
    (exists y: Z,
      (BinaryTree.step_l h v y \/ BinaryTree.step_r h v y) /\ (v > y)%Z) /\
    (* 其他所有节点都满足堆的性质 *)
    (forall x y: Z,
      x <> v -> 
      (BinaryTree.step_l h x y \/ BinaryTree.step_r h x y) -> 
      (x <= y)%Z);
}.

(* Definition move_up (h: BinTree Z Z) (v: Z): BinTree Z Z :=
  {|
    BinaryTree.vvalid := h.(vvalid);
    BinaryTree.evalid := h.(evalid);
    BinaryTree.src := fun e => 
      match (h.(src) e =? v)%Z with
      | true => h.(dst) e
      | false => 
        match (h.(dst) e =? v)%Z with
        | true => h.(src) e
        | false => h.(src) e
        end
      end;
    BinaryTree.dst := fun e =>
      match (h.(dst) e =? v)%Z with
      | true => h.(src) e
      | false => 
        match (h.(src) e =? v)%Z with
        | true => h.(dst) e
        | false => h.(dst) e
        end
      end;
    BinaryTree.go_left := h.(go_left)
  |}. *)
(* 首先定义 elements 函数 *)
(* 首先定义一个有限集合的概念 *)

Require Import PL.FixedPoint.
Require Import PL.StateRelMonad. 

Definition bind {A B: Type} (m: option A) (f: A -> option B): option B :=
  match m with
  | Some x => f x
  | None => None
  end.

Notation "'do' x <- m1 ; m2" := 
  (bind m1 (fun x => m2))
  (at level 60, x ident, m1 at level 200, right associativity).

Definition find_parent (bt: BinTree Z Z) (v parent: Z): Prop :=
  BinaryTree.step_u bt v parent.

Fixpoint swap_nodes (bt: BinTree Z Z) (v1 v2: Z) (bt': BinTree Z Z): Prop :=
  match bt with

Definition swap_nodes (bt: BinTree Z Z) (v1 v2: Z) (bt': BinTree Z Z): Prop :=
  (* 交换节点 v1 和 v2，得到新的二叉树 bt' *)
  bt'.(vvalid) == bt.(vvalid) /\
  bt'.(evalid) == bt.(evalid) /\
  (* 更新 src 和 dst *)
  (forall e,
      bt'.(src) e =
        if Z.eq_dec (bt.(src) e) v1 then v2
        else if Z.eq_dec (bt.(src) e) v2 then v1
        else bt.(src) e) /\
  (forall e,
      bt'.(dst) e =
        if Z.eq_dec (bt.(dst) e) v1 then v2
        else if Z.eq_dec (bt.(dst) e) v2 then v1
        else bt.(dst) e) /\
  bt'.(go_left) = bt.(go_left).

Definition move_up (v: Z): StateRelMonad.M (BinTree Z Z) unit :=
  fun (bt1: BinTree Z Z) (_: unit) (bt2: BinTree Z Z) =>
    (* 检查节点 v 是合法的 *)
    bt1.(vvalid) v /\
    (* 存在父节点 parent *)
    exists parent,
      (* 在 bt1 中找到 parent *)
      BinaryTree.step_u bt1 v parent /\
      (* 交换节点 v 和 parent，得到新的 bt2 *)
      swap_nodes bt1 v parent bt2.