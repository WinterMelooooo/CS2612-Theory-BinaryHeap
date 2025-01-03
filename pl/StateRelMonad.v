Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
Require Import PL.Monad.
Require Import PL.Monad2.
Import SetsNotation
       KleeneFix Sets_CPO
       Monad
       MonadNotation.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.


(** 下面用StateRelMonad表示带有程序状态的非确定性计算。*)

Module StateRelMonad.

Definition M (Σ A: Type): Type :=
  Σ -> A -> Σ -> Prop.

Definition bind (Σ A B: Type) (f: M Σ A) (g: A -> M Σ B): M Σ B :=
  fun (s1: Σ) (b: B) (s3: Σ) =>
    exists (a: A) (s2: Σ),
      (s1, a, s2) ∈ f /\ (s2, b, s3) ∈ g a.

Definition ret (Σ A: Type) (a0: A): M Σ A :=
  fun (s1: Σ) (a: A) (s2: Σ) => a = a0 /\ s1 = s2.

End StateRelMonad.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{|
  bind := StateRelMonad.bind Σ;
  ret := StateRelMonad.ret Σ;
|}.

Module StateRelMonadOp.
Import SetMonadOperator1.


(** 下面用StateRelMonad表示带有程序状态的非确定性计算。*)

Module StateRelMonad.

Definition M (Σ A: Type): Type :=
  Σ -> A -> Σ -> Prop.

Definition bind (Σ A B: Type) (f: M Σ A) (g: A -> M Σ B): M Σ B :=
  fun (s1: Σ) (b: B) (s3: Σ) =>
    exists (a: A) (s2: Σ),
      (s1, a, s2) ∈ f /\ (s2, b, s3) ∈ g a.

Definition ret (Σ A: Type) (a0: A): M Σ A :=
  fun (s1: Σ) (a: A) (s2: Σ) => a = a0 /\ s1 = s2.

End StateRelMonad.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{|
  bind := StateRelMonad.bind Σ;
  ret := StateRelMonad.ret Σ;
|}.

(** 以下可以再定义一些额外的算子。*)

Definition test {Σ: Type} (P: Σ -> Prop): StateRelMonad.M Σ unit :=
  fun s1 _ s2 => P s1 /\ s1 = s2.

Definition choice {Σ A: Type} (f g: StateRelMonad.M Σ A): StateRelMonad.M Σ A :=
  f ∪ g.

Definition any {Σ: Type} (A: Type): StateRelMonad.M Σ A :=
  fun s1 _ s2 => s1 = s2.

Definition repeat_break_f
             {Σ A B: Type}
             (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B))
             (W: A -> StateRelMonad.M Σ B)
             (a: A): StateRelMonad.M Σ B :=
  x <- body a;;
  match x with
  | by_continue a' => W a'
  | by_break b => ret b
  end.

Definition repeat_break
             {Σ A B: Type}
             (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B)):
  A -> StateRelMonad.M Σ B :=
  Kleene_LFix (repeat_break_f body).

Definition continue {Σ A B: Type} (a: A):
  StateRelMonad.M Σ (ContinueOrBreak A B) :=
  ret (by_continue a).

Definition break {Σ A B: Type} (b: B):
  StateRelMonad.M Σ (ContinueOrBreak A B) :=
  ret (by_break b).

End StateRelMonadOp.

(** 可以如下定义有向图。*)

Record PreGraph (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

(** 基于此就能定义“从x点经过一条边可以到达y点”。*)

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y.

(** 进一步，单步可达关系的自反传递闭包就是多步可达关系。*)

Definition reachable {V E: Type} (pg: PreGraph V E) :=
  clos_refl_trans (step pg).


(** 自反传递闭包_[clos_refl_trans]_是SetsClass库提供的定义。*)


Module StateRelMonadExample.
Import SetMonadOperator1
       StateRelMonadOp.

(** 下面定义DFS算法的程序状态，每个程序状态包含一个_[visitied]_集合与一个栈。*)

Record state (V: Type): Type :=
{
  stack: list V;
  visited: V -> Prop;
}.

Definition unvisited (V: Type) (s: state V): V -> Prop :=
  Sets.complement (visited V s).

Notation "s '.(visited)'" := (visited _ s) (at level 1).
Notation "s '.(unvisited)'" := (unvisited _ s) (at level 1).
Notation "s '.(stack)'" := (stack _ s) (at level 1).

Lemma unvisited_visited {V: Type}:
  forall (s: state V),
    s.(unvisited) == Sets.complement s.(visited).
Proof. intros. reflexivity. Qed.

(** 基于此就可以定义DFS中需要用到的程序状态基本操作。*)

Definition test_unvisited {V} (v: V): StateRelMonad.M (state V) unit :=
  test (fun s => ~ v ∈ s.(visited)).

Definition test_all_neighbor_visited {V E} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) unit :=
    test (fun s => forall v, step pg u v -> v ∈ s.(visited)).

Definition visit {V} (v: V): StateRelMonad.M (state V) unit :=
  fun s1 _ s2 =>
    s2.(visited) == s1.(visited) ∪ Sets.singleton v /\
    s2.(stack) = s1.(stack).

Definition push_stack {V} (v: V): StateRelMonad.M (state V) unit :=
  fun s1 _ s2 =>
    s2.(stack) = v :: s1.(stack) /\ s2.(visited) = s1.(visited).

Definition pop_stack {V}: StateRelMonad.M (state V) V :=
  fun s1 v s2 =>
    s1.(stack) = v :: s2.(stack) /\ s2.(visited) = s1.(visited).

Definition test_empty_stack {V}: StateRelMonad.M (state V) unit :=
  test (fun s => s.(stack) = nil).

(** 以下是DFS算法的描述。*)

Definition body_DFS {V E} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) (ContinueOrBreak V unit) :=
  choice
    (v <- any V;;
     test_unvisited v;;
     test (fun _ => step pg u v);;
     push_stack u;;
     visit v;;
     continue v)
    (test_all_neighbor_visited pg u;;
      choice
      (v <- pop_stack;;
       continue v)
      (test_empty_stack;;
       break tt)).

Definition DFS {V E} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) unit :=
  repeat_break (body_DFS pg) u.

End StateRelMonadExample.

Module StateRelMonadHoare.
Import SetMonadOperator1
       StateRelMonadOp.


(** 在StateRelMonad上的霍尔逻辑是一个关于霍尔三元组的逻辑。*)

Definition Hoare {Σ A: Type}
                 (P: Σ -> Prop)
                 (c: StateRelMonad.M Σ A)
                 (Q: A -> Σ -> Prop): Prop :=
  forall s1 a s2, P s1 -> (s1, a, s2) ∈ c -> Q a s2.

Theorem Hoare_bind {Σ A B: Type}:
  forall (P: Σ -> Prop)
         (f: StateRelMonad.M Σ A)
         (Q: A -> Σ -> Prop)
         (g: A -> StateRelMonad.M Σ B)
         (R: B -> Σ -> Prop),
  Hoare P f Q ->
  (forall a, Hoare (Q a) (g a) R) ->
  Hoare P (bind f g) R.
Proof.
  intros.
  unfold Hoare, bind; simpl; sets_unfold; unfold StateRelMonad.bind.
  intros s1 b s3 ? [a [s2 [? ?]]].
  pose proof H _ _ _ H1 H2.
  pose proof H0 a _ _ _ H4 H3.
  tauto.
Qed.

Theorem Hoare_ret {Σ A: Type}:
  forall (P: A -> Σ -> Prop) (a0: A),
    Hoare (P a0) (ret a0) P.
Proof.
  intros.
  unfold Hoare, ret; simpl; sets_unfold; unfold StateRelMonad.ret.
  intros.
  destruct H0; subst; tauto.
Qed.

End StateRelMonadHoare.


