Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Inductive CriticalToken : Type :=
  | UNLOCKED
.

Inductive Criticalstate : Type :=
  | Unlocked : addr -> list Z -> Criticalstate
  | Locked : addr -> list Z -> Criticalstate
.

Definition CriticalTranslation (s1 s2 : Criticalstate * (CriticalToken -> Prop)) : Prop :=
  exists p l, fst s1 = Locked p l /\ fst s2 = Locked p l \/ 
  exists p l, fst s1 = Unlocked p l /\ fst s2 = Unlocked p l \/
  exists p x l, fst s1 = Locked p l /\ fst s2 = Unlocked p (x :: l).


Definition Critical_S : STS := {|
  token := CriticalToken;
  STS_state := Criticalstate;
  Transition := CriticalTranslation;
|}.

Module STS_Critical <: STS_def.
  Definition sts := Critical_S.
End STS_Critical.

Module Critical_C_Rules := ConC_Rules STS_Critical.

Export Critical_C_Rules.
Local Open Scope sac.
Import CRules.

Notation "'STS_state'" := (sts.(STS_state)) (at level 1).
Notation "'TokenSet'" := (sts.(TokenSet)) (at level 1).

Definition InvownedToken (s : STS_state) : TokenSet :=
  match s with
  | Unlocked _ _ => ∅
  | Locked _ _ => [UNLOCKED]%sets
  end.

Definition Inside_critical (state : STS_state) : Assertion :=
  fun s => mem_empty s.(s_mem) /\ s.(s_token) == ∅ /\ s.(s_STS) == [state]%sets. 

Definition Outside_critical (state : STS_state -> Prop) : Assertion :=
  fun s => mem_empty s.(s_mem) /\ s.(s_token) == [UNLOCKED]%sets /\ s.(s_STS) == state.

Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX y: addr,
                   &(x # "list" ->ₛ "data") # Int |-> a **
                   &(x # "list" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

Definition Invmem (state : STS_state) : Assertion :=
  match state with 
  | Unlocked p l => sll p l
  | Locked p l => sll p l
  end.

(*

void enter_critical()
/*@ With s1 
    Require Outside_critical(s1)
    Ensure exists s, s ∈ s1 && Inside_critical(s) && Invmem(s)
*/

void exit_critical()
/*@ With s1 s2
    Require Inside_critical(s1) && Invmem(s1)
    Ensure Outside_critical(s2) 
*/

void push_inside_critical(int x)
/*@ With p l
    Require sll(p, l)
    Ensure sll(p, x :: l)
*/

void push(struct list *p, int x)
/*@ With l
    Require Outside_critical(Unlocked(p,l))
    Ensure exists l', Outside_critical(Unlocked(p, l'))
*/
{
  enter_critical();
  push_inside_critical(x);
  exit_critical();
}

*)