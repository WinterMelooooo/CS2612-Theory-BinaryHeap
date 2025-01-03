Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem Assertion.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope sac.
Import CRules.
Require Import String.
Require Import demo0125.

(** 考虑C程序

struct list {
  int data;
  struct list *next;
};

struct list * * G;
int * B;

void atomic_push(int x) {
enter_critical();
while ( * B == LOCKED ) {
  exit_critical();
  enter_critical();
}
* B = LOCKED;
p = get_head_ptr();
exit_critical();
x = MD5(x, p);
enter_critical();
push(x);
* B = UNLOCKED;
exit_critical();
}

修改后考虑加密的sll定义：

sll(p, nil)    := p == NULL && emp
sll(p, x :: l) := exists q,
                    &(p -> data) |-> MD5(x, q) **
                    &(p -> next) |-> q **
                    sll(q, l)

要证明的结论：
  atomic_push(x) ⪯ atomic(AbstractPush(x))

*)

Definition STS_stateₕ := list Z.

Inductive LockState: Type :=
| LOCKED
| UNLOCKED.

Record STS_stateₗ: Type := {
  lockState: LockState;
  addrState: addr;
  listState: list Z;
}.

Definition Locked (p: addr) (l: list Z): STS_stateₗ :=
    {|
        lockState := LOCKED;
        addrState := p;
        listState := l;
    |}.

(** 用UNLOCK token表示把LOCKED状态转化为UNOLOCKED状态的权限；任何线程/任务都可以
    从UNLOCKED转移到LOCKED状态，同时获得一个UNLOCK token。从LOCKED状态转移回到
    UNLOCKED状态时，需要交回UNLOCK token。总共全局只有一个UNLOCK token。*)

(**
其中涉及的临界区内函数满足下面规约：

node* get_head_ptr()
/*@ With p l
    Require G |-> p * sll(p, l)
    Ensure __return == p && G |-> p * sll(p, l)
*/

void push(int x)
/*@ With q
    Require G |-> q 
    Ensure exists p, G |-> p * &(p -> data) |-> x * &(p -> next) |-> q
*/
*)

(**

glob_inv(Locked(p, l)) :=
  G |-> p ** B |-> LOCKED ** sll(p, l)
glob_inv(Unlocked(p, l)) :=
  G |-> p ** B |-> UNLOCKED ** sll(p, l)

/*@ 
  With l
  Require exists p,
            Outside_Stateₗ(Unlocked(p, l) , {}) **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x)))
  Ensure exists p l',
            Outside_Stateₗ(Unlocked(p, x :: l' ++ l), {}) **
            AsToExe(Stateₕ(x :: l' ++ l), skip)
*/

/*@ exists p,
            Outside_Stateₗ(Unlocked(p, l) , {}) **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

enter_critical();

/*@ exists p' l',
            Inside_Stateₗ(Unlocked(p', l' ++ l) , {}) **
              G |-> p' ** sll(p', l' ++ l) ** B |-> UNLOCKED
              AsToExe(Stateₕ(l), atomic(AbstractPush(x))) ||
            Inside_Stateₗ(Locked(p', l' ++ l) , {}) **
              G |-> p' ** sll(p', l' ++ l) ** B |-> LOCKED
              AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

while ( * B == LOCKED ) {

  /*@ exists p' l',
              Inside_Stateₗ(Locked(p', l' ++ l) , {}) **
              G |-> p' ** sll(p', l' ++ l) ** B |-> LOCKED
              AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

  exit_critical();

  /*@ exists p' l',
              Outside_Stateₗ(Locked(p', l' ++ l) , {}) **
              AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

  enter_critical();

  /*@ exists p' l' l'',
            Outside_Stateₗ(Locked(p', l'' ++ l' ++ l) , {}) **
              G |-> p' ** sll(p', l'' ++ l' ++ l) ** B |-> LOCKED
              AsToExe(Stateₕ(l), atomic(AbstractPush(x))) ||
            Outside_Stateₗ(Unlocked(p', l'' ++ l' ++ l) , {}) **
              G |-> p' ** sll(p', l'' ++ l' ++ l) ** B |-> UNLOCKED
              AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */
}

/*@ exists p' l',
            Inside_Stateₗ(Unlocked(p', l' ++ l) , {}) **
              G |-> p' ** sll(p', l' ++ l) ** B |-> UNLOCKED
              AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

* B = LOCKED;

/*@ exists p' l',
            Inside_Stateₗ(Unlocked(p', l' ++ l) , {}) **
            G |-> p' ** sll(p', l' ++ l) ** B |-> LOCKED
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

p = get_head_ptr();

/*@ exists l',
            Inside_Stateₗ(Unlocked(p, l' ++ l) , {}) **
            G |-> p ** sll(p, l' ++ l) ** B |-> LOCKED **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

exit_critical();

/*@ exists l',
            Outside_Stateₗ(Locked(p, l' ++ l) , {UNLOCK}) **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

x0 = MD5(x, p);

/*@ exists l',
            x0 == MD5(x, p) &&
            Outside_Stateₗ(Locked(p, l' ++ l) , {UNLOCK}) **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

enter_critical();

/*@ exists l',
            x0 == MD5(x, p) &&
            Inside_Stateₗ(Locked(p, l' ++ l) , {UNLOCK}) **
            G |-> p ** sll(p, l' ++ l) ** B |-> LOCKED **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

push(x0);

/*@ exists l',
            x0 == MD5(x, p) &&
            Inside_Stateₗ(Locked(p, l' ++ l) , {UNLOCK}) **
            G |-> p ** sll(p, x :: l' ++ l) ** B |-> LOCKED **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

* B = UNLOCKED;

/*@ exists l',
            x0 == MD5(x, p) &&
            Inside_Stateₗ(Locked(p, l' ++ l) , {UNLOCK}) **
            G |-> p ** sll(p, x :: l' ++ l) ** B |-> UNLOCKED **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

exit_critical();

/*@ exists l',
            x0 == MD5(x, p) &&
            Outside_Stateₗ(Unlocked(p, x :: l' ++ l) , {}) **
            AsToExe(Stateₕ(l), atomic(AbstractPush(x))) */

/*@ exists l',
            Outside_Stateₗ(Unlocked(p, x :: l' ++ l) , {}) **
            AsToExe(Stateₕ(x :: l' ++ l), skip) */































//@ SE: exists p s, s ∈ closure(Unlocked(p,l),{}) && Inside_Stateₗ(s,{}) && glob_inv(s) * Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x)))

/*@ assert : exists p l', s == Unlocked(p,l' ++ l) && glob_inv(s) || 
             exists p l', s == Locked(p,l' ++ l) && glob_inv(s) */

/*@ which implies : exists p l', G |-> p * sll(p, l' ++ l) * B |-> UNLOCKED || 
                    exists p l', G |-> p * sll(p, l' ++ l) * B |-> LOCKED */

/*@ SE : exists p l', 
        Inside_Stateₗ(Unlocked(p, l' ++ l), {}) && G |-> p * sll(p, l' ++ l) * B |-> UNLOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) ||
      exists p l', 
        Inside_Stateₗ(Locked(p, l' ++ l),{}) && G |-> p * sll(p, l' ++ l) * B |-> LOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

/*@ Inv
      exists p l', 
        Inside_Stateₗ(Unlocked(p, l' ++ l), {}) && G |-> p * sll(p, l' ++ l) * B |-> UNLOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) ||
      exists p l', 
        Inside_Stateₗ(Locked(p, l' ++ l),{}) && G |-> p * sll(p, l' ++ l) * B |-> LOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

while ( * B == LOCKED ) {

  /*@ SE: exists p l', 
        Inside_Stateₗ(Locked(p, l' ++ l), {}) && G |-> p * sll(p, l' ++ l) * B |-> LOCKED *  
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

  /*@ assert : exists p l', G |-> p * sll(p, l' ++ l) * B |-> LOCKED */
  /*@ which implies : exists p l', glob_inv(Locked(p, l' ++ l)) */

  exit_critical(); //@ where gained_token = {}

  /*@ SE: exists p l', Outside_Stateₗ(Locked(p, l' ++ l), {}) && Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

  enter_critical();

  /*@ SE: exists p l' s, s ∈ closure(Locked(p, l' ++ l), {}) && Inside_Stateₗ(s,{}) && glob_inv(s) * Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

  /*@ assert : exists p l', s == Unlocked(p,l' ++ l) && glob_inv(s) || 
               exists p l', s == Locked(p,l' ++ l) && glob_inv(s) */

  /*@ which implies : exists p l', G |-> p * sll(p, l' ++ l) * B |-> UNLOCKED || 
                      exists p l', G |-> p * sll(p, l' ++ l) * B |-> LOCKED */

  /*@ SE : exists p l', 
        Inside_Stateₗ(Unlocked(p, l' ++ l), {}) && G |-> p * sll(p, l' ++ l) * B |-> UNLOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) ||
      exists p l', 
        Inside_Stateₗ(Locked(p, l' ++ l),{}) && G |-> p * sll(p, l' ++ l) * B |-> LOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */
}

/*@ SE: exists p l', 
        Inside_Stateₗ(Unlocked(p, l' ++ l), {}) && G |-> p * sll(p, l' ++ l) * B |-> UNLOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x)))  */

* B = LOCKED;

/*@ SE: exists p l', 
        Inside_Stateₗ(Unlocked(p, l' ++ l),{}) && G |-> p * sll(p, l' ++ l) * B |-> LOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x)))  */

p = get_head_ptr_inside_critical();

/*@ SE: exists l', 
        Inside_Stateₗ(Unlocked(p, l' ++ l), {}) && G |-> p * sll(p, l' ++ l) * B |-> LOCKED * 
        Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x)))  */

/*@ assert : exists l', G |-> p * sll(p, l' ++ l) * B |-> LOCKED */
/*@ which implies : exists l', glob_inv(Locked(p, l' ++ l)) */

exit_critical(); //@ where gained_token = {UNLOCK}

/*@ SE ：exists l', Outside_Stateₗ(Locked(p, l' ++ l),{UNLOCK}) &&
               Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */ 

x' = MD5(x, p);

/*@ SE : exists l', x' == MD5(x,p) && Outside_Stateₗ(Locked(p, l' ++ l),{UNLOCK}) && Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

enter_critical();

/*@ SE: exists s l', x' == MD5(x, p) && s ∈ closure(Locked(p, l' ++ l),{UNLOCK}) && 
               Inside_Stateₗ(s, {UNLOCK}) && glob_inv(s) *
               Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

/*@ assert : exists l', s == Locked(p, l' ++ l) && glob_inv(s) */
/*@ which implies : exists l', G |-> p * sll(p, l' ++ l) * B |-> LOCKED */

push_inside_critical(x');

/*@ SE: exists q l', x' == MD5(x,p) && Inside_Stateₗ(Locked(p, l' ++ l), {UNLOCK}) && G |-> q * &(q -> data) |-> x' * &(q -> next) |-> p * sll(p, l' ++ l) * B |-> LOCKED * Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

* B = UNLOCKED;

/*@ SE: exists q l', x' == MD5(x,p) && Inside_Stateₗ(Locked(p, l' ++ l), {UNLOCK}) && G |-> q * &(q -> data) |-> x' * &(q -> next) |-> p * sll(p, l' ++ l) * B |-> UNLOCKED * Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x))) */

/*@ assert : exists q l', G |-> q * sll(q, x :: l' ++ l) * B |-> UNLOCKED */
/*@ which implies: exists q l', glob_inv(Unlocked(q, x :: l' ++ l)) */

exit_critical(); //@ where gained_token = {}

/*@ SE : exists q l', Outside_Stateₗ(Unlocked(q, x :: l' ++ l),{}) && Stateₕ(Abs(l)) * AbsProg(atomic(AbstractPush(x)))
*/

/*@ assert : exists q l', Outside_Stateₗ(Unlocked(q, x :: l' ++ l),{}) && Stateₕ(Abs(x :: l' ++ l)) * AbsProg(skip) */

OSInv := exists p l, Outside_Stateₗ(Unlocked(p, l),{}) && Stateₕ(Abs(l))


In Coq :

sll(p, nil) := p = NULL && emp
sll(p, x :: l) := exists q, &(p -> data) |-> MD5(x, q) * &(p -> next) |-> q * sll(q, l)

AbstractPush(x) := fun l1 l2 => l2 = x :: l1

Token := {UNLOCK}
TokenSetₗ := Token -> Prop

STS_stateₗ := { Unlocked(p, l) | l: list } ∪ { Locked(p, l) | l: list }

STS_stateₕ := { l | l: list }

Outside_Stateₗ : (STS_stateₗ  * TokenSetₗ -> Prop) -> Assertion
Inside_Stateₗ : (STS_stateₗ * TokenSetₗ -> Prop) -> Assertion
Stateₕ : (STS_stateₕ -> Prop) -> Assertion

Token(Locked(p, l)) := []
Token(UnLocked(p, l)) := [UNLOCKED]

AllowedTransition (s1, s2) :=
  exists p l, s1 = Locked(p,l) /\ s2 = Locked(p,l) \/ 
  exists p x q l, s1 = Locked(p,l) /\ s2 = Unlocked(q, x :: l) \/
  exists p l, s1 = Unlocked(p,l) /\ s2 = Locked(p,l)

*)