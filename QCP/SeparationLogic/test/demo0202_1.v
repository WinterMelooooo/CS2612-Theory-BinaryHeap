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

(** 1. 压栈的原子操作 *)

(**

考虑下面C程序

struct list {
  int data;
  struct list *next;
};

struct list * * G;

void push(int x)
//@ With l
//@ Require sll_box(G, l)
//@ Ensure sll_box(G, x :: l)
{
  struct list * p;
  p = ( struct list * ) malloc(sizeof(struct list));
  p -> data = x;
  p -> next = * G;
  * G = p;
}

void atomic_push(int x) {
  enter_critical();
  push(x);
  exit_critical();
}

*)

(** 这两个函数中，push()函数不涉及并发操作，它的规约是明确的，证明也不困难。而
    atomic_push()函数中涉及进出临界区，它的操作似乎还要考虑其他线程（或任务）的操作带
    来的影响。然而，简单分析后不难发现，这段程序中临界区保护的是全局变量G指向的一个单链
    表，这可以用以下谓词来表示：

        _[exists l, sll_box(G, l)]_

    因此，在利用并发分离逻辑验证这段程序的时候，可以这样看到进出临界区函数：

        1. 进入临界区时，获得一块满足_[exists l, sll_box(G, l)]_的内存的读写权限；

        2. 离开临界区时，放弃一块满足_[exists l, sll_box(G, l)]_的内存的读写权限。

    “对于临界区保护的内存空间总是执行服从上面协议的操作”就是一种功能正确性。下面是用程
    序断言标注表示的证明。其中，_[Outside_Stateₗ()]_表示处于临界区外，
    _[Inside_Stateₗ()]_表示处于临界区内。注：这段程序与这个功能正确性规约比较简单，之
    后还会再细化这两个谓词。

    //@ Outside_Stateₗ()
    enter_critical();
    //@ exists l, Inside_Stateₗ() ** sll_box(G, l)
    push(x);
    //@ exists l, Inside_Stateₗ() ** sll_box(G, x :: l)
    exit_critical();
    //@ Outside_Stateₗ()

    另一个证明：

    //@ Outside_Stateₗ()
    enter_critical();
    //@ exists l, Inside_Stateₗ() ** sll_box(G, l)
    //@ ghost l = the l above
    //@ Inside_Stateₗ() ** sll_box(G, l)
    push(x);
    //@ Inside_Stateₗ() ** sll_box(G, x :: l)
    exit_critical();
    //@ Outside_Stateₗ()


*)

(** 2. 带栈操作协议的情况 *)

Module Case2.

(** 假如同样考虑前面提到的程序，但是对于临界区保护的内存空间，我们不仅仅约定，各个线程
    在关闭临界区时会保证其中是一个合法的单链表，还保证，各个线程只会向这个链表实现的栈
    中进行压栈操作，不会进行包括出栈之内的其他操作；那么，我们可以证明更细化的性质。
    
    首先，定义C程序临界区所保护内存区域的集合。由于临界区保护的内存总是存储了一个合法的
    单链表，因此可以使用单链表内的数据（即整数序列_[list Z]_）描述这块受保护的内存状
    态。由于我们验证liteOS使用的并发程序逻辑是基于STS（state transition system）的并
    发分离逻辑，这个状态集合我们就称为_[STS_stateₗ]_。*)

Definition STS_stateₗ := list Z.

(** 在基于STS的并发程序验证中，可以通过两种形式规定合法与非法的状态转移。其一是用一个
    STS_state集合上的二元关系规定合法的状态转移。在任何时候，这个二元关系之外的状态转
    移都是非法的。其二是通过一个token系统刻画额外的状态转移限制，这将在后续的例子中再做
    介绍。这个例子中只考虑第一种合法性规定，即需要明确规定，什么是合法的单步转移，什么
    是一次进出临界区期间允许对STS_state做的改变。下面定义说的是，单次操作允许不修改栈
    状态，也允许向栈中压栈一个元素。*)

Definition AllowedTransition (s1 s2: STS_stateₗ): Prop :=
  s1 = s2 \/
  exists z, s2 = z :: s1.

(** 根据这一点看，如果某时刻观察到STS_state为_[l0]_，那么下一次观察看到的状态一定形如
    _[l ++ l0]_，即 *)

Definition RelyTransition (s1 s2: STS_stateₗ): Prop :=
  exists l, s2 = l ++ s1.

(** 它们两者之间的关系（在没有token的情况下）可以概括为：_[RelyTransition]_是
    _[AllowedTransition]_的自反传递闭包。*)

(** 除此之外，被临界区保护的内存满足一条以STS_state为参数的断言，这个断言就是整个并发
    协议的全局不变式。
    
      //@ Let glob_inv(s) = sll_seg(G, s)

    基于这些设定，可以写出atomic_push规约如下：
    
      void atomic_push(int x);
      //@ With l
      //@ Require Outside_Stateₗ(l)
      //@ Ensure exists l', Outside_State(x :: l' ++ l)

    它表示，如果在执行atomic_push前，曾经观察到STS_state为_[l]_，那么在执行后，就可以
    说“曾经观察到了_[x :: l' ++ l]_这一STS_state”。

    下面带标注程序简要“说明”了上述规约的一种证明方法。

    //@ Outside_Stateₗ(l)
    enter_critical();
    //@ exists l', Inside_Stateₗ(l' ++ l) ** sll_box(G, l' ++ l)
    push(x);
    //@ exists l', Inside_Stateₗ(l' ++ l) ** sll_box(G, x :: l' ++ l)
    exit_critical();
    //@ exists l', Outside_Stateₗ(x :: l' ++ l)

    这一证明背后的严格语义是这样的。

    (1). 所有程序内存分为可以在临界区外直接读写的内存和受临界区保护的内存。上面的例子
         中，前者包括&x上存储的值。

    (2). 进入临界区时，就拥有这两者全部的读写权限；而为进入临界区时，没有后者的读写权
         限，而只知道STS_state处于某个可能的集合中。因此，该并发程序的程序状态（在不考
         虑token和嵌套临界区的情况下）可以是：

           InsideCritical, s, m
           OutsideCritical, X, m

         其中s表示当前STS_state，X表示下次进入临界区是可能看到的STS_state的集合，m表
         示当前拥有读写权限的内存。

    (3). 进入临界区的语义（在不考虑token和嵌套临界区的情况下）如下：

           (OutsideCritical, X, m1) ---(enter_critical())-->
           (InsideCritical, s, m1 ⊎ m2)

         其中 s ∈ X 并且 m2 满足 glob_inv(s)。

    (4). 离开临界区的语义（在不考虑token和嵌套临界区的情况下）如下：

           (InsideCritical, s, m1 ⊎ m2) ---(exit_critical())-->
           (OutsideCritical, X, m1)

         其中，要存在s'使得AllowedTransition s s'，并且X是根据RelyTransition从s’可
         达的所有STS_state构成的集合，m2 满足 glob_inv(s')，若有多种拆分得到m1与m2的方法，这一选择是angelic的。
       
    (5). Inside_Stateₗ(s)这一断言表示处于(InsideCritical, s)状态。
    
    (6). Outside_Stateₗ(s) 这一断言表示存在s'使得
    
           RelyTransition s s'
        
        并且当前处于(OutsideCritical, X)这一状态，其中X是又是根据RelyTransition从s'
        出发可达的所有STS_state构成的集合。
        
    当 p == 0x0040

    [0x0040 |-> 1] |= store(p, 1)
    [0x0040 |-> 1] |= exists x, x > 0 && store(p, x)

    (OutsideCritical, X, m) |= Outside_Stateₗ(l) iff.
      (1) m是空内存
      (2) 存在l'使得，X = { l'' ++ l' ++ l | l'': list }
          更一般的，存在l1使得
          (2.1.) RelyTransition l l1
          (2.2.) X = { l2 | RelyTransition l1 l2 }

*)

End Case2.

(** 3. 利用程序精化表述更精确的功能正确性性质 *)

(** 下面证明

      { Outside_Stateₗ(l) ** Outside_Stateₕ(l) }
          atomic_push(x) ⪯ atomic(AbstractPush(x))
      { exists l', Outside_Stateₗ(l') ** Outside_Stateₕ(l') }

    这里的精化关系“⪯”前一个程序的每一个行为都是后一个程序的可能行为。
    
    其中 AbstractPush(x) 是一个high level的临界区内程序，在这个简单情况下，可以看
    作：

        AbstractPush(x): STS_stateₕ -> STS_stateₕ -> Prop

    在STS系统的并发分离逻辑中，我们证明下面的spec：

    void atomic_push(int x);
    //@ With l
    //@ Require Outside_Stateₗ(l) **
                AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x)))
    //@ Ensure exists l,
                 Outside_Stateₗ(l) **
                 AsToExe(Outside_Stateₕ(l), skip)

    /*@ Outside_Stateₗ(l) **
        AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x))) */

    enter_critical();

    /*@ exists l',
          Inside_Stateₗ(l' ++ l) ** sll_box(G, l' ++ l) **
          AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x))) */

    push(x);

    /*@ exists l',
          Inside_Stateₗ(l' ++ l) ** sll_box(G, x :: l' ++ l) **
          AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x))) */

    exit_critical();

    /*@ exists l',
          Outside_Stateₗ(x :: l' ++ l) **
          AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x))) */

    /*@ exists l',
          Outside_Stateₗ(x :: l' ++ l) **
          AsToExe(Outside_Stateₕ(x :: l' ++ l), skip) */

*)

(** 4. 没有操作限制情况下的精化关系 *)

Module Case4.

Definition STS_stateₗ := list Z.

Definition AllowedTransition (s1 s2: STS_stateₗ): Prop := True.

Definition RelyTransition (s1 s2: STS_stateₗ): Prop := True.

End Case4.

(** 下面证明

      { Outside_Stateₗ(l) ** Outside_Stateₕ(l) }
          atomic_push(x) ⪯ atomic(AbstractPush(x))
      { exists l', Outside_Stateₗ(l) ** Outside_Stateₕ(l) }
      
    这里的精化关系“⪯”前一个程序的每一个行为都是后一个程序的可能行为。
    
    /*@ Outside_Stateₗ(l) **
        AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x))) */

    enter_critical();

    /*@ exists l',
          Inside_Stateₗ(l') ** sll_box(G, l') **
          AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x))) */

    push(x);

    /*@ exists l',
          Inside_Stateₗ(l') ** sll_box(G, x :: l') **
          AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x))) */

    exit_critical();

    /*@ exists l',
          Outside_Stateₗ(x :: l') **
          AsToExe(Outside_Stateₕ(l), atomic(AbstractPush(x))) */

    /*@ exists l',
          Outside_Stateₗ(x :: l') **
          AsToExe(Outside_Stateₕ(x :: l'), skip) */

*)

