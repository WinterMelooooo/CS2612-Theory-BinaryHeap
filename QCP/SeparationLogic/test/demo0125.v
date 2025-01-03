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
Local Open Scope string.

(** 注：本文件的Coq代码需要加载VST-IDE才能运行。请暂时不在运行状态阅读这些代码。 *)

(**

C 程序的例子

struct list {
  int data;
  struct list *next;
};

struct list *reverse(struct list *p) {
  struct list *w, *t, *v;
  w = ( void * ) 0;
  v = p;
  while (v) {
    t = v->next;
    v->next = w;
    w = v;
    v = t;
  }
  return w;
}
*)

(** 1. 定义C程序的分离逻辑谓词 *)

(** 在定义谓词时，Assertion表示“关于C语言内存的断言”，具体而言：
    (1) 这些Assertion可以描述内存中存储了什么，
    (2) 这些Assertion不会描述关于C程序局部变量地址的环境信息，
    (3) 这些Assertion可以描述关于C程序全局变量的信息，
    (4) C程序的struct/union/typedef相关的类型信息，可以在Assertion中涉及；
    如果只考虑32位整数，以及32位的指针，内存可以简化地看作地址到32位值的部分映射，但
    是我们的验证工具实际是会处理8位、16位、64位的情形的。 *)

(** 下面定义单链表的谓词Singly-Linked-List *)

Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = NULL |] && emp
    | z :: l0 => EX y: addr,
                   &(x # "list" ->ₛ "data") # Int |-> z ** 
                   &(x # "list" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

(** 假设_[x]_是一个存储struct list类型数据的地址，那么

      _[&(x # "list" ->ₛ "data")]_

    表示这个struct中data这个域的地址，也可以写作
    
      _[struct_field_address x "list" "data"]_。
      
    假设_[x]_是一个存储32位整数类型的地址，那么
    
      _[x # Int |-> y]_
    
    表示在_[x]_地址上存储了_[y]_这个有符号32位整数，也可以写作：
    
      _[store_int x y]_
    
    另外，_[emp]_表示不占据空间，_[EX]_表示存在，_[**]_表示分离合取，[| ... |]表示
    将与程序状态无关的数学命题当作断言。*)

(** 例如考虑一下情况：

         l = [0; 1; 2]
         x                                        = 0x0040
         &(x # "list" ->ₛ "data")     &(x -> data) = 0x0040
         &(x # "list" ->ₛ "next")     &(x -> next) = 0x0044
         x -> next                                = 0x0100
         &(0x0100 -> data)                        = 0x0100
         &(0x0100 -> next)                        = 0x0104
         0x0100 -> next                           = 0x0108
         ...

         如果
         x = 0x0040, z = 0, y = 0x0100

         [0x0040 |-> 0] 满足 &(x # "list" ->ₛ "data") # Int |-> z

         [0x0044 |-> 0x0100] 满足 &(x # "list" ->ₛ "next") # Ptr |-> y

         [0x0040 |-> 0, 0x0044 |-> 0x0100] 满足 
            &(x # "list" ->ₛ "data") # Int |-> z ** 
            &(x # "list" ->ₛ "next") # Ptr |-> y

    *)
        
(** 问：验证工具是否支持强制类型转化？

    答：是的。

    x # Int |-> -1
    x # UInt |-> 2^32 - 1

    两者是等价的。 *)

(** 下面这个定义表示在一个二阶指针_[x]_上存储了一个链表的头指针，这个谓词涵盖了地址
    _[x]_与链表所涉及的所有内存权限。*)

Definition sllb (x: addr) (l: list Z): Assertion :=
  EX y: addr, x # Ptr |-> y ** sll y l.

(** 2. 临界区内C函数的前后条件 *)

(** 如果一个C函数是一个临界区内的函数，那么它的规约包括一个逻辑参数列表，和一组前后条
    件。例如，下面C函数的规约就读作：对于任意整数序列l，如果reverse(p)函数执行前，
    _[sll(p, l)]_性质成立，那么函数执行后它的返回值满足_[sll(__return, rev(l))]_。
    这里的_[sll]_就是我们刚刚定义的谓词，_[rev]_是Coq标准库中的序列取反函数。

      struct list *reverse(struct list *p);
        /*@ With l
            Require sll(p, l)
            Ensure sll(__return, rev(l))
         */

      void reverse2(struct list *p);
        /*@ With l
            Require sll(p, l)
            Ensure sll(p, rev(l))
         */

      void reverse3(struct list * * q);
        /*@ With l
            Require sllb(q, l)
            Ensure sllb(q, rev(l))
         */

      void reverse4(struct list * * q);
        /*@ With p l
            Require q # Ptr |-> p ** sll(p, l)
            Ensure  q # Ptr |-> p ** sll(p, rev(l))
         */

      int add1(int x);
        /*@ Require MIN_INT <= x < MAX_INT
            Ensure __return == x + 1 */

      void add2(int * x);
        /*@ With v
            Require MIN_INT <= x < MAX_INT &&
                    x # Int |-> v
            Ensure x # Int |-> v + 1 */

    这样的C函数规约中，前条件是一个关于C程序内存与函数形参数值的断言，后条件是一个关于C
    程序内存、函数形参数值与函数返回值的断言，它们都不是上面在Coq中所写的
    _[Assertion]_。在使用我们的验证工具时，可以在C文件中写入上述注释，验证工具会以正确
    的方式处理这些断言。*)

(** 3. 临界区内C程序语句间的断言与不变量 *)

(** 前面提到的reverse函数可以使用下面循环不变量证明。

      struct list *w, *t, *v;
      w = ( void * ) 0;
      v = p;
      /*@ Inv
            exists l1 l2,
              l == app(rev(l1), l2) &&
              sll(w, l1) ** sll(v, l2)
       */
      while (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
      }
      return w;

    这里的循环不变量表示进入循环时，以及每次执行完循环体后重新检查循环条件前，C程序状态
    应当满足的性质。因此，这个不变量实际上是关于C程序内存与C变量相关环境信息的断言。例
    如，sll(w, l1)实际说的是：

      exists ptr_w value_w,
        &w == ptr_w &&
        ptr_w # Ptr |-> value_w **
        sll value_w l1

    因此，这个断言也不是一个前面所说的_[Assertion]_，我们的验证工具会正确处理这些写在C
    程序中的循环不变量标注或断言标注。 *)

(** 4. 逐层定义的谓词与逐层验证的函数 *)

(** 假设程序中用单链表形式存储了一个整数的有穷集合，这个集合中的数以升序存储。那么我们
    就可以在_[sll]_谓词的基础上，定义“存储整数集合”。*)

Definition set_list_match (X: Z -> bool) (l: list Z): Prop :=
  forall z: Z, X z = true <-> In z l.

Fixpoint increasing_aux (a: Z) (l: list Z): Prop :=
  match l with
  | nil => True
  | cons b l0 => a < b /\ increasing_aux b l0
  end.

Definition increasing (l: list Z): Prop :=
  match l with
  | nil => True
  | cons a l0 => increasing_aux a l0
  end.

Definition store_Z_set (x: addr) (X: Z -> bool): Assertion :=
  EX l: list Z,
    [| set_list_match X l |] &&
    [| increasing l |] &&
    sll x l.

(** 在验证C程序时，我们可能会验证一些关于单链表的程序性质。例如：

      struct list * push(struct list * p, int x);
        /*@ With l
            Require sll(p, l)
            Ensure sll(__return, cons(x, l))
         */

      int pop(struct list * * q);
        /*@ With x l
            Require sllb(q, cons(x, l))
            Ensure __return == x && sll(q, l)
         */

      struct list * remove(struct list * p, int x);
        /*@ With l1 l2
            Require sll(p, app(l1, cons(x, l2)))
            Ensure sll(__return, app(l1, l2))
         */

    在这些C函数的基础上，我们又可以实现关于集合的操作，并验证相关性质：

      struct list * remove(struct list * p, int x);
        /*@ With X
            Require x ∈ X && store_Z_set(p, X)
            Ensure store_Z_set(__return, X \ x)
         */
    
*)

