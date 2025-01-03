# 标注语言的语法说明

本文档主要是为了说明前端的标注语言的相关语法，具体如何写正确的标注请参考``T1_sequential_C_program_verification.md``和``T2_polymorphic.md``

我们的标注语言都是以``/*@  ... */``或者``//@ ...``的注释形式给出，主要分为以下几类：

- 引入Coq中定义的类型、函数和谓词。

- 函数的规范描述。

- 函数中插入的辅助证明的标注。

在后文中，如果没有特别说明，我们使用assertion表示一般的断言标注。我们将会在最后介绍assertion的语法

### 引用Coq内容的标注语法

目前引用Coq内容的标注都应当写在函数的外部，不支持在函数内部声明特定类型的写法。

首先，为了保证生成的证明文件能够获取到相关定义，我们需要通过以下语法来标注相关的Coq文件依赖：
```
/*@ Import Coq Require Import filename */
/*@ Import Coq Import filename */
/*@ Import Coq Local Open Scope scopename */
```

另外，为了方便用户，我们并不需要用户直接在标注中写明相关类型、函数和谓词的定义, 只需要提供对应的函数/谓词的类型即可，下面是一个例子：
```
/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (return : {Sigma} {A} -> A -> program Sigma A) 
               (applyf: {A} {B} -> (A -> B) -> A -> B) */
```

其中``program``和``unit``是两个Coq Type, ``program``还需要额外的两个类型参数。我们要求所有的类型声明和函数/谓词声明应该分开写。

``return``和``applyf``是两个函数，我们用``{A}``表明它需要的隐式类型参数, `` -> ``表示类型的imply，``program Sigma A``表示function application。``Z``,``Prop``和``Assertion``是我们的内置类型，分别对应Coq中的``Z``,``Prop``和``Assertion``(这是我们在Coq中实现的断言的类型)。

除此之外，考虑到``Definition addr := Z.``的情况，我们同样允许用户通过``/*@ Extern Coq addr := Z */``声明addr类型并且在类型推断过程中把它当作``Z``。

最后，由于Coq中的Record定义不仅会创建类型，对应的field也能被当作函数使用，为了方便，用户可以直接写类似下面的定义来定义Record类型：
```
/*@ Extern Coq Record StableGlobVars {
  g_taskCBArray: Addr;
  g_swtmrCBArray: Addr;
  g_allSem: Addr;
  g_allQueue: Addr;
}*/
```

同样，定义之后``g_taskCBArray``也会被视作是一个``StableGlobVars -> Addr``的函数。

目前为止Record的声明不能带额外的参数，也不能指明构造函数的名字，可能之后考虑支持。

### 函数规范描述语法

函数规范用于描述函数执行的前后条件，表示的是函数的性质，也是一般而言我们的证明目标。

通常而言，对于一个函数，我们需要在声明和定义的时候都提供一个函数规范标注，分别用于被调用函数的符号执行和该函数的验证，下面是一个例子：
```
struct list *reverse(struct list *p) 
/*@ With {A} storeA (l : list A)
    Require sll(storeA, p, l)
    Ensure sll(storeA, __return, rev(l))
*/;

struct list *reverse(struct list *p) 
/*@ With {A} storeA (l : list A)
    Require sll(storeA, p, l)
    Ensure sll(storeA, __return, rev(l))
*/
{
  ...
}
```

如上面的例子所示，通常一个函数规范包括三个部分``With``, ``Require``, ``Ensure``，当然，也有可能某个函数不需要``With``因此只有后面两个部分。

- ``With``表示在整个函数符号执行中使用的通用的逻辑变量、函数甚至是相关类型。
   在上面的例子中，``A``是一个类型参数，``storeA``是一个``Z->A->Assertion``类型的函数, ``l``是一个``list A``类型的函数。这里没有给出``storeA``的类型是因为我们能够根据``sll``的类型推断出storeA的类型。 ``With``中的参数可以近似理解为函数的逻辑变量输入参数，一般而言可以根据调用时的断言自动推断出来，如果没有成功推断，即出现了``Cannot derive the precondition of function xxx``, 可能是缺少必要的strategy，也有可能是需要指定相关的逻辑变量/函数。对于后者，我们可以通过``where``来进行指定：
   ``p = reverse(q) /*@ where A = list Z, storeA = storeIntArray */;``

- ``Require``表示进入函数时的前条件

- ``Ensure``表示函数结束时的后条件，特别的，我们使用``__return``表示返回值。
    我们规定后条件中出现的程序变量形参代表的是参数在函数入口处的值。比如在下面的例子中，函数标注表明返回值是25。
    ```
    int sqr5(int x)
    /*@
      Require x == 5
      Ensure __return == x * x
    */
    ```

值得注意的是，``With x Require P(x) Ensure Q(x)``描述的其实是``forall x, { P(x) } c { Q(x) }``的霍尔三元组，因此在符号执行过程中，每一个逻辑变量是不会发生变化的。 自然下面的函数标注是错误的：
```
void inc(int *y)
/*@ With x v
  Require x == v && data_at(y, x) 
  Ensure x == v + 1 && data_at(y, x) 
*/;
```

正确的写法应该为:

```
void inc(int *y)
/*@ With x 
  Require data_at(y, x) 
  Ensure data_at(y, x + 1) 
*/;
```

或是

```
void inc(int *y)
/*@ With x 
  Require data_at(y, x) 
  Ensure exists x', x' == x + 1 && data_at(y, x') 
*/;
```

全局变量与普通的形参变量不同，断言中的``x``表明``&x``上存的值, 因此下面的例子表示全局变量``x``在调用一次函数``f``之后会增加1， ``x@pre``表明变量x在前条件断言中的值。
```
void f()
/*@
  Require 0 <= x && x <= 10
  Ensure x == x@pre + 1
*/
```



另外，也许一个函数具有多种函数规范，我们需要在调用的时候指明使用的是哪个规范，以``swap``函数为例：
```
void swap(int * px, int * py)
/*@ neq <= all
    With x y
    Require x == *px && y == *py
    Ensure  y == *px && x == *py
*/;

void swap(int * px, int * py)
/*@ eq <= all
    With x
    Require px == py && x == *px
    Ensure  x == *py
*/;

void swap(int * px, int * py)
/*@ all
    With x y
    Require x == *px && y == *py || px == py && x == y && x == *py
    Ensure  y == *px && x == *py || px == py && x == *py
*/
{
  int t;
  t = * px;
  * px = * py;
  * py = t;
}

void swap_test1(int *x, int *y) 
/*@ 
   Require x != y && *x == 1 && *y == 2
   Ensure  *y == 1 && *x == 2
*/
{
  swap(x, y) /*@ where (neq) */;
}

void swap_test2(int *x, int *y) 
/*@ 
   Require x == y && *x == 1
   Ensure  *y == 1
*/
{
  swap(x, y) /*@ where (eq) */;
}
```

在证明这个函数时，我们需要对``px``和``py``是否指向同一个地址进行讨论，因此我们写出了函数标注``all``。但是在调用的时候，往往只会使用某一种情况，于是我们给出了``neq``和``eq``两种函数标注，并在调用的时候通过``where (eq)``方式指明这里使用的函数标注为``eq``。

对于这种情况，我们规定所有调用时用到的函数标注都能被证明时使用的函数标注推出，并且证明时使用的函数标注必须唯一。

### 函数中的断言标注语法

函数中的断言标注主要是为了辅助符号执行，包括循环不变量，读写操作时的谓词拆分以及函数调用的相关参数提供。为了减轻用户的负担，我们默认提供的断言都是部分断言（只描述了部分程序变量的信息），如果需要强调该断言为完整断言(即描述了全部程序变量的相关信息)，可以在标注最开头加上``Assert``，比如``/*@ Assert ... */``

#### 循环不变量语法

区别于一般的断言，我们需要在断言前加上``Inv``来表明这是一个循环不变量。下面展现了三种循环的循环不变量位置:
```
/*@ Inv
      0 <= i && i <= n && n == n@pre && ret == sum(sublist(0, i, l))
*/
while (i < n) {
  ret += a[i];
  ++i;
}
```

```
do {
    ret += a[i];
    ++i;
} /*@ Inv 0 <= i && i <= n && n == n@pre && ret == sum(sublist(0, i, l)) */
while (i != n);
```

```
/*@ Inv
      0 <= i && i <= n && n == n@pre && ret == sum(sublist(0, i, l))
*/
for (i = 0; i < n; ++i) {
  ret += a[i];
}
```

可以观察到，while循环和do-while循环的循环不变量都在while之前，for循环的循环不变了在for之前，并且里面涉及到的程序变量都必须要在循环之前定义好(比如说i)。

C标准中不允许在``for(c1;c2;c3) c4``的``c1``位置定义变量，我们也保留了这个设定，并且我们会在执行完c1之后进行invariant check，正如do-while中会先执行完一次循环体之后再进行invariant check。

特别的，有的时候循环不变量并没有那么容易被写出，我们允许用户通过在循环体内给出必要的断言，然后我们自己进行循环不变量的推导。
```
while (x < a) {
  x = x + 1;
  //@ (1 <= a) && (a <= 100) && (x <= a)
}
```
但是我们要求循环体内每条执行分支都至少要有一个断言，比如下面的例子就是一个非法的例子：
```
  while(cur) {
    x = cur -> head;
    if (x > 0) {
      s += x;
      /*@ x == cur -> head && s == x + sum(pos(l1)) * sllseg(head,cur, l1) * sll(cur -> next) */ 
    }
    else {
      cur -> head = abs(x) + 1;
    }
    cur = cur -> next;
  }
```

这个例子中缺少了else分支的断言，因此我们没有办法推导出正确的循环不变量。

#### 谓词拆分替换

有的时候，我们需要对一些谓词进行等价替换，有可能是需要拆分出即将被读写的地址，有可能是为了合并一部分内存来简化断言。这些等价替换有的能够被strategy自动实现，但是有的必须要人手动指出，特别是从多种替换方案中选择一个的时候。因此我们提供了``which implies``，下面是一个例子：
```
/*@ exists l1a, ((* pt) == y) && sllbseg(pres, pt, l1a)
      which implies
      sllseg(*pres, y, l1a) && pt == pt
   */
```
在符号执行的过程中，我们会检查``which implies``的前断言是否能被推出，如果能，我们则用后断言将其替换。这里实际上可以当做一个简单的函数调用, ``With``是前断言的exists, ``Require``是前断言, ``Ensure``是后断言。与函数调用不同的是，这里我们会额外产生前段言推出后断言的待证明结论。

出于简化断言的角度，我们有时候希望能够删除前断言中的一些逻辑变量，以下面的程序为例：
```
/*@ exists [rev_l2],
          cons(x, l) == rev_l2 &&
          sll(q -> l1, rev_l2)
        which implies
        sll(q -> l1, cons(x, l)) */
```
我们希望删除``rev_l2``这个逻辑变量，因此我们在exists中使用``[rev_l2]``表明这应该被视作``Require``中的exists一起被替换掉。


对于多分支的情况，可以写
```
/*@ A || B 
  which implies 
    C || D
```

对于当前的断言``P || Q``, 我们会将P中包含A的部分替换成C，Q中包含B的部分替换成D，如果此时分支数不匹配我们将会拒绝which implies请求。

如果希望把1个分支变成多个分支，那么可以写
```
/*@ A || B 
  which implies 
   C || (D || E)
*/
```
对于当前的断言``P || Q``, 我们会将P中包含A的部分替换成C，Q中包含B的部分替换成D和E变成两个新的分支，如果此时分支数不匹配我们将会拒绝which implies请求。

#### 函数调用的相关参数提供

正如前一节所介绍的，我们可以用``f = g(x) /*@ where (spec_name) arg1 = e1, arg2 = e1 ; type_arg1 = T1, type_arg2 = T2 */; ``来对函数调用的spec和With参数做相关的指定。

特别的，如果一个语句中包含多个函数调用应该写作
``f = g(x) /*@ where */ + h(x) /*@ where */;``

如果``With``中没有变量参数只有类型参数应写作``/*@ where (spec_name) ; type_arg1 = T1 , ... */``

#### 部分断言标注和完整断言标注

对于部分断言标注(包括普通断言，循环不变量和which implies)，我们要求断言的分支数和跟据符号执行计算出来的分支数相同，否则我们会直接报错。

对于完整断言标注，我们会直接替换成用户写的断言，然后生成对应的待证明结论，此时分支数不影响符号执行。

### 一般的断言标注语法

从上面的例子中我们已经看到了很多断言标注，这里我们简单介绍一下断言标注的基本语法和一些上面没有涉及到的特性。

#### 通常的断言标注语法

我们的断言通常是以$\exists \bar{x}, P_1 \&\& P_2 \&\& \cdots \&\&Q_1 * Q_2 * \cdots * Q_n$的形式给出。其中$P$是一些内存无关的命题，$Q$是一些内存相关的命题。

特别的，我们允许用户在断言中写C表达式，比如``x -> next == y``,这里其实是描述了内存中$x$的next指针指向了$y$； ``*x == 1``描述的是``data_at(x,1)``。

我们用``->``表示类型的imply，用``=>``表示命题的imply。

#### Feature : shadowed variable

考虑到可能会出现重名的局部变量，C程序中同名变量会选取最近的scope的定义，我们也是如此设定，比如在下面的断言中，$x$表示的是if中定义的局部变量$x$。
```
int x;
x = p;
if (x > 1) {
  int x;
  x = 20;
  /*@ x == 20 */
  ...
}
else {
  ...
}
```

但如果我们想说这里$p$的值保持和外面的$x$相同，此时就不能用``p == x``表达这个意思。我们提供了`#x`来表示上一层$x$, 这里断言应该写为``p == #x && x == 20``。

#### Feature : mark and old value

更进一步，我们可能需要想说之前的某个时候某个变量的值。这时我们引入了mark和old value的特性。
```
int x;
int y;
x = p;
/*@ x == p @mark s1*/
if (x > 1) {
  int x;
  x = 20;
  /*@ x == 20 && p == x@s1 */
  ...
}
else {
  ...
}
```

我们用``@mark name``来对断言进行标记，然后用``e@name``表示在$name$这个断言中$e$的值，比如可以写``(x + y)@name``。在上面的例子中``p == x@s1``就起到了``p == #x``的类似作用。

值得注意的是，这里我们不能写``p == #x@s1``，因为在断言1的外层并没有别的x的定义，因此这里会出现求值失败，同理我们不能写``p == y@s1``因为在断言1中$y$还没有初始化。

我们要求mark标注必须紧跟单个断言,比如``A || B @mark s1``这里mark的其实是断言B,如果想要mark断言A则得写成``A @mark s1 || B``。

最后，我们允许使用``@pre``表示在``Require``中的前条件的值。





