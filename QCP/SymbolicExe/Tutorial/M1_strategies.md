# strategy文件撰写规范

### strategy 使用情况说明

用户需要提供相应的strategy文件来指导solver如何对自定义的谓词进行断言推导。需要使用strategy的场景主要是:
- 用户自己插入的部分断言，包括循环不变量(Inv),普通断言, which implies(前条件检查).
- 函数调用，主要是为了检查是否满足函数前条件. 
- 对内存地址的读取/写入，这里我们要求必须要在断言中出现显式的data_at(p,_)才能对p地址进行相应的操作.
- return时检查是否满足函数后条件.

不会在符号执行中调用strategy的场景:
- 用户自己插入的完整断言.
- which implies的前条件推后条件.

其中which implies的前条件推后条件我们不会在符号执行的过程中调用strategy, 但是我们会在输出proof goal的时候调用, 来判断应该输出到auto文件还是manual文件当中.

在符号执行的过程中，每次使用某一条strategy, 都会打印``applying rule (file_name, strategy_id)``, 表明使用了哪个文件中的哪条strategy, 便于debug.

### strategy 文件格式

我们默认接受的strategy文件应该是形如sll_DSLFileLists的文件.
```
add:/examples/sll.strategies
add:/examples/common.strategies
```

add表示需要添加的strategies文件, 冒号之后是文件所在的相对整个符号执行文件夹的路径。

在符号执行是通过``-strategy-file=../examples/sll_DSLFileLists``的方式来调用指定的strategy文件.

如果不希望增加额外的sll_DSLFileLists, 也可以在C代码中增加`` /*@ include strategies "sll.strategies" */``的标注来指明需要使用什么strategies文件。
注意``" "``里的文件路径是相对于c文件的路径，strategies文件的include应该在所有相关定义都写完之后给出，否则可能会导致parse strategies文件失败。

### strategy 格式

对于单个.strategies文件,它包括若干的环境标注内容和若干的strategy,形如
```

...

id : 6
priority : core(0)
left : data_at(?p : Z, ?ty, ?x : Z) at 0
right : data_at(p, ty, ?y : Z) at 1
check : absense(should_be_equal(x, y));
action : right_add(x == y);
         left_add(should_be_equal(x, y));

...

```

这里include的路径是相对于strategy文件的路径。

我们会在strategy parse的时候检查谓词信息是否在环境中出现, 在符号执行的时候检查strategy的环境是否是c程序环境的子集。

通常而言，一个strategy包括id, priority, left, right, check, action六个部分。
- id表示这个strategy的编号，通常是0~2147483647之间的一个整数。我们规定每个文件内部的id不能重复，不同文件的不同strategy id可以重复.
- priority表示这个strategy的优先级和作用的strategy scope。我们内置的scope主要有core, post, Pcancel，具体每个scope的作用范围将会在之后进行解释。里面的数字表示在当前scope的优先级，通常是0~20之间的一个整数，数字越大优先级越低.
- left/right表示在A |-- B的左侧(A)和右侧(B)中去匹配对应的表达式. ``at number``表示这个表达式的编号为number. 我们允许写多个left/right,我们会按照写的顺序进行匹配。
- check表示需要额外检查左侧需要满足的性质. ``absence(P)``表示如果左边没有匹配到P这个命题，我们就做之后action的操作. ``infer(P)``表示如果左边能够通过smt_solver推出P这个命题,我们就做之后action的操作.
- action表示这条strategy会对原来的A |-- B进行的操作. 主要的操作包括:
``left_erase(number)`` ``right_erase(number)`` 删除左/右对应编号为的number的表达式.
``left_add(e)`` ``right_add(e)``在左/右增加对应的表达式.
``left_exist_add(var)`` ``right_exist_add(var)`` 在左/右增加existential variable.
``instantiate(x -> y)``把存在变量x填成y.
``substitute(x -> y)``把x替换成y.

strategy内的表达式与c程序中断言表达式基本一致, 这里对一些特殊语法进行说明:
- ?p 表示 p是一个pattern expression, solver会去匹配这里的表达式然后把之后所有出现p的地方进行替换. 我们要求只需要在第一次出现的位置用?标注这是一个pattern expression即可.
- atom p 表示 p是一个pattern variable, 它要求这里只能匹配到变量而不能是表达式
- {}表示apply on Type variable, {?A} 表明对A这个Type variable进行pattern
- a : Z 表明a的Type是Z, 一般情况下可以不需要写，但是由于类型推断不一定能推出所有的类型，所以在exist_add的时候需要提供对应变量的类型。这里的Type允许写``<A>``表示名字为A的Type, ``A``表示类型变量A, ``list{A}``表示参数为A的链表类型, ``A -> B``表示函数类型. 我们同样允许对函数进行pattern,但这个时候要求必须标注函数的类型，比如``(?storeA : Z -> ?A -> asrt)(?p, ?x)``, 如果不标注可能会导致类型推断失败. 如果类型变量A与环境中定义过的类型同名，我们会直接做替换。
- 内置的Type: ``Z``, ``Assertion``, ``Prop``, 分别可以写``Z``, ``asrt/Assertion``, ``Prop``(不区分大小写).
- field_addr. 在c程序断言中我们允许写->和.来表示field的访问。但是strategy目前还没有支持这样的notation. 因此只能用field_addr(x,struct_name,field_name)来表示x的field_name的地址.
- data_at. 由于在strategy里面我们严格区分了prop和sep, 因此``x->tail == a``只能写成``data_at(field_addr(x,list,tail),PTR(struct list),a)``. 其中第二个参数表示对应地址的CType. 我们允许用I32,U32,I64,U64来作为int, unsigned int, long long, unsigned long long的简写, 对应的C数据结构的名字需要标注struct/union/enum作为类型,PTR(CType) 表示对应CType的指针. 
- ``nil{A}``, ``empty_tree()``. 对于像是nil, empty_tree之类的类型实例，我们需要写成零元函数的形式，与叫做empty_tree的pattern variable进行区分. 其中nil{A}表示类型参数为A的空链表实例，这里由于需要提供类型，因此可以省略(). 
- 一些特别的规定：我们不允许类似``(?f : Type){A}()``或者``(f : Type){A}()``的写法.


### 关于priority scope的额外说明
我们允许用户自定义scope并且在C程序中通过``by xxx``指明当前的断言推导除了core以外还额外需要使用哪个scope中的strategy。下面是一些例子：
```
/*@ sll(x , l) * sll(y, l1) by sll */


/*@ Inv 
      sll(x , l) * sll(y, l1) by sll */

/*@ exists l2, v != 0 && sll(v, l2) by sll
    which implies
    exists l2_new, l2 == cons(v -> data, l2_new) && sll(v -> next, l2_new) by sll */

split_rec(t, q, p) /*@ where(low_level_spec_aux) l1 = l2, c = reversepair,  X = X by sll_merge*/; 

```

我们内置了core,post,Pcancel三种scope. 这几种scope中的strategy的使用范围为:
- core : 几乎所有的断言推导
- post : 在load/store操作后，把拆开的sep进行合并。目前主要用于数组读写。
- Pcancel : 在Partial solve之后对prop部分进行操作。由于我们对于prop部分采取的策略是全部保留，因此有可能会保留一些不需要的prop. 因此可以写Pcancel scope的strategy来进行消去.


### Strategy Soundness Generator
我们要求符号执行所使用的每一条strategy都是sound的，因此符号执行的VC_Correct中增加了使用的strategy file的soundness proof证明。如果不想引入可以使用--no-strategy-gen的编译选项。

我们额外提供了StrategyCheck用于strategy soundness的生成, 相关命令为：
```
wsl : ASAN_OPTIONS=detect_leaks=0 build/StrategyCheck --strategy-folder-path=../../annotated_simplec/examples/ --no-logic-path --input-file=../examples/poly_sll.strategies
```

```
cygwin : build/StrategyCheck --strategy-folder-path=../../annotated_simplec/examples/  --no-logic-path --input-file=../examples/poly_sll.strategies
```

这里``--input-file=``指明了输入文件的位置，由于include的路径是相对于strategy文件的路径，因此我们推荐使用这种方式而不是``< input_file``的形式来指定输入。

``--strategy-folder-path=xxx``表明生成的相关文件放于哪个文件夹。

``--coq-logic-path=xxx``表明依赖的的相关文件的逻辑路径, 默认为``--no-logic-path``

``--strategy-proof-logic-path=xxx``表明生成的strategy proof文件属于哪个逻辑路径，用于生成文件之间Import的时候以及符号执行文件Import的时候使用。默认为``--no-strategy-proof-logic-path``


### 常见的符号执行报错及原因分析

``Fail to find lib for scope: A`` 这是因为在c程序中指明需要对应scope的strategy但是并没有在lib中找到这个scope.

``bison : error message around line number ``表明在第number行左右bison报错，错误信息为error message，通常会是syntax error. 这表明include的文件中有语法错误。

``strategy parser: error mesage around line number`` 表示在第number行左右strategy parser报错, 错误信息是error message, 通常会是syntax error. 这表明strategy文件中有语法错误。

``Invalid Function Structure (x : f){A}.`` 表明在strategy中写了``(x : f){A}``类似的表达式，我们不支持这种表示。

``Cannot find function A in the environment.`` 通常是A这个谓词没有在c程序断言标注定义中出现.

``f :Expected paras(a) types(b); Received paras(c) types(d) in function func``表示f这个谓词需要a个输入参数和b个类型参数,但是现在有c个输入参数和d个类型参数,报错位置是func这个函数. 一般情况下这个报错原因在于某个谓词提供的类型标注/环境中的类型标注与实际使用不匹配.

``Type inference error: cannot not unify (<A>) with (A) ``这是因为前者被当作了一个名字为A的已经被定义过的类型，而后者是一个类型变量A，所以类型不相同。

``Type inference error: left pattern should be of type Prop or Assertion``这个表示left pattern对象不是一个Prop或者Assertion, 我们目前不支持``?f : Type at number``的表示.

``Type inference error: action add pattern should be of type Prop or Assertion``这个表示action增加的pattern经过type check,Type不是Prop或者Assertion, 可能是add了一个单独的变量或者是类似cons之类的计算函数.

``Cannot unify types A and B around line number`` 这是前端parser报的错，说明在第number行附近的断言出现了Type A和Type B不匹配。$\mathbb{SP}$表示Assertion，$\mathbb{PP}$表示Prop.

``Partial Solve Failed``这个表明strategy不足或者错误，需要检查它的apply_rule列表来慢慢分析. 如果发现了``number -> NULL``, 表明他不知道这个存在变量如何赋值.