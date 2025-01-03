# QCP 项目介绍及使用说明

QCP是由上海交通大学曹钦翔老师实验室在VST, VST-A的基础上进行开发的C程序验证工具。

### 原理说明

QCP延续了VST-A的思路，接受一个带标注的C程序为输入，会基于标注断言对C程序进行符号执行，生成待证明的Coq proof。用户只需要证明相关的Coq proof就能够完成对C程序的证明。

QCP项目分为C实现的符号执行部分和Coq实现的后端证明部分。

在符号执行部分，我们实现了更为丰富的标注语言，能够接受更加复杂的C程序语法，并且使用了strategy和SMT solver来进行断言的自动求解，减少了用户的证明工作量。我们将整个证明分别输出为四个文件``xxx_proof_goal``、``xxx_proof_auto``、 ``xxx_proof_manual``、``xxx_proof_check``，分别表示所有待证明结论列表，已经通过strategy和SMT solver自动解决的相关证明，需要手动完成的相关证明和所有证明都已经完成的检查文件。具体的标注可以参考``SymbolicExe/Tutorial/T0_frontend_assertions.md``, strategy的使用和soundness生成可以参考``SymbolicExe/Tutorial/T3_strategies.md``

在后端证明部分，我们实现了与VST类似的proof tactics，相关tactic的介绍可以参考``SeparationLogic/README.md``。


### 编译与使用


#### 相关环境依赖

推荐使用cygwin和wsl进行工具的使用，不推荐使用powershell，可能会出现未知错误。
mac环境请不要使用Apple Clang作为编译器, Clang和gcc的部分行为不一致会导致生成结果错误从而使Coq编译失败。

```
Coq version = 8.15.2
Flex version = 2.6.4
Bison version = 3.8.1 / 3.8.2 
gcc version <= 8.13.1 (更高的版本还未经过测试)
cmake version >= 3.5 
```
#### SymbolicExe 编译

wsl环境下不需要额外配置文件
cygwin/mac环境下可能需要在``SymbolicExe/test``文件夹下添加配置文件CONFIGURE(大小写敏感、无后缀), 提供gcc所在路径，eg: `C_PATH=/usr/bin/gcc`，推荐使用绝对路径。

完成上面的配置之后，可以使用下面的指令进行编译，冒号前表示当前终端所在的文件夹，冒号后表示使用的指令：

wsl：
```
SymbolicExe/test : sh ./gen.sh
```

cygwin：
```
SymbolicExe/test : sh ./gen.sh
```

mac:
```
SymbolicExe/test : sh ./gen.sh
```

powershell:
```
SymbolicExe/test : sh ./gen.sh windows
```

如果sh报错可能是因为git clone下来的文件中都是以CRLF结尾，需要把它转化成LF结尾。

编译完成之后可以在``test``目录使用下面的指令运行：
wsl:
```
build/symexec --goal-file=../../SeparationLogic/examples/sll_goal.v --proof-auto-file=../../SeparationLogic/examples/sll_proof_auto.v --proof-manual-file=../../SeparationLogic/examples/sll_proof_manual.v --no-logic-path --strategy-file=../examples/sll_DSLFileLists --input-file=../examples/sll.c;
```

cygwin:
```
build/symexec --goal-file=../../SeparationLogic/examples/sll_goal.v --proof-auto-file=../../SeparationLogic/examples/sll_proof_auto.v --proof-manual-file=../../SeparationLogic/examples/sll_proof_manual.v --no-logic-path --strategy-file=../examples/sll_DSLFileLists --input-file=../examples/sll.c;
```

我们同样提供了``test.sh``用于批量运行测试文件。

这里对相关运行选项进行说明,其中带有 \* 的运行选项是我们推荐指定的:

- --gen-and-backup，表示如果输出的 coq 文件已经存在，就先将其转存为一个 backup 文件，再修改文件内容；如果不包含这个选项，将会默认覆盖goal文件和proof-auto文件，不修改proof-manual文件

- (\*) --goal-file=\<file\> 表示输出的 proof goal 的路径；

- (\*) --proof-auto-file=\<file\> 表示输出的 proof auto 的路径；

- (\*) --proof-manual-file=\<file\> 表示输出的 proof manual 的路径；

- --coq-logic-path=\<path\> goal-file 所在的 coq 逻辑路径；

- (\*) --no-logic-path 不设置 goal-file 的 coq 逻辑路径。不能和 --coq-logic-path=\<path\> 同时使用

- --no-strategy-gen 不生成 strategy 的 soundness 证明目标，如果不包含这个选项默认为不生成

- --no-strategy-proof-logic-path 不指定strategy proof 文件的 Coq 逻辑路径，如果不包含这个选项默认为不指定

- --strategy-proof-logic-path=\<path\> strategy proof 文件的 Coq 逻辑路径，如果不包含这个选项默认为不指定

- (\*) --strategy-file=\<file\> 表示使用的 strategy 的配置路径；

- --program-path=\<path\> 表示将要证明代码的 Coq 表示输出到哪个路径；如果不包含这个选项则不输出

- (\*) --input-file=\<file\> 表示输入的文件路径；如果不包含这个选项则从 stdin 输入

如果代码中含有 `#define`、 `#include` 等预处理指令，请使用 `cpp -P -C <input file> <output file>` 来得到预处理后的C源文件。目前的解析器只原生支持了 `#include`。

#### SeparationLogic 编译

需要在``SeparationLogic``文件夹和``SeparationLogic/unifsl``文件夹下分别添加配置文件CONFIGURE(大小写敏感、无后缀)，用于配置coq的路径. 下面是一个在cygwin中使用的配置例子：
```
COQBIN = /cygdrive/d/Coq-8.15/bin/
SUF=.exe
```

其中如果试图在wsl/powershell中使用windows下安装的Coq，请务必提供SUF，否则可能会出现类似``/bin/coqdep not found``的报错。

完成上面的配置之后，可以使用下面的指令进行编译，冒号前表示当前终端所在的文件夹，冒号后表示使用的指令：
```
SeparationLogic : cd unifysl
SeparationLogic/unifysl : make depend ; make
SeparationLogic/unifysl : cd ..
SeparationLogic : make depend ; make
```

编译完成之后就可以按照正常Coq方式进行使用。

### 相关论文发表

暂无

### 开发人员名单和联系方式
吴熙炜(yashen@sjtu.edu.cn) 项目维护, soundness proof证明
陆潇扬(luxy1115@sjtu.edu.cn) 前端开发和维护
冯跃洋(fyyvexoben@sjtu.edu.cn) 符号执行开发和维护
谢立汉(sheringham@sjtu.edu.cn) SMT solver和proof checker开发和维护
王治奕(ginwiahzy@gmail.com) strategy开发和维护，相关soundness proof证明
钟泓逸(zhonghongyi1204@sjtu.edu.cn) strategy parser开发和维护
吴姝姝(ciel77@sjtu.edu.cn) Relational HL部分证明维护

特别感谢董弈伯、周李韬、秦健行、唐亚周、陈彦宁和刘涵之等同学在项目前期探索方面做出的贡献。
