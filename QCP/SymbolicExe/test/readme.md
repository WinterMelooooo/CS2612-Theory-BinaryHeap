## VST-IDE测试代码

### 测试内容

测试分为五个部分：

- Full user annotated program：测试 lexer, parser 的正确性
- Full inner annotated program：测试转化为 AST 的正确性（这一步包括 UserAssertion 到 InnerAssertion 的转化）
- Partial inner annotated program：测试 full program 转为 partial program 的正确性
- Symbolic Execution：测试符号执行和生成的 Witness 的正确性
- Coq Print：测试输出到 Coq 的正确性

### 编译与运行

#### 编译

已经从原来的 Makefile 改为了 Cmake

在编译之前需要新建CONFIGURE（全大写，文件最后一行需要以换行符结束）来写入一些配置

如果是cygwin的话，你可能需要在CONFIGURE中提供gcc所在路径，eg: `C_PATH=/usr/bin/gcc`，推荐使用绝对路径。

编译代码之前，你首先需要配置 CONFIGURE

你需要写的配置：

- `GOAL_FILE`: proof goal 文件的路径

- `PROOF_AUTO_FILE`: 可以被 solver 自动解决的目标的路径

- `PROOF_MANUAL_FILE`: 需要手动解决的目标的路径

- `COQ_LOGIC_PATH`: proof goal 文件的 Coq 逻辑路径

- `STRATEGY_FILE`: strategy 文件的路径。具体使用见下文“使用DSL自定义Strategy”

如果你想要使用相对路径，可以使用 `${PROJECT_ROOT_DIR}` 来表示项目根目录

以下是一个例子：

```
GOAL_FILE = ${PROJECT_ROOT_DIR}/../annotated_simplec/test/test_goal.v
PROOF_AUTO_FILE = ${PROJECT_ROOT_DIR}/../annotated_simplec/test/test_proof_auto.v
PROOF_MANUAL_FILE= ${PROJECT_ROOT_DIR}/../annotated_simplec/test/test_proof_manual.v
COQ_LOGIC_PATH = SimpleC.EE
STRATEGY_FILE = ${PROJECT_ROOT_DIR}/examples/common_DSLFileLists
```

要编译代码，请在本目录下执行 `sh ./gen.sh`   （如果你使用的是 cygwin，请执行 `sh ./gen.sh cygwin`）

#### 符号执行的运行

如果你使用的是 wsl，在`test`目录下执行以下命令运行代码：

`ASAN_OPTIONS=detect_leaks=0 build/symexec --no-logic-path --no-strategy-gen --strategy-file=../examples/sll_DSLFileLists --input-file=../examples/sll.c`

如果你使用的是 cygwin，用以下命令：

`build/symexec --no-logic-path --no-strategy-gen --strategy-file=../examples/sll_DSLFileLists --input-file=../examples/sll.c`

这个命令表示，将`examples/sll.c`作为输入，使用`examples/sll_DSLFileLists`作为 strategy 文件，进行符号执行并将 Proof Goal 输出到coq

`ASAN_OPTIONS=detect_leaks=0` 是取消内存泄漏检查。如果不加这个会额外输出很多内存泄漏信息。cygwin 下不支持 sanitize，所以不需要这个参数。

`--no-strategy-gen` 的意思是不考虑 strategy 的 soundness 证明。如果去掉这个选项，在生成的 Proof Goal 中会要求证明使用到的 strategy 的正确性。关于 strategy soundness 证明目标生成，见  [T3_strategies.md](../examples/Tutorial/T3_strategies.md)

**注意：请不要使用输入流重定向代替`--input-file=<path>`**

你可以添加一些运行选项,其中带有 \* 的运行选项是我们推荐指定的

- --gen-and-backup，表示如果输出的 coq 文件已经存在，就先将其转存为一个 backup 文件，再修改文件内容；如果不包含这个选项，将会默认覆盖goal文件和proof-auto文件，不修改proof-manual文件

- (\*) --goal-file=\<file\> 表示输出的 proof goal 的路径；如果不包含这个选项则输出到 CONFIGURE 中指定的路径

- (\*) --proof-auto-file=\<file\> 表示输出的 proof auto 的路径；如果不包含这个选项则输出到 CONFIGURE 中指定的路径

- (\*) --proof-manual-file=\<file\> 表示输出的 proof manual 的路径；如果不包含这个选项则输出到 CONFIGURE 中指定的路径

- --coq-logic-path=<path> goal-file 所在的 coq 逻辑路径；如果不包含这个选项则设置为 CONFIGURE 中指定的路径

- (\*) --no-logic-path 不设置 goal-file 的 coq 逻辑路径。不能和 --coq-logic-path=<path> 同时使用

- --no-strategy-gen 不生成 strategy 的 soundness 证明目标。

- (\*) -slp <folder_path> <logic_path> 表示添加 <folder_path> 为用于寻找 .strategies 文件的文件夹，并将该文件夹中的 strategy 的逻辑路径设置为 <logic_path>；未指定的 strategy 则默认不使用逻辑路径

- (\*) --strategy-file=\<file\> 表示使用的 strategy 的配置路径；如果不包含这个选项使用 CONFIGURE 中指定的路径

- --program-path=<path> 表示将要证明代码的 Coq 表示输出到哪个路径；如果不包含这个选项则不输出

- (\*) --input-file=\<file\> 表示输入的文件路径；如果不包含这个选项则从 stdin 输入

- --no-exec-info 表示不展示符号执行过程中产生的运行信息

- -s \<number\> 表示运行测试的第几阶段。 $1 \le number \le 5$。如果不包含这个选项则测试所有阶段。除了工具的开发者之外，一般不使用该选项。

如果代码中含有 `#define`、 `#include` 等预处理指令，请使用 `cpp -P -C <input file> <output file>` 来得到预处理后的C源文件。目前的解析器只原生支持了 `#include`。

### 使用DSL自定义Strategy

#### DSL文件选择

若需要自定义DSL，请新建一个DSL文件，按格式`"add:"+[Path]`增加所有 strategy 路径，然后在 CONFIGURE 中写： `STRATEGY_FILE=[DSL文件路径]`

**注意：strategy 文件路径应当填写相对于项目根目录的路径**

#### 预处理Strategies文件

可以通过如下脚本预处理 Strategies 文件中引用的头文件。例如，
```
./spp.perl ../examples/sll.strategies sll.strategies.h sll.pp.strategies
```
的效果是在 `../examples` 目录下生成 `sll.strategies.h` 和 `sll.pp.strategies`。前者是所有引用头文件合在一起预处理后的结果，后者是将 `sll.strategies` 中的引用替换为引用前者的结果。

如果你的系统中C预处理器的路径比较特殊，请在这三个参数后附加之。

### 测试脚本

测试脚本暂时不可用

<!-- 运行 `python3 test.py` 会自动评测 `testcases` 目录下的所有测试点（不包括输出到coq） -->


