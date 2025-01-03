- AsrtDef: 定义了 Inner Assertion
  - 分为 Prop, Local, Sep, Exist 四个部分

- CDef: 定义了 Partial Statement

- CoqPrint: 将一些内容打印成 Coq 可以接收的对象
   - Statement，Annotated Statement，Partial Statement的输出
   - Witness 的输出

- Trans: 定义了一些转换函数：
   - AstModifier.c: 用于将 AST 中表示乘号的 `*` 和表示 sepcon 的 `*` 区分开来，将表示逻辑运算符的 `&&` 和 Assertion 中的 `&&` 区分开来
   - UserToInnerAsrtTrans.c: 将 AST 中的 User Assertion 转为符号执行用的 Inner Assertion
   - InnerToUserAsrtTrans.c: 将 Inner Assertion 转为可读性更好的 User Assertion（目前只实现很粗糙的版本）
   - StmtTrans.c: 将 AST 中的语句转为 Partial Statement

- SymExec: 做符号执行
   - CexprExec.c: 做 C 表达式的符号执行
   - StateMachine.c: 基于状态机在 Partial Statement 上做符号执行

- utility: 一些辅助函数

- test: 用于测试的代码
