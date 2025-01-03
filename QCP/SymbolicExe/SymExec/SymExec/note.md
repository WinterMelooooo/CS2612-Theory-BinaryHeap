## 表达式求值

### 左右值

对于一个程序变量，存一个地址 $v_1$，地址中存一个值 $v_2$

符号执行求 `x`,右值：返回地址中的值 $v_2$

符号执行求 `x`, 左值：返回变量的地址 $v_1$

符号执行求 `&x`，右值：返回变量的地址 $v_1$

符号执行求 `&x`，左值：不应该出现 

符号执行求 `*x`，右值：先找到 $v_2$，再找 `data_at(..., v2)`

符号执行求 `*x`，左值：返回 $v_2$

### 求值顺序

- `a = b`. right first

- `a + b`. left first

### 内存问题

求值 `1`，新建一个 ExprVal，存放 `const 1`

求右值 `a`，找到 pa, data_at(pa, va), 返回 `va` 的深拷贝

求左值 `a`，深拷贝

求左值 `a->b`, 求 `a` 的右值va（深拷贝），新建 ExprVal, 存放 Field_Address(va, b)

## Partial-Statement 符号执行

### 循环不变量放在中间

- While
  - 前条件进来，做一次符号执行，符号执行到结束的结果再做一次符号执行。第二次做符号执行时，遇到断言尝试推导；如果推导成功，这条path结束。执行到结束时，如果还有剩余断言，说明有些path没有被assertion完整覆盖
  - 循环不变量取为：precondition || 第一次符号执行完的结果(nrm || cnt)
  - 最终的后条件：(inv && !condition) || (两次符号执行的 brk)

### 目前实现的功能

- [ ] 表达式求值
  - [x] 简单的运算（+ - * / % & ^ | << >> !）
  - [x] 比较运算符（在计算时会枚举取值的结果，例如 `a<b ` 会产生两种 assertion，其中一个在 prop 中会多一条 `a<b`，返回值为 `EZ_VAL 1`；另一个在 prop 中会多一条 `a >= b`，返回值为 `EZ_VAL 0`）
  - [x] 逻辑运算符（|| && 支持短路求值）
  - [ ] 函数
- [x] 简单语句符号执行
  - [x] 赋值（包括 += -= %=, etc.）
  - [x] 自增自减（处理成 `+=1`, `-=1` ）
  - [x] 单纯的计算（实现为直接调用表达式求值；会导致Assertion拆分为多个分支）
- [x] If 语句符号执行
- [x] While 语句
  - [x] break
  - [x] continue
- [x] switch
  - [x] break
  - [x] default
  - [x] fall-through
- [ ] do-while
- [ ] for
- [x] return
- [x] 变量定义
- [ ] function call

### 可能需要添加的模块

- [ ] entailment 
   - [ ] comment 语句能否推出
   - [ ] 循环不变量判断能否推出
   - [ ] 函数后条件判断能否推出
   - [ ] 函数调用
- [ ] Inner Assertion 转 User Assertion（部分完成）
- [ ] 重名变量处理
- [x] 变量作用域