# Multi-Branch

## 使用场景
符号执行过程中，控制流常会产生分支。而在不同控制流合并时，由于经过的程序路径不同，它们的断言也不同，因而符号执行分支仍需保留。而下一次控制流产生分支再合并时，每一执行分支又会各自产生新的分支，导致 path explosion 等问题。为了解决相关问题，我们提供了 Multi-Branch 系列语句，来对执行分支进行命名、删除、合并等操作。

## 用 Branch name 语句为分支命名
### 语法
直观上类似：
```c
/*@ Branch name
    name0 prop0;
    name1 prop1
*/
```
形式化地：
```
 'Branch' 'name' 
  branch_name branch_prop (';' branch_name branch_prop)* ';'?
```
其中 `branch_prop` 为一个断言语句。

### 语义
按照顺序，依次将当前所有满足 `branch_prop` 的分支命名为 `branch_name`。

- `branch_name` 不能为 `all`, `unnamed`。
- 一个名字可以对应多个分支，但一个分支最多有一个名字。
- 可以为已有名字的分支指定新的名字，新名字将覆盖旧名字。
- `branch_name` 可以使用已经使用过的名字，相当于为该名字添加分支。
- `branch_prop` 可以为空，此时会为当前所有分支命名 `prop_name`，这在只有一个分支的情况下比较有用。如 `/*@ Branch name x */`。
- 已有名字的分支在符号执行时产生了多个分支时，这些分支继承原有的名字。
- 为了方便排查错误，下列情况报错：
  - 没有分支满足 `branch_prop`
  - 在同一 `Branch name` 语句块内第二次为某一分支命名



## 用 Branch clear 语句删除分支
### 语法
直观上类似：
```c
/*@ Branch clear branch0 branch1 */
/*@ Branch clear unnamed */
```
形式化地：
```
 'Branch' 'clear' branch_list
```
其中，
```
branch_list := branch_name+ | 'unnamed' | 'all'
```

### 语义
声明 `branch_list` 指定的分支由于蕴含矛盾在程序中不可能执行，并清除这些分支。

- 工具会用 SMT 自动推理这些分支的断言蕴含矛盾，未彻底求解会生成 manual proof。
- 可以用 `unnamed` 指定所有未命名分支。

## 用 Branch join 语句合并分支
### 语法
直观上类似：
```c
/*@ Branch join branch0 branch1
    into new_branch
    with partial_assertion
*/

/*@ Branch join all
    with Assert full_assertion
*/
```
形式化地：
```
 'Branch' 'join' branch_list
 ('into' new_name )?
  'with' partial_assertion | ('Assert' full_assertion) 
```
其中，

### 语义
将 `branch_list` 指定的分支合并为一个新的分支。如果有 `into` 语句，就将新分支命名为 `new_name`。然后根据 `with` 语句中的 assertion 得到新分支的断言。 
- 若 `with` 后是 `partial_assertion`，则工具在每一个待合并分支上用 SMT 做 partial solve，确认每个分支的 frame `F` 是相同的，并找出各个分支的公共纯逻辑断言 `P`，最后新分支的 assertion 为 `P * F` 和 `partial_assertion` 的合取。

- 若 `with` 后是 `full_assertion`，则每个分支用 SMT 求解，新分支断言即 `full_assertion`。
- 与 `Branch clear` 一样，可用 `all` 和 `unnamed` 分别代指所有分支和所有未命名分支。

- join 到 partial assertion 时，相同 frame 和公共断言的标准为 **α-equivalence**。
