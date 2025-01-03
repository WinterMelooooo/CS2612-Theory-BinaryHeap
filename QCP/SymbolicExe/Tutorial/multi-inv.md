# loop & multicase-inv

## 关于 loop frame 中的存在变量与 prop
- 记录存在变量和prop的 def (首次引入) 在 CFG 中的位置。
- 在 CoqPrint 生成 loop 中的 proof goal 时，将在 loop 之前 def 的存在变量视作 With 变量（在左端由全称量词bound，在右端不出现）。
- 存在变量的回收机制：当存在变量 x 无法与 sep 中的变量产生关联（图上不可达）时，从exist_list中删去 x 并删去其所有 prop。
- **def在loop前且不在loop inv中的** prop 不出现在生成的 goal 的右端，以使 goal 更为简洁。

## multicase-inv  
### 机制
考虑到由于循环/数据结构比较复杂，有时循环不变量有多个分支，并且这多个分支是不同阶段的而非并行的，我们普通的partial inv solve无法处理这种循环不变量的符号执行，因此我们需要使用multicase-inv机制来解决。
- 对于一个inv的多个case, 用户可以对这些 case 给出多个不同的case_name，以便之后使用。
- 在进入时，用户需要为每个 branch 指定**唯一的** case，用于确定进入循环时该 branch 会进入哪个 inv 的 哪一 case，且对应 case 在循环中的 branch 的名字即为指定的 case_name。
- 用户需要在 loop body 的每一个出口(包括continue和正常结束循环体执行)为每一个 branch 指定**唯一**对应的 case，用于确定这一 branch 在这一出口执行下次循环时适用哪个 case。

一些需要注意的点：
- **case 与 frame 一一对应** (参考符号执行行为)。
- 当某一 branch 未在入口或出  口处显式指定对应 case，**默认进入与该 branch 有相同名字的 case**。若 branch 未取名或没有相同名字的 case 则报错。
-  当使用普通 Inv 时（没有 case_name 的单个 partial inv），进入循环前的每一个 branch 分别对应一个 case (使用的自然是同一个 inv)，且 case_name 继承之前的 branch_name。 
- 循环前多个 branch 进入同一个 case 时，相当于对这些 branch 做 partial assert join。
- 循环中进行 branch join 时必须要求在**第一次执行到此处时，所有被 join 的 branch 必须是 concrete branch (已求出 frame 的 case 产生的 branch)**，否则报错。


符号执行的行为：
- 对于进入 loop 的每个 branch，对为其指定的 inv case 分别 partial solve 得到 frame，产生对应 case_name 的新的 branch。
- 若指定多个 branch 进入同一case，则等价于执行 ``Branch join ... into case_name with inv``。
- 对这些新 branch 进行符号执行。在遇到出口时，
  - 若目标 inv case 已经解出过 frame，则要求当前的assertion能推出已经求好frame的inv（相当于 full assertion）；
  - 否则 partial solve 得到新的 frame 和新 branch，将新 branch 加入待执行队列。 
- 当该 branch 在循环中的所有的 inv case 的符号执行完毕时，该 branch 在该循环的符号执行结束。跳出循环时 branch name 与跳出时的 name 一致。

### 语法
下面的例子简洁地展示了 multicase-inv 的语法。 
```c
/*@ Inv  
    invA_1 invA_2: invA
    invB_1: invB
    with
    pre_1 => invA_1
    pre_2 => invA_2
*/
while (...) {
  ...
  if (...) {
    continue /*@ invA_1 => invB_1 */ ;
  }
  ...
  /*@ invB_1 => invA_2 */
}
```

在这个例子中，我们假设进入循环前有两个branch``pre_1``和``pre_2``。
我们通过 ``/*@ Inv ... */`` 语句指定了两个循环不变量 ``invA`` 和 ``invB``，前者有两个 case ``invA_1``和``invA_2``，后者有一个 case ``invB_1``。
我们通过 ``pre_1 => invA_1`` 指定 ``pre_1`` 进入 ``invA_1`` 分支，此时会根据 ``pre_1`` 对 ``invA_1`` 进行 partial inv solve 求出 frame，然后使用``invA_1``进行后面的符号执行。对 ``pre_2`` 的处理也是类似的。

对于 ``invA_1`` 分支，如果它进入if的then分支，然后通过continue进入下次循环，这时会进入``invB_1``, 如果进入else分支那么会直接进入下次循环，此时仍然落入``invA_1``的分支，此时由于``invA_1``的frame已经求出，我们会得到对应的goal然后结束该分支的符号执行。

如果进入``invB_1``, 我们会根据``invA_1``对``invB_1``进行partial inv solve求出frame. 根据代码的假设，如果这里``invB_1``进入了if的then分支遇到了continue，由于这里没有提供关于``invB_1``的出口，相当于省略了 `/*@ invB_1 => invB_1*/`，得到对应 goal 即可结束符号执行。

另外，如果用户可以确定 `invB_1` 不会进入 then 分支，则可以在 then 分支使用 `/*@ Branch clear invB_1 */` 来清除分支。如果不进入if的then分支，那么根据出口标注，它会进入``invA_2``。由于``invA_2``的frame已经求出，我们会得到对应的goal然后结束该分支的符号执行。
剩余的``invA_2``符号执行是类似的，在此不多赘述。

### 例子
- 红黑树中 delete_balance 的例子
- 红黑树 insert_balance (或 delete_balance) 的 refinement proof 的例子
- 一个naive的例子 (multiinv_example.c)
