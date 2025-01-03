## transformation:

定义了命题的结构，对命题做curryfy和constant replace，并转为cnf，并且通过转化后的cnf初始化sat solver中的数据结构。
theroy_deduction实现了theory部分的求解，具体函数功能描述参见头文件。

## congruence：

实现了uf theory求解的关键步骤：计算congruence closure
merge函数读入一系列等式，构建congruence closure
areCongruent判断两个元素是否在同一个等价类中
explain有三个版本，读入参数a，b
explain会打印a=b是由哪些等式推导而来
re_explain会返回这些等式
explain_p 会返回a=b的证明，证明的结构参见proof.h

## CDCL:

实现了SAT solver，串联上面两个部分实现了smt solver
sat solver可以通过函数Test_Sat_Solver进行测试，输入格式为DIMACS格式，可参加cnf文件夹中的测试用例
smt solver封装在函数smt_solver中，读入一个命题，返回其是否satisfible

## proof：

尚未完成的证明模块。

## hashtable：

程序实现中使用的简单哈希表

## others：

transformation.c中注释的main函数给出了读入一系列字符串构建congruence closure的方法，以及输出相关的解释。

congruence.c中注释的main函数给出一个简单的样例，输出了带证明的结果。
