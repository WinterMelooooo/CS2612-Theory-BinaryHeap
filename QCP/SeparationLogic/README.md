# QCP的soundness proof部分

本文件夹包括了QCP本身的soundness proof证明以及用户函数证明的相关依赖。

### 文件结构

compcert_lib、sets、auxlibs是整个项目的相关依赖

Asrtdef、AuxiFun、Cdef、StrategyLib是关于QCP本身soundness proof的相关文件

MonadLib、SeparationLogic、unifysl是关于用户函数证明的相关依赖。

### 如何编译

需要在当前文件夹和``unifsl``文件夹下分别添加配置文件CONFIGURE(大小写敏感、无后缀)，用于配置coq的路径. 下面是一个在cygwin中使用的配置例子：
```
COQBIN = /cygdrive/d/Coq-8.15/bin/
SUF=.exe
```

其中如果试图在wsl/powershell中使用windows下安装的Coq，请务必提供SUF，否则可能会出现类似``/bin/coqdep not found``的报错。

完成上面的配置之后，可以使用下面的指令进行编译，冒号前表示当前终端所在的文件夹，冒号后表示使用的指令：
```
. : cd unifysl
unifysl : make depend ; make
unifysl : cd ..
. : make depend ; make
```

编译完成之后就可以按照正常Coq方式进行使用。

### 用户在证明中可以使用的相关tactic介绍

注意，我们把证明结论``P |-- Q``中$P$称为前条件，$Q$成为后条件，前提指的是Coq中的Hypothesis。

``Intros``: 将前条件中的纯命题引入到前提中

``Intros_any`` : 将前条件中的存在变量实例化引入到前提中,名字由coq自动生成

``Intros x`` : 将前条件中的存在变量实例化记作$x$引入到前提中

``Intros_r_any`` : 将后条件中的forall变量实例化引入到前提中,名字由coq自动生成

``Intros_r x`` : 将后条件中的forall变量实例化记作$x$引入到前提中

``Exists x`` : 将后条件中的存在变量填为$x$

``Exists_l x`` : 将前条件中的forall变量填为$x$

``entailer!`` : 自动尝试进行分离逻辑的消去

``sep_apply H`` : 尝试使用H对结论进行变化， 往往H具有``P * Q |-- R``的形式，它会将前条件中的``P * Q``替换成``R``

``prop_apply H`` : 尝试使用H对结论进行变化, 往往H具有``P * Q |-- [| R |]``的形式，它会给前条件中增加``[| R |]``这个纯命题

``Left``: 把``P |-- Q || R``变成 ``P |-- Q``

``Right`` : 把``P |-- Q || R`` 变成 ``P |-- R``

``Split`` : 把``P || Q |-- R``变成``P |-- R``和``Q |-- R``两个分支

``csimpl`` : 对notation进行化简

