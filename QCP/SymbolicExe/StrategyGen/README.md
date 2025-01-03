# StrategyGen

`PredicateInput` 文件夹中包含了对于每一份代码，需要读入的谓词定义。

`GeneratedStrategy` 文件夹中包含测试代码、头文件、strategies 文件。

自动生成 strategies 的方法如下：
```
cd sac_c_parser/StrategyGen
python strategy_generation.py --name list_app --check True
``` 

其中 `name` 表示代码的文件名， `check` 表示是否检测该 strategies 的正确性。

目前测试代码包含了 `list_app.c` (data0,nest0)，`list_app_data2.c`(data2,nest0) 以及 `listlist_app.c`(data1,nest1)