# Tactic Readme

### abs_choice_left

对于形如 ``P -@ (choice c1 c2) -⥅ Q ♯ a``的结论，我们可以用这个指令把它变成``P -@ c1 -⥅ Q ♯ a ``


### abs_choice_right

对于形如 ``P -@ (choice c1 c2) -⥅ Q ♯ a``的结论，我们可以用这个指令把它变成``P -@ c2 -⥅ Q ♯ a ``

### abs_test_step

对于形如``P -@ (test Q) -⥅ P ♯ a``的结论，我们可以用这个指令把它解决并且产生一个``Q``的待证明结论

对于形如``P -@ (test Q ;; c1) -⥅ P ♯ a``的结论，我们可以用这个指令把它变成``P -@ c1 -⥅ P ♯ a``并且产生一个``Q``的待证明结论

### abs_assert_step

对于形如``P -@ (assert Q) -⥅ P ♯ a``的结论，我们可以用这个指令把它解决并且产生一个``Q``的前提

对于形如``P -@ (assert Q ;; c1) -⥅ P ♯ a``的结论，我们可以用这个指令把它变成``P -@ c1 -⥅ P ♯ a``并且产生一个``Q``的前提

### abs_return_step

对于形如``P -@ (return a) -⥅ P ♯ a``的结论，我们可以用这个指令把它解决


### safe_step H

如果H形如`` safeExec s (test Q ;; c1) `` 那么可以使用``safe_step H``把它变成``safeExec s c1``
并且产生一个Q的待证明结论

如果H形如`` safeExec s (assert Q ;; c1) `` 那么可以使用``safe_step H``把它变成``safeExec s c1``
并且产生一个Q的前提



### safe_choice_l H

如果H形如`` safeExec s (choice c1 c2) `` 那么可以使用``safe_choice_l H``把它变成``safeExec s c1``

### safe_choice_r H

如果H形如`` safeExec s (choice c1 c2) `` 那么可以使用``safe_choice_r H``把它变成``safeExec s c2``
