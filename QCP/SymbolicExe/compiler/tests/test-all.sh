#!/bin/bash

tests=(test0.c
       test1.c
       test2.c
       test3.c
       test4.c
       test5.c
       test6.c
       test7.c
       test8.c
       test9.c
       test10.c
       test11.c
       test12.c
       test13.c
       test14.c
       test15.c
       test16.c
       test17.c)

for test in ${tests[*]}; do
    ./test-one.sh $test
done
