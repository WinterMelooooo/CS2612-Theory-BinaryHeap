#!/bin/bash

for dir in ../../examples/*; do
    rm -rf $(basename $dir)
    mkdir $(basename $dir)
    for file in $dir/*; do
        ../build/test < $file 1> ./$(basename $dir)/$(basename $file).s 2> ./$(basename $dir)/$(basename $file).msg
    done
done
