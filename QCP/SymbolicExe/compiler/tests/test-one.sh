#!/bin/bash

../build/test <$1 1>$1.s
# clang -target bpf -c $1.s
