#!/usr/bin/env bash

set -o errexit

if [[ $# != 2 ]]; then
    echo "Usage:  build.sh IN OUT" >&2
    exit 1
fi


CFLAGS=\
'-std=gnu99 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable '\
'-Wno-unused-function -Wno-unused-but-set-variable '\
'-Werror=implicit-function-declaration '

gcc $CFLAGS -c -o hashtable.o hashtable.c
gcc $CFLAGS -c -o hashtable_itr.o hashtable_itr.c
gcc $CFLAGS -o $2 hashtable.o hashtable_itr.o -x c $1 -lm
