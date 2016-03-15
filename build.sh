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

gcc $CFLAGS -x c -o $2 $1
