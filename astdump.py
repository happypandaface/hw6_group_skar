#!/usr/bin/env python2


import ast
import sys


if __name__ == '__main__':
    print ast.dump(ast.parse(sys.stdin.read()))
