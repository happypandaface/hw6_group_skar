#!/usr/bin/env python2


import ast
import compiler
import sys
from sys import stdin, stdout


if __name__ == '__main__':
    prog = stdin.read()
    stdout.write(str(compiler.parse(prog)) + "\n")
    stdout.write("\n")
    stdout.write(ast.dump(ast.parse(prog)) + "\n")
