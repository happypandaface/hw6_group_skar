#!/usr/bin/env python2


import difflib
import glob
import subprocess as subproc
import sys
from sys import stdout, stderr


TEMP = "/tmp/skar-test-cvjw8ef9823ua0d89vxhcvx71"

devnull = open("/dev/null", "w")


def fancy_format(x):
    for lt, rt in ("()", "[]"):
        f = []
        for g in x.split(lt):
            if g and g[0] == rt:
                f.append(g)
            else:
                f.append("\n" + g)
        x = lt.join(f)[1:]
        f = []
        for g in x.split(rt):
            if f:
                if not (f[-1] and f[-1][-1] == lt):
                    f[-1] += "\n"
            f.append(g)
        x = rt.join(f)
    return x + "\n"


def main(pyname):
    fail = []

    for testname in sorted(glob.glob("test-translate/*.py")):
        stdout.write(testname + "\n")
        with open(testname) as src:
            translator = subproc.Popen(
                ('python2', pyname, '-q'), stdin=src, stdout=subproc.PIPE)
            compiler = subproc.Popen(
                (
                    'gcc',
                    '-std=gnu99', '-Wall', '-Wextra', '-Wno-unused-parameter',
                    '-Wno-unused-variable', '-Wno-unused-function',
                    '-Wno-unused-but-set-variable',
                    '-Werror=implicit-function-declaration',
                    '-x', 'c', '-o', TEMP, '-'
                ),
                stdin=translator.stdout)
            if translator.wait() != 0:
                compiler.terminate()
                stderr.write("TEST FAILED: Can't translate\n")
                fail.append(testname)
                continue
            if compiler.wait() != 0:
                stderr.write("TEST FAILED: Can't compile\n")
                fail.append(testname)
                continue

            refprog = subproc.Popen(("python2", testname), stdout=subproc.PIPE)
            testprog = subproc.Popen((TEMP,), stdout=subproc.PIPE)
            refout, _ = refprog.communicate()
            testout, _ = testprog.communicate()

            if refprog.returncode != 0:
                testprog.terminate()
                stderr.write("TEST FAILED: Reference program failed\n")
            if testprog.returncode != 0:
                stderr.write("TEST FAILED: Test program failed\n")
            diff = "".join(difflib.unified_diff(
                refout.splitlines(True),
                testout.splitlines(True)))[len("--- \n+++ \n"):]
            stdout.write(diff)
            if diff:
                stderr.write("TEST FAILED: Test and reference output differ\n")
                fail.append(testname)

    for testname in sorted(glob.glob("test-no-translate/*.py")):
        stdout.write(testname + "\n")
        with open(testname) as src:
            translator = subproc.Popen(
                ('python2', pyname, '-q'), stdin=src, stdout=devnull,
                stderr=devnull)

            if translator.wait() == 0:
                stderr.write("TEST FAILED: Translation should fail\n")
                fail.append(testname)


    if fail:
        stdout.write("FAILED: " + ", ".join(fail) + "\n")
    else:
        stdout.write("PASSED\n")


if __name__ == '__main__':
    main("hw6_compiler.py")
