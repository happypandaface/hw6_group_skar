#!/usr/bin/env python2


import difflib
import glob
import subprocess as subproc
import sys
from sys import stdout, stderr


TEMP = "./temp"


def main(pyname):
    fail = []

    for testname in sorted(glob.glob("test-translate/*.py")):
        stdout.write(testname + "\n")
        with open(testname) as src:
            translator = subproc.Popen(
                ('python2', pyname, '-q'), stdin=src, stdout=subproc.PIPE)
            compiler = subproc.Popen(
                ('./build.sh', '-', TEMP), stdin=translator.stdout)
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
                ('python2', pyname, '-q'), stdin=src, stdout=subproc.devnull,
                stderr=subproc.devnull)

            if translator.wait() == 0:
                stderr.write("TEST FAILED: Translation should fail\n")
                fail.append(testname)

    if fail:
        stdout.write("FAILED: " + ", ".join(fail) + "\n")
    else:
        stdout.write("PASSED\n")


if __name__ == '__main__':
    if len(sys.argv)<2:
      print "what script do you want me to test?"
    else:
      main(sys.argv[1])
