#!/usr/bin/env python3
import sys
import pathlib
import argparse
import subprocess

HERE = pathlib.Path(__file__).parent
CM_ROOT = HERE.parent

def discover_make():
    if sys.platform.startswith("freebsd"):
        return "gmake"
    else:
        return "make"

def main(argv):
    args = parser.parse_args(argv)
    make_cmd = discover_make()
    cp = subprocess.run(
        [make_cmd, "-C", str(CM_ROOT), "lint"]
    )
    return cp.returncode


parser = argparse.ArgumentParser()
parser.add_argument("file", nargs="*")

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
