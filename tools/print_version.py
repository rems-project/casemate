#!/usr/bin/env python3
import argparse
import pathlib
import subprocess

HERE = pathlib.Path(__file__).parent
CM_ROOT = HERE.parent

CM_VERSION_PATH = CM_ROOT / "VERSION"

cm_version = CM_VERSION_PATH.read_text().strip()
cm_date = subprocess.run(
    ["git", "log", "-n1", "--pretty=tformat:%as", str(CM_VERSION_PATH)],
    check=True,
    capture_output=True,
    text=True,
).stdout.strip()

def main(args):
    if args.long:
        print(f"{cm_version}, {cm_date}")
    elif args.release_date:
        print(f"{cm_date}")
    else:
        print(cm_version)

parser = argparse.ArgumentParser()
g = parser.add_mutually_exclusive_group()
g.add_argument("--long", action="store_true")
g.add_argument("--release-date", action="store_true")

if __name__ == "__main__":
    args = parser.parse_args()
    main(args)
