#!/usr/bin/env python
import sys
import pathlib
import subprocess

HERE = pathlib.Path(__file__).parent
SRC = HERE.parent

EXPECTED = SRC / "expected"

overwritten_expected_logs = len([
    f
    for f in EXPECTED.iterdir()
    if f.suffix == ".log"
])

if overwritten_expected_logs:
    yn = input(
        f"This overwrites {overwritten_expected_logs} logs. Continue anyway? [Y/n]: "
    ).lower().strip()

    if yn and yn != "y":
        sys.exit(0)

# ask for the list of targets
build_objs = subprocess.run(
    ["make", "list-build-objs"],
    cwd=SRC,
    check=True,
    capture_output=True,
    text=True,
).stdout.split()

# run each, and collect output into a log file
for obj in build_objs:
    with open((EXPECTED / obj).with_suffix(".log"), "w") as f:
        subprocess.run(
            [str((SRC / obj).absolute()), "-a"],
            stdout=f,
        )

print("Done")