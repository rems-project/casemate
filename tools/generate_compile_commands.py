#!/usr/bin/env python3
# Generates a clangd suitable compile_commands.json file
# Usage: ./generate_compile_commands.py PATH_TO_SRCROOT_DIR

import json
import pathlib

import argparse

parser = argparse.ArgumentParser()
parser.add_argument("srcdir", type=pathlib.Path)
parser.add_argument("workdir", type=pathlib.Path)
args = parser.parse_args()

compile_commands = []

for f in args.srcdir.rglob("*.c"):
    cmd_path = f.with_suffix(".o.cmd")
    if cmd_path.exists():
        compile_commands.append(
            {
                "command": cmd_path.read_text(),
                "directory": str(args.workdir.absolute()),
                "file": str(f.absolute()),
            }
        )

with open(args.srcdir / "compile_commands.json", "w") as f:
    json.dump(compile_commands, f, indent=4)
