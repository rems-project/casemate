#!/usr/bin/env python
# Generates a clangd suitable compile_commands.json file
# Usage: ./generate_compile_commands.py PATH_TO_SRCROOT_DIR

import json
import pathlib

import argparse

parser = argparse.ArgumentParser()
parser.add_argument("dir", type=pathlib.Path)
args = parser.parse_args()

compile_commands = []

for f in args.dir.rglob("*.c"):
    cmd_path = f.relative_to(args.dir).with_suffix(".o.cmd")
    if cmd_path.exists():
        compile_commands.append(
            {
                "command": cmd_path.read_text(),
                "directory": str(args.dir),
                "file": str(f),
            }
        )

with open(args.dir / "compile_commands.json", "w") as f:
    json.dump(compile_commands, f, indent=4)