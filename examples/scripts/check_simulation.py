#!/usr/bin/env python
# Guesses and checks a simulation between two log files, and checks the final condition.
#
# Usage:
# ./check_simulation.py generated_log_file.log expected/expected_log_file.log

import re
import sys
import pathlib
import argparse
import itertools


def simulate(simulation, n, s):
    pairs = [(n - i, var) for (i, var) in simulation.items()]
    pairs = [(distance, var) for (distance, var) in pairs if distance >= 0]
    pairs = sorted(pairs)

    if not pairs:
        return s

    closest = pairs[0]
    distance, var = closest

    if distance == 0:
        return var
    elif distance <= 4096:
        return "{}+{}".format(var, distance)
    else:
        return s


def rewrite_record(simulation, line):
    def repl(m):
        try:
            k = int(m.group(0), 0)
        except ValueError:
            return m.group(0)
        return simulate(simulation, k, m.group(0))

    return re.sub(r"(?:0x[0-9a-fA-F]+)|\d+", repl, line)


def rewrite_trace(f):
    simulation = {}

    for line in f:
        if line.startswith("#define"):
            parts = line.split()
            assert len(parts) == 3
            simulation[int(parts[2], 0)] = parts[1]

        new_line = rewrite_record(simulation, line)
        yield new_line


def compare_traces(f1, f2, debug=False):
    for i, (r1, r2) in enumerate(
        itertools.zip_longest(rewrite_trace(f1), rewrite_trace(f2))
    ):
        if debug:
            print("XX '{}' ~> '{}' @ i".format(r1.strip(), r2.strip(), i))
        if r1 != r2:
            raise ValueError(
                "mismatched records at line #{}: got '{}', expected '{}'".format(
                    i, r1, r2
                )
            )


parser = argparse.ArgumentParser()
parser.add_argument("given", type=pathlib.Path)
parser.add_argument("expected", type=pathlib.Path)
parser.add_argument("--debug", action="store_true", default=False)


def main(args):
    with open(args.given) as f1, open(args.expected) as f2:
        compare_traces(f1, f2, debug=args.debug)
    return 0


if __name__ == "__main__":
    sys.exit(main(parser.parse_args()))
