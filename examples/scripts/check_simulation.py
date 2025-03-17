#!/usr/bin/env python3
# Guesses and checks a simulation between two log files, and checks the final condition.
#
# Usage:
# ./check_simulation.py generated_log_file.log expected/expected_log_file.log

import re
import sys
import string
import pathlib
import argparse
import itertools

PAGE_SHIFT = 12
PAGE_MASK = (1 << 12) - 1

# Really dumb 'simulation' check:
# give each new page a sequentially named identifier,
# then check that the two traces when re-labelled are the same
# which checks the traces are the same shape (but not necessarily that they properly refine)
class Sim:
    def __init__(self):
        self.var_names = iter(string.ascii_lowercase)
        self.relation = {}

def simulate(simulation, n, s):
    n_page = n & ~PAGE_MASK

    if n_page not in simulation.relation:
        var = next(simulation.var_names)
        simulation.relation[n_page] = var
    else:
        var = simulation.relation[n_page]

    distance = n - n_page

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

    return re.sub(r"(?:0x[0-9a-fA-F]+)", repl, line)


def rewrite_trace(f):
    simulation = Sim()
    for line in f:
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
