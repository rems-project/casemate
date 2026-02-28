#!/usr/bin/env python3
import sys
import pathlib
import argparse
import subprocess

HERE = pathlib.Path(__file__).parent
EXAMPLES_ROOT = HERE.parent
CASEMATE_ROOT = EXAMPLES_ROOT.parent
CASEMATE_CHECK_ROCQ_ROOT = CASEMATE_ROOT / "src" / "casemate-check-rocq"

EXAMPLES = (
    subprocess.run(
        ["make", "list-build-objs"],
        cwd=EXAMPLES_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip().split()
)


def runmsg(prefix, s):
    print(f'  {prefix:<8}\t\t\t{s}', file=sys.stderr)

def check_expected(test_name):
    example_exe = EXAMPLES_ROOT / test_name
    out_path = (EXAMPLES_ROOT / "tests" / test_name).with_suffix(".log")

    runmsg("RUN", test_name)
    with open(out_path, "wb") as logf:
        subprocess.run(
            [str(example_exe)],
            cwd=EXAMPLES_ROOT,
            stdout=logf,
            check=False,
        )

    expected = (EXAMPLES_ROOT / "expected" / test_name).with_suffix(".log")
    runmsg("CHECK", test_name)
    subprocess.run(
        ["python3", "./scripts/check_simulation.py", str(out_path), str(expected)],
        cwd=EXAMPLES_ROOT,
        check=True,
    )

def check_rocq_trace(test_name):
    expected_log = (EXAMPLES_ROOT / "expected" / test_name).with_suffix(".log")

    runmsg("CHECK", test_name)

    expected_status = expected_log.read_text().strip().splitlines()[-1]
    expected_status = 121 if expected_status.startswith("!") else 0

    cp = (
        subprocess.run(
            ["dune", "exec", "casemate", "--", str(expected_log)],
            cwd=CASEMATE_CHECK_ROCQ_ROOT,
            check=False,
        )
    )

    if cp.returncode != expected_status:
        raise ValueError(f"Fail check on {test_name}")


def main(argv):
    args = parser.parse_args(argv)

    for example in EXAMPLES:
        expected_log = (EXAMPLES_ROOT / "expected" / example).with_suffix(".log")

        if expected_log.exists():
            if args.rocq:
                check_rocq_trace(example)
            else:
                check_expected(example)


parser = argparse.ArgumentParser()
grp = parser.add_mutually_exclusive_group(required=True)
grp.add_argument("--rocq", action="store_true", default=False)
grp.add_argument("--examples", action="store_true", default=False)

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
