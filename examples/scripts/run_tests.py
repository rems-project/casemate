#!/usr/bin/env python3
import sys
import pathlib
import argparse
import subprocess

HERE = pathlib.Path(__file__).parent
EXAMPLES_ROOT = HERE.parent
CASEMATE_ROOT = EXAMPLES_ROOT.parent
CASEMATE_CHECK_ROCQ_ROOT = CASEMATE_ROOT / "src" / "casemate-check-rocq"
ROCQ_CHECKER = CASEMATE_CHECK_ROCQ_ROOT / "_build" / "default" / "src" / "casemate.exe"

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
    print(f'  {prefix:<8}\t\t\t{s}', file=sys.stderr, flush=True)

def build_rocq_checker():
    runmsg("BUILD", "rocq checker")
    subprocess.run(
        ["dune", "build", "./src/casemate.exe"],
        cwd=CASEMATE_CHECK_ROCQ_ROOT,
        check=True,
    )

def expected_rocq_result(expected_log):
    final_line = expected_log.read_text().strip().splitlines()[-1]

    if final_line.startswith("!"):
        return 121, final_line[1:].strip()

    return 0, None

def print_completed_process(cp):
    if cp.stdout:
        print(cp.stdout, end="", flush=True)
    if cp.stderr:
        print(cp.stderr, end="", file=sys.stderr, flush=True)

def check_expected(test_name, fine_grained=False):
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
        ["python3", "./scripts/check_simulation.py", "-T" if not fine_grained else "", str(out_path), str(expected)],
        cwd=EXAMPLES_ROOT,
        check=True,
    )

def check_rocq_trace(test_name):
    expected_log = (EXAMPLES_ROOT / "expected" / test_name).with_suffix(".log")

    runmsg("CHECK", test_name)

    expected_status, expected_error = expected_rocq_result(expected_log)

    cp = (
        subprocess.run(
            [str(ROCQ_CHECKER), str(expected_log)],
            cwd=CASEMATE_CHECK_ROCQ_ROOT,
            capture_output=True,
            check=False,
            text=True,
        )
    )
    print_completed_process(cp)

    if cp.returncode != expected_status:
        raise ValueError(
            f"Fail check on {test_name}: expected exit {expected_status}, "
            f"got {cp.returncode}"
        )

    output = cp.stdout + cp.stderr
    if expected_error is not None and expected_error not in output:
        raise ValueError(
            f"Fail check on {test_name}: expected Rocq error "
            f"{expected_error!r}"
        )

    if expected_error is None and "Success!" not in output:
        raise ValueError(f"Fail check on {test_name}: expected success output")


def main(argv):
    args = parser.parse_args(argv)

    if args.rocq:
        build_rocq_checker()

    for example in EXAMPLES:
        expected_log = (EXAMPLES_ROOT / "expected" / example).with_suffix(".log")

        if expected_log.exists():
            if args.rocq:
                check_rocq_trace(example)
            else:
                check_expected(example, fine_grained=args.fine_grained)


parser = argparse.ArgumentParser()
grp = parser.add_mutually_exclusive_group(required=True)
grp.add_argument("--rocq", action="store_true", default=False)
grp.add_argument("--examples", action="store_true", default=False)

parser.add_argument("--fine-grained", help="do step-by-step simulation checks", action="store_true", default=False)

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
