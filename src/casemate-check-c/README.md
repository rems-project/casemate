# casemate-check

An offline trace checker

Build and run
---


```
$ ./configure
$ make
```

Then run with e.g.

```
$ ./casemate-check ../../examples/expected/bad_bbm_missing_tlbi.log
(mem-init (id 0) (tid 0) (address 0xaaaac68f2000) (size 0x1000) (src "tests/bad_bbm_missing_tlbi.c:25"))
(mem-init (id 1) (tid 0) (address 0xaaaac68f3000) (size 0x1000) (src "tests/bad_bbm_missing_tlbi.c:26"))
(mem-init (id 2) (tid 0) (address 0xaaaac68f4000) (size 0x1000) (src "tests/bad_bbm_missing_tlbi.c:27"))
(hint (id 3) (tid 0) (kind set_root_lock) (location 0xaaaac68f2000) (value 0xaaaac68f5000) (src "tests/bad_bbm_missing_tlbi.c:28"))
(hint (id 4) (tid 0) (kind set_owner_root) (location 0xaaaac68f3000) (value 0xaaaac68f2000) (src "tests/bad_bbm_missing_tlbi.c:29"))
(hint (id 5) (tid 0) (kind set_owner_root) (location 0xaaaac68f4000) (value 0xaaaac68f2000) (src "tests/bad_bbm_missing_tlbi.c:30"))
(mem-write (id 6) (tid 0) (mem-order plain) (address 0xaaaac68f2000) (value 0xaaaac68f3003) (src "tests/bad_bbm_missing_tlbi.c:33"))
(sysreg-write (id 7) (tid 0) (sysreg vttbr_el2) (value 0xaaaac68f2000) (src "tests/bad_bbm_missing_tlbi.c:36"))
(lock (id 8) (tid 0) (address 0xaaaac68f5000) (src "tests/bad_bbm_missing_tlbi.c:38"))
(mem-write (id 9) (tid 0) (mem-order plain) (address 0xaaaac68f2000) (value 0x0) (src "tests/bad_bbm_missing_tlbi.c:39"))
(barrier (id 10) (tid 0) dsb (kind ish) (src "tests/bad_bbm_missing_tlbi.c:40"))
(barrier (id 11) (tid 0) dsb (kind ish) (src "tests/bad_bbm_missing_tlbi.c:41"))
(mem-write (id 12) (tid 0) (mem-order plain) (address 0xaaaac68f2000) (value 0xaaaac68f4003) (src "tests/bad_bbm_missing_tlbi.c:42"))
! BBM invalid unclean->valid
```

This drives the model one transition at a time, and aborts early if the model detects a violation.

Usage
---

```
$ ./casemate-check -h
Usage:
 ./casemate-check TRACE_FILE_NAME [OPTIONS]

Options:
  -t --trace      print trace record for each step
  -c              output in condensed trace format
  -d --diff       show diffs of state
  -U --cleans     show clean locations in states/diffs
  -p --print      print state out at each step
  --dry-run       do not run checks
  -q              quiet, do not print state, or trace steps, or show error messages
  -a --no-colour  ascii-only, no ANSI escape colour codes
  -D --debug      debug mode
```
