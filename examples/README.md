# Examples

A collection of small unit-test like programs which drive the online (WIP: and online) checks.
Each test is a small C program which uses the C library hooks to step transitions to generate a trace

Usage
---


To configure and build the tests:

```
$ ./configure
$ make
```

Once built, tests can be run directly:

```
$ ./bad_bbm_missing_tlbi
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

Logs can be checked against the expected result:
```
$ ./bad_bbm_missing_tlbi -a > /tmp/test.log   # Note -a to turn off formatting
$ ./scripts/check_simulation.py /tmp/test.log expected/bad_bbm_missing_tlbi.log
```

See the [expected/](./expected/) directory for example expected output logs for the test programs.

Log formats
---

The tests print in a uniform log format with three sections:
```
HEADER
TRACE RECORDS
[! FAILURE]
```

The header helps the simulation checker guess the relation between variables and addresses for checking equality,
the middle section is a newline-separated log of the traces as described in the trace format,
and the last line can optionally be an exclamation-point-prefixed error message, which must also match.

Prints and diffs
---

The examples can be ran with the printing and diffing machinery enabled,
which shows updates to unclean locations:

```
$ ./bad_bbm_missing_tlbi -d
(mem-init (id 0) (tid 0) (address 0xaaaadc0e2000) (size 0x1000) (src "tests/bad_bbm_missing_tlbi.c:25"))
<identical>
(mem-init (id 1) (tid 0) (address 0xaaaadc0e3000) (size 0x1000) (src "tests/bad_bbm_missing_tlbi.c:26"))
<identical>
(mem-init (id 2) (tid 0) (address 0xaaaadc0e4000) (size 0x1000) (src "tests/bad_bbm_missing_tlbi.c:27"))
<identical>
(hint (id 3) (tid 0) (kind set_root_lock) (location 0xaaaadc0e2000) (value 0xaaaadc0e5000) (src "tests/bad_bbm_missing_tlbi.c:28"))
<identical>
(hint (id 4) (tid 0) (kind set_owner_root) (location 0xaaaadc0e3000) (value 0xaaaadc0e2000) (src "tests/bad_bbm_missing_tlbi.c:29"))
<identical>
(hint (id 5) (tid 0) (kind set_owner_root) (location 0xaaaadc0e4000) (value 0xaaaadc0e2000) (src "tests/bad_bbm_missing_tlbi.c:30"))
<identical>
(mem-write (id 6) (tid 0) (mem-order plain) (address 0xaaaadc0e2000) (value 0xaaaadc0e3003) (src "tests/bad_bbm_missing_tlbi.c:33"))
<identical>
(sysreg-write (id 7) (tid 0) (sysreg vttbr_el2) (value 0xaaaadc0e2000) (src "tests/bad_bbm_missing_tlbi.c:36"))
<identical>
(lock (id 8) (tid 0) (address 0xaaaadc0e5000) (src "tests/bad_bbm_missing_tlbi.c:38"))
<identical>
(mem-write (id 9) (tid 0) (mem-order plain) (address 0xaaaadc0e2000) (value 0x0) (src "tests/bad_bbm_missing_tlbi.c:39"))
mem:
    -*[  0xaaaadc0e2000]=    aaaadc0e3003 (pte_st:V       root:  0xaaaadc0e2000, range:               0-      8000000000)
    +*[  0xaaaadc0e2000]=               0 (pte_st:IU n  0 root:  0xaaaadc0e2000, range:               0-      8000000000)
(barrier (id 10) (tid 0) dsb (kind ish) (src "tests/bad_bbm_missing_tlbi.c:40"))
mem:
    -*[  0xaaaadc0e2000]=               0 (pte_st:IU n  0 root:  0xaaaadc0e2000, range:               0-      8000000000)
    +*[  0xaaaadc0e2000]=               0 (pte_st:IU d  0 root:  0xaaaadc0e2000, range:               0-      8000000000)
(barrier (id 11) (tid 0) dsb (kind ish) (src "tests/bad_bbm_missing_tlbi.c:41"))
<identical>
(mem-write (id 12) (tid 0) (mem-order plain) (address 0xaaaadc0e2000) (value 0xaaaadc0e4003) (src "tests/bad_bbm_missing_tlbi.c:42"))
! BBM invalid unclean->valid
```

See how the `mem-write` on line `"bad_bbm_missing_tlbi.c:42"` updates the state from vald (`V`) to invalid-unclean-no-sync (`IU n`). See the protocol description in [doc/overview.md](../doc/overview.md).