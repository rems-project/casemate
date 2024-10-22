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
#define root 0xaaaacf902000
#define child 0xaaaacf903000
#define new_child 0xaaaacf904000
#define l 0xaaaacf905000
(MEM-INIT (id 0) (tid 0) (src "bad_bbm_missing_tlbi.c:29") (address 0xaaaacf902000) (size 0x1000))
(MEM-INIT (id 1) (tid 0) (src "bad_bbm_missing_tlbi.c:30") (address 0xaaaacf903000) (size 0x1000))
(HINT (id 2) (tid 0) (src "bad_bbm_missing_tlbi.c:31") (kind SET_ROOT_LOCK) (location 0xaaaacf902000) (value 0xaaaacf905000))
(HINT (id 3) (tid 0) (src "bad_bbm_missing_tlbi.c:32") (kind SET_OWNER_ROOT) (location 0xaaaacf903000) (value 0xaaaacf902000))
(HINT (id 4) (tid 0) (src "bad_bbm_missing_tlbi.c:33") (kind SET_OWNER_ROOT) (location 0xaaaacf904000) (value 0xaaaacf902000))
(MEM-WRITE (id 5) (tid 0) (src "bad_bbm_missing_tlbi.c:36") (mem-order plain) (address 0xaaaacf902000) (value 0xaaaacf903003))
(MSR (id 6) (tid 0) (src "bad_bbm_missing_tlbi.c:39") (sysreg VTTBR_EL2) (value 0xaaaacf902000))
(LOCK (id 7) (tid 0) (src "bad_bbm_missing_tlbi.c:41") (address 0xaaaacf905000))
(MEM-WRITE (id 8) (tid 0) (src "bad_bbm_missing_tlbi.c:42") (mem-order plain) (address 0xaaaacf902000) (value 0x0))
(BARRIER (id 9) (tid 0) (src "bad_bbm_missing_tlbi.c:43") DSB (kind ish))
(BARRIER (id 10) (tid 0) (src "bad_bbm_missing_tlbi.c:44") DSB (kind ish))
(MEM-WRITE (id 11) (tid 0) (src "bad_bbm_missing_tlbi.c:45") (mem-order plain) (address 0xaaaacf902000) (value 0xaaaacf904003))
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
#define root 0xaaaad8a72000
#define child 0xaaaad8a73000
#define new_child 0xaaaad8a74000
#define l 0xaaaad8a75000
(MEM-INIT (id 0) (tid 0) (src "bad_bbm_missing_tlbi.c:29") (address 0xaaaad8a72000) (size 0x1000))
<identical>
(MEM-INIT (id 1) (tid 0) (src "bad_bbm_missing_tlbi.c:30") (address 0xaaaad8a73000) (size 0x1000))
<identical>
(HINT (id 2) (tid 0) (src "bad_bbm_missing_tlbi.c:31") (kind SET_ROOT_LOCK) (location 0xaaaad8a72000) (value 0xaaaad8a75000))
<identical>
(HINT (id 3) (tid 0) (src "bad_bbm_missing_tlbi.c:32") (kind SET_OWNER_ROOT) (location 0xaaaad8a73000) (value 0xaaaad8a72000))
<identical>
(HINT (id 4) (tid 0) (src "bad_bbm_missing_tlbi.c:33") (kind SET_OWNER_ROOT) (location 0xaaaad8a74000) (value 0xaaaad8a72000))
<identical>
(MEM-WRITE (id 5) (tid 0) (src "bad_bbm_missing_tlbi.c:36") (mem-order plain) (address 0xaaaad8a72000) (value 0xaaaad8a73003))
<identical>
(MSR (id 6) (tid 0) (src "bad_bbm_missing_tlbi.c:39") (sysreg VTTBR_EL2) (value 0xaaaad8a72000))
<identical>
(LOCK (id 7) (tid 0) (src "bad_bbm_missing_tlbi.c:41") (address 0xaaaad8a75000))
<identical>
(MEM-WRITE (id 8) (tid 0) (src "bad_bbm_missing_tlbi.c:42") (mem-order plain) (address 0xaaaad8a72000) (value 0x0))
mem:
    -*[  0xaaaad8a72000]=    aaaad8a73003 (pte_st:V       root:  0xaaaad8a72000, range:               0-      8000000000)
    +*[  0xaaaad8a72000]=               0 (pte_st:IU n  0 root:  0xaaaad8a72000, range:               0-      8000000000)
(BARRIER (id 9) (tid 0) (src "bad_bbm_missing_tlbi.c:43") DSB (kind ish))
mem:
    -*[  0xaaaad8a72000]=               0 (pte_st:IU n  0 root:  0xaaaad8a72000, range:               0-      8000000000)
    +*[  0xaaaad8a72000]=               0 (pte_st:IU d  0 root:  0xaaaad8a72000, range:               0-      8000000000)
(BARRIER (id 10) (tid 0) (src "bad_bbm_missing_tlbi.c:44") DSB (kind ish))
<identical>
(MEM-WRITE (id 11) (tid 0) (src "bad_bbm_missing_tlbi.c:45") (mem-order plain) (address 0xaaaad8a72000) (value 0xaaaad8a74003))
! BBM invalid unclean->valid
```

See how the `MEM-WRITE` on line `"bad_bbm_missing_tlbi.c:42"` updates the state from vald (`V`) to invalid-unclean-no-sync (`IU n`). See the protocol description in [doc/overview.md](../doc/overview.md).