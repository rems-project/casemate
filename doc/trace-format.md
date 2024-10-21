# Offline trace-checker format #

The offline trace checker consumes traces from a runtime execution, and performs the break-before-make dynamic check on those traces.

The traces are a sequence of records,
where each record is a trace event tagged with a sequence ID and an originating thread ID:
```
SEQ = "(", "id", int, ")";
TID = "(", "thread", int, ")";
SRC = "(", "src", (string | int), ")"

TRANSITION =
    MEM-WRITE
  | MEM-READ
  | MEM-INIT
  | MEM-SET
  | BARRIER
  | TLBI
  | SYSREG
  | HINT
  | LOCK
  ;

RECORD(t: TRANSITION) =
    "(", t[0], SEQ, TID, t[1..], SRC?, ")"
  ;
```

Records are s-exps which start with the name of the transition,
followed by the sequence and thread IDs,
then the remainin fields,
with the source location in final position.

The source location is optional,
and is either a string containing the source line
or an integer key into an externally defined map from tracepoint to source location.

## transitions

### mem-write

A write to potentially-pagetable memory.

```
MEM-WRITE =
    "mem-write",
         "(", "mem-order", ( "PLAIN" | "RELEASE" ), ")",
         "(", "address", u64, ")",
         "(", "value", u64, ")";
```

### mem-read

A read of potentially-pagetable memory.

```
MEM-READ =
    "mem-read",
         "(", "address", u64, ")",
         "(", "value", u64, ")";
```

### mem-init

Zero initialise memory.

```
MEM-INIT =
    "mem-init",
         "(", "address", u64, ")",
         "(", "size", u64, ")";
```

### mem-set

Wide memory write.
Writes `value` to every byte of the given region.

`address` must be aligned on an 8-byte boundary,
and `size` a multiple of 8.

equvialent to efficiently performing a sequence of `WRITE-MEM` transitions.

```
MEM-SET =
    "mem-set",
         "(", "address", u64, ")",
         "(", "size", u64, ")",
         "(", "value", u8, ")";
```

### barrier

Barriers/fences.

```
BARRIER =
    "barrier", BARRIER-KIND;

DxB-KIND =
    "ISH"
  | "ISHST"
  | "NSH"
  | "SY"
  ;

BARRIER-DSB =
    "DSB",
      "(", "kind", DxB-KIND, ")"

BARRIER-KIND =
    "ISB" | BARRIER-DSB;
```

### TLBIs

```
TLBI =
    "tlbi",
         (TLBI-OP-ALL | TLBI-OP-ADDR);

TLBI-OP-ALL =
    "VMALLS12E1"
  | "VMALLS12E1IS"
  | "VMALLE1IS"
  | "ALLE1IS"
  | ...
  ;

TLBI-OP-ADDR-KIND =
    "VAE2"
  | "VAE2IS"
  | "IPAS2E1IS"
  | ...
  ;

TLBI-OP-ADDR =
    TLBI-OP-ADDR-KIND,
      "(", "addr", u64, ")",
      "(", "level", u64, ")"
  ;
```

### MSR (SysReg Write)

```
SYSREG =
    "sysreg-write"
        "(", "sysreg", ( "VTTBR_El2" | "TTBR0_EL2" ), ")",
        "(", "value", u64, ")"
  ;
```

### HINTs

Hint transitions update purely logical state,
assocating pagetables with locks and so on.

```
HINT =
    "hint",
         "(", "kind", ( "SET_ROOT_LOCK" | "SET_OWNER_ROOT" |
                        "RELEASE" | "SET_PTE_THREAD_OWNER" ), ")",
         "(", "location", u64, ")",
         "(", "value", u64, ")";
```

### LOCKs

Acquire/release of a pagetable-owning lock.

```
LOCK =
    ("lock" | "unlock"),
         "(", "address", u64, ")"
```

## Example trace

```
(MEM-INIT
  (id 0)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:29")
  (address 0xaaaaaf200000)
  (size 0x1000))
(MEM-INIT
  (id 1)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:30")
  (address 0xaaaaaf201000)
  (size 0x1000))
(HINT
  (id 2)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:31")
  (kind SET_ROOT_LOCK)
  (location 0xaaaaaf200000)
  (value 0xaaaaaf203000))
(HINT
  (id 3)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:32")
  (kind SET_OWNER_ROOT)
  (location 0xaaaaaf201000)
  (value 0xaaaaaf200000))
(HINT
  (id 4)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:33")
  (kind SET_OWNER_ROOT)
  (location 0xaaaaaf202000)
  (value 0xaaaaaf200000))
(MEM-WRITE
  (id 5)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:36")
  (mem-order plain)
  (address 0xaaaaaf200000)
  (value 0xaaaaaf201003))
(MSR
  (id 6)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:39")
  (sysreg VTTBR_EL2)
  (value 0xaaaaaf200000))
(LOCK
  (id 7)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:41")
  (address 0xaaaaaf203000))
(MEM-WRITE
  (id 8)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:42")
  (mem-order plain)
  (address 0xaaaaaf200000)
  (value 0x0))
(BARRIER
  (id 9)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:43")
  DSB (kind ish))
(BARRIER
  (id 10)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:44")
  DSB (kind ish))
(MEM-WRITE
  (id 11)
  (tid 0)
  (src "test04_bad_bbm_missing_tlbi.c:45")
  (mem-order plain)
  (address 0xaaaaaf200000)
  (value 0xaaaaaf202003))
```

Arguments can be also be given positionally for more compressed traces:

```
(mem-write 1 1 "src" release 42 93)
(lock 2 1 "src" 42)
(msr 3 1 "src" TTBR_EL2 93)
(barrier 4 1 "src" DSB ISH)
(hint 5 1 "src" SET_PTE_THREAD_OWNER 42 93)
```
