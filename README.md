# Casemate: Concurrent Architectural System-level Monitoring and Testing

Casemate is a dynamic monitoring tool for checking architecture-level protocols in systems code.

Description
---

The primary protocol casemate looks for is **break-before-make**.

Kernels and hypervisors enforce isolation between VMs
by leveraging the *virtual memory* mechanism of the hardware.
Concretely, they dictate how hardware *memory management units* (MMUs)
in hardware translate *virtual addresses* manipulated by those VMs into the *physical addresses* of the system.
They do so by maintaining *page tables*, the in-memory data structures that the MMUs read.

Page tables are looked up by the MMU and use specialised caches, called Translation Lookaside Buffers (TLBs),
and on Arm those TLBs must be manually cleared by software.
Arm require software follow a specific protocol called **break-before-make**,
and failure to follow this protocol will break any isolation guarantees the software tries to enforce.

Usage
---

There are two ways to use casemate:
1. Offline, with `casemate-check`, passing log files generated at runtime.
2. At runtime, with a C version of the checker baked into the library.

### Offline

The offline checker takes log files containing traces,
in a format described in `doc/trace-format.md`,
and checks the trace does not violate the protocols being checked.

It is written as a Rocq program, which is extracted to efficiently executable OCaml,
and its source is located in `src/online/`.

TODO: how to use offline checker.

### Online

This is some standalone C code (located in `src/online/`) which compiles to a standalone object file
which can be linked into the kernel at compile time.
Hooks can be added into the kernel to initialise the model and step the transitions.

The model performs trace checking dynamically, and asserts a failure when a violation of the protocol is detected.

The online checker can also be integrated with some tracing infrastructure to generate logs suitable for offline checking later.

TODO: how to use online checker.

Examples
---

See the [examples](./examples/) directory.

Documentation
---

See [doc/overview.md](./doc/overview.md) for explanation of how the checker works.
See [doc/trace-format.md](./doc/trace-format.md) for information about the format the offline checker accepts.
