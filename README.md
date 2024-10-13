# Casemate: Concurrent Abstract Semantic Monitoring of the Architectural Envelope

Dynamic monitoring of architectural protocols for virtual memory.

## Arm-A and Break-before-make

Kernels and hypervisors enforce isolation between VMs
by leveraging the *virtual memory* mechanism of the hardware.
Concretely, they dictate how hardware *memory management units* (MMUs)
in hardware translate *virtual addresses* manipulated by those VMs into the *physical addresses* of the system.
They do so by maintaining *page tables*, the in-memory data structures that the MMUs read.

Page tables are looked up by the MMU and use specialised caches, called Translation Lookaside Buffers (TLBs),
and on Arm those TLBs must be manually cleared by software.
Arm require software follow a specific protocol called **break-before-make**,
and failure to follow this protocol will break any isolation guarantees the software tries to enforce.


## Usage

XXX