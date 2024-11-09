Require Import Types.

(* Constants *)
Definition PAGE_SHIFT : u64.t := 12.
Definition PAGE_SIZE : u64.t := 1 << PAGE_SHIFT.

(* Calculate the offset within a page *)
Definition OFFSET_IN_PAGE (x : u64.t) : u64.t :=
  and x (GENMASK (u64.decr PAGE_SHIFT) 0).

(* Align down to the nearest page boundary *)
Definition PAGE_ALIGN_DOWN (x : u64.t) : u64.t :=
  u64.and x (u64.not (GENMASK PAGE_SHIFT 0)).

(* Align up to the nearest page boundary *)
Definition PAGE_ALIGN (x : u64.t) : u64.t :=
  PAGE_ALIGN_DOWN (u64.decr (x u+ PAGE_SIZE)).

(* Check if a value is page-aligned *)
Definition IS_PAGE_ALIGNED (x : u64.t) : bool :=
  (OFFSET_IN_PAGE x) u=? 0.

