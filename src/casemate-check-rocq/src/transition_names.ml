open Rocq_casemate

let find_by_name name table = List.assoc_opt name table

let name_of value table =
  match List.find_opt (fun (_, candidate) -> candidate = value) table with
  | Some (name, _) -> name
  | None -> invalid_arg "unknown extracted transition constructor"

let write_orders =
  [
    ("plain", WriteOrderPlain);
    ("page", WriteOrderPage);
    ("release", WriteOrderRelease);
  ]

let write_order_of_string name = find_by_name name write_orders
let string_of_write_order order = name_of order write_orders

let sysregs =
  [
    ("vttbr_el2", SYSREG_VTTBR);
    ("ttbr0_el2", SYSREG_TTBR_EL2);
    ("vtcr_el2", SYSREG_VTCR_EL2);
    ("hcr_el2", SYSREG_HCR_EL2);
    ("tcr_el2", SYSREG_TCR_EL2);
    ("sctlr_el2", SYSREG_SCTLR_EL2);
    ("mair_el2", SYSREG_MAIR_EL2);
  ]

let sysreg_of_string name = find_by_name name sysregs
let string_of_sysreg sysreg = name_of sysreg sysregs

let hints =
  [
    ("set_root_lock", Hint_SetRootLock);
    ("set_owner_root", Hint_SetOwnerRoot);
    ("release_table", Hint_ReleaseTable);
    ("set_pte_thread_owner", Hint_SetPteThreadOwner);
  ]

let hint_of_string name = find_by_name name hints
let string_of_hint hint = name_of hint hints

let tlbis =
  [
    ("vmalls12e1", TLBI_vmalls12e1);
    ("vmalls12e1is", TLBI_vmalls12e1is);
    ("vmalle1is", TLBI_vmalle1is);
    ("vmalle1", TLBI_vmalle1);
    ("alle1", TLBI_alle1);
    ("alle1is", TLBI_alle1is);
    ("alle2", TLBI_alle2);
    ("alle2is", TLBI_alle2is);
    ("vale2is", TLBI_vale2is);
    ("vae2is", TLBI_vae2is);
    ("ipas2e1is", TLBI_ipas2e1is);
  ]

let tlbi_of_string name = find_by_name name tlbis
let string_of_tlbi tlbi = name_of tlbi tlbis

let tlbi_needs_value = function
  | TLBI_vale2is | TLBI_vae2is | TLBI_ipas2e1is -> true
  | TLBI_vmalls12e1 | TLBI_vmalls12e1is | TLBI_vmalle1is | TLBI_vmalle1
  | TLBI_alle1 | TLBI_alle1is | TLBI_alle2 | TLBI_alle2is ->
      false
