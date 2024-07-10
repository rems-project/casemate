open Coq_executable_sm

let p0xZ ppf z = Fmt.pf ppf "0x%Lx" (Big_int_Z.int64_of_big_int z)
let pp_u64 = p0xZ
let pp_phys_addr_t = p0xZ

type tLBIOp = [%import: Coq_executable_sm.tLBIOp] [@@deriving show]
type regime = [%import: Coq_executable_sm.regime] [@@deriving show]
type tLBILevel = [%import: Coq_executable_sm.tLBILevel] [@@deriving show]
type tLBIRecord = [%import: Coq_executable_sm.tLBIRecord] [@@deriving show]
type shareability = [%import: Coq_executable_sm.shareability] [@@deriving show]
type tLBI = [%import: Coq_executable_sm.tLBI] [@@deriving show]

let pp_transition_data ppf = function
  | GSMDT_TRANS_MEM_WRITE
      { twd_mo = typ; twd_phys_addr = addr; twd_val = value } ->
      Fmt.pf ppf "W%s %a %a"
        (match typ with
        | WMO_release -> "rel"
        | WMO_page -> "page"
        | WMO_plain -> "")
        p0xZ addr p0xZ value
  | GSMDT_TRANS_MEM_ZALLOC { tzd_addr = addr; tzd_size = size } ->
      Fmt.pf ppf "ZALLOC %a size %a" p0xZ addr p0xZ size
  | GSMDT_TRANS_MEM_READ { trd_phys_addr = addr; trd_val = value } ->
      Fmt.pf ppf "R %a (=%a)" p0xZ addr p0xZ value
  | GSMDT_TRANS_BARRIER _ -> Fmt.pf ppf "barrier"
  | GSMDT_TRANS_MSR { tmd_sysreg = reg; tmd_val = value } ->
      Fmt.pf ppf "MSR %s %a"
        (match reg with
        | SYSREG_TTBR_EL2 -> "SYSREG_TTBR_EL2"
        | SYSREG_VTTBR -> "SYSREG_VTTBR")
        p0xZ value
  | GSMDT_TRANS_TLBI data -> Fmt.pf ppf "TLBI %a" pp_tLBI data
  | GSMDT_TRANS_HINT _ -> Fmt.pf ppf "Hint"
  | GSMDT_TRANS_LOCK l ->
      Fmt.pf ppf "%s %a"
        (match l.tld_kind with LOCK -> "LOCK" | UNLOCK -> "UNLOCK")
        p0xZ l.tld_addr

let pp_location ppf = function
  | Some loc ->
      Fmt.pf ppf "@[%s:%d@ in@ %s@]" loc.sl_file loc.sl_lineno loc.sl_func
  | None -> Fmt.pf ppf "unknown location"

let pp_transition ppf trans =
  Fmt.pf ppf "@[ID: %d;@ CPU: %d;@ %a@ at@ %a@]" trans.gsmt_id
    trans.gsmt_thread_identifier pp_transition_data trans.gsmt_data pp_location
    trans.gsmt_src_loc

let pp_error ppf = function
  | GSME_bbm_violation (violation, addr) ->
      Fmt.pf ppf "@[BBM violation:@ %s %a@]"
        (match violation with
        | VT_valid_on_invalid_unclean -> "Wrote valid on invalid unclean"
        | VT_valid_on_valid -> "Wrote valid on another valid descriptor"
        | VT_release_unclean -> "Tried to release a page that was still unclean")
        p0xZ addr
  | GSME_not_a_pte (str, addr) ->
      Fmt.pf ppf "Address %a was expected to be a PTE in function %s" p0xZ addr
        str
  | GSME_inconsistent_read -> Fmt.pf ppf "GSME_inconsistent_read"
  | GSME_uninitialised (str, addr) ->
      Fmt.pf ppf "Address %a was uninitialized in function %s" p0xZ addr str
  | GSME_unclean_child loc ->
      Fmt.pf ppf "An unclean child has been encountered at address: %a" p0xZ loc
  | GSME_write_on_not_writable loc ->
      Fmt.pf ppf "Tried to write while a parent is unclean at address %a" p0xZ
        loc
  | GSME_double_use_of_pte loc ->
      Fmt.pf ppf "PTE at address %a is used in two page-tables" p0xZ loc
  | GSME_root_already_exists -> Fmt.pf ppf "GSME_root_already_exists"
  | GSME_unaligned_write -> Fmt.pf ppf "unaligned write"
  | GSME_double_lock_acquire (i, j) ->
      Fmt.pf ppf "locking error, locked owned by %i, used by %i" i j
  | GSME_transition_without_lock i ->
      Fmt.pf ppf
        "Tried to take make a step without owning the lock at address: %a" p0xZ
        i
  | GSME_unimplemented -> Fmt.pf ppf "GSME_unimplemented"
  | GSME_internal_error e ->
      Fmt.pf ppf "@[GSME_internal_error:@ %s@]"
        (match e with
        | IET_infinite_loop -> "the maximum number of iterations was reached."
        | IET_unexpected_none -> "a None was found where it was unexpected."
        | IET_no_write_authorization -> "no write authorization was found.")
  | GSME_write_without_authorization addr ->
      Fmt.pf ppf "Wrote plain without being authorized to at address %a" p0xZ
        addr
  | GSME_parent_invalidated addr ->
      Fmt.pf ppf "Address %a's parent was invalidated" p0xZ addr
  | GSME_owned_pte_accessed_by_other_thread (str, addr) ->
      Fmt.pf ppf "Private PTE %a was accessed by other thread in function %s"
        p0xZ addr str

let pp_log ppf = function
  | Inconsistent_read (a, b, c) ->
      Fmt.pf ppf "Inconsistent read, expected %a, got %a at address %a" p0xZ a
        p0xZ b p0xZ c
  | Warning_read_write_non_allocd x ->
      Fmt.pf ppf "Read/wrote a non-alloc'd location at address %a" p0xZ x
  | Warning_unsupported_TLBI ->
      Fmt.pf ppf
        "Warning: unsupported TLBI, defaulting to TLBI VMALLS12E1IS;TLBI ALLE2."
  | Log (a, x) -> Fmt.pf ppf "%s: %a" a p0xZ x

let pp_logs ppf log = (Fmt.list ~sep:Fmt.comma pp_log) ppf log

let pp_step_result :
    ( Coq_executable_sm.ghost_simplified_model,
      Coq_executable_sm.ghost_simplified_model_error )
    result
    Fmt.t =
  Fmt.(
    result ~ok:(const string "Success!\n") ~error:(fun ppf ->
        Fmt.pf ppf "@[<v>@[<2>Error:@ @[%a@]@]@]" pp_error))

(* Automatically derive printers using pretty evil metaprogramming, with
   ppx_import and ppx_deriving.show.

   Each `type foo = [%import: foo] [@@deriving show]` creates the function
   `pp_foo` and can be replaced with a custom `pp_foo` to control the
   printing.

   Dear future reader: when ppx_import finally totally breaks, please rewrite
   the printers by hand.
*)

type owner_t = [%import: Coq_executable_sm.owner_t] [@@deriving show]

let pp_sm_pte_state ppf state =
  Fmt.pf ppf
    (match state with
    | SPS_STATE_PTE_VALID _ -> "valid"
    | SPS_STATE_PTE_INVALID_CLEAN _ -> "invalid clean"
    | SPS_STATE_PTE_INVALID_UNCLEAN unclean_state -> (
        "unclean "
        ^^
        match unclean_state.ai_lis with
        | LIS_unguarded -> "unguarded"
        | LIS_dsbed -> "dsbed"
        | LIS_dsb_tlbi_all -> "dsb_tlbi_all"
        | LIS_dsb_tlbi_ipa -> "dsb_tlbi_ipa"
        | LIS_dsb_tlbied -> "dsb_tlbied"
        | LIS_dsb_tlbi_ipa_dsb -> "dsb_tlbi_ipa_dsb")
    | SPS_STATE_PTE_NOT_WRITABLE -> "Clean, Not writable")

let pp_pte_rec ppf = function
  | PTER_PTE_KIND_TABLE t -> Fmt.pf ppf "Table: %a" p0xZ t
  | PTER_PTE_KIND_MAP t ->
      Fmt.pf ppf "Table: %a-%a" p0xZ t.range_start p0xZ
        (Z.add t.range_start t.range_size)
  | PTER_PTE_KIND_INVALID -> Fmt.pf ppf "Invalid"

let pp_stage_t ppf = function S1 -> Fmt.pf ppf "1" | S2 -> Fmt.pf ppf "2"

let pp_level_t ppf = function
  | L0 -> Fmt.pf ppf "0"
  | L1 -> Fmt.pf ppf "1"
  | L2 -> Fmt.pf ppf "2"
  | L3 -> Fmt.pf ppf "3"
  | Lerror -> Fmt.pf ppf "error"

let pp_ghost_exploded_descriptor ppf desc =
  Fmt.pf ppf
    "{@[<2>@ region: %a-%a;@ level: %a;@ stage: %a;@ owner: %a@ pte kind: %a;@ \
     state: %a;@ @]}"
    p0xZ desc.ged_ia_region.range_start p0xZ
    (Z.add desc.ged_ia_region.range_start desc.ged_ia_region.range_size)
    pp_level_t desc.ged_level pp_stage_t desc.ged_stage p0xZ desc.ged_owner
    pp_pte_rec desc.ged_pte_kind pp_sm_pte_state desc.ged_state

let pp_sm_location ppf sl =
  Fmt.pf ppf "@[val: %a@ %a@]" p0xZ sl.sl_val
    (fun ppf -> function
      | Some pte -> Fmt.pf ppf "@ %a" pp_ghost_exploded_descriptor pte
      | _ -> ())
    sl.sl_pte

type pte_roots = [%import: Coq_executable_sm.pte_roots] [@@deriving show]

let pp_ghost_simplified_model_state ppf m =
  let pp_k_v =
    Fmt.pair p0xZ pp_sm_location ~sep:(fun ppf () -> Fmt.pf ppf "@ ->@ ")
    |> Fmt.box
  in
  Fmt.pf ppf "@[<2>{ %a }@]"
    Fmt.(list ~sep:comma pp_k_v)
    (Cmap.fold
       (fun k v xs ->
         match v.sl_pte with
         | Some _ -> (Big_int_Z.shift_left_big_int k 3, v) :: xs
         | None -> xs)
       m [])

let pp_ghost_simplified_model_zallocd ppf m =
  Fmt.pf ppf "@[<2>{ %a }@]"
    Fmt.(list ~sep:comma p0xZ)
    (Zmap.fold (fun x () xs -> Big_int_Z.shift_left_big_int x 12 :: xs) m [])

let pp_lock_entry ppf (root, addr, status, auth) =
  match status with
  | None -> Fmt.pf ppf "%a -> %a unlocked" p0xZ root p0xZ addr
  | Some x ->
      Fmt.pf ppf "%a -> %a locked by %d%s" p0xZ root p0xZ addr x
        (match auth with
        | None -> ""
        | Some Write_authorized -> "; authorized to write"
        | Some Write_unauthorized -> "; unauthorized to write")

let pp_ghost_simplified_model_locks ppf m =
  Fmt.pf ppf "@[<2>{ %a }@]"
    Fmt.(list ~sep:comma pp_lock_entry)
    (Zmap.fold
       (fun root addr xs ->
         ( root,
           addr,
           Zmap.find_opt addr m.gsm_lock_state,
           Zmap.find_opt addr m.gsm_lock_authorization )
         :: xs)
       m.gsm_lock_addr [])

let pp_ghost_simplified_model ppf m =
  Fmt.pf ppf
    "roots:@ @[<2>%a@]@. memory:@ @[<2>%a@]@. zalloc'd:@ @[<2>%a@]@. locks:@ \
     @[<2>%a@]@."
    pp_pte_roots m.gsm_roots pp_ghost_simplified_model_state m.gsm_memory
    pp_ghost_simplified_model_zallocd m.gsm_zalloc
    pp_ghost_simplified_model_locks m

let pp_state state =
  Fmt.(result ~ok:pp_ghost_simplified_model ~error:pp_error) state

let pp_tr ppf tr =
  Fmt.pf ppf "%a: @[%a@]" Fmt.(styled `Red string) "TRANS" pp_transition tr
