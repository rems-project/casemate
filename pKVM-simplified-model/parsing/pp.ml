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
        (match typ with WMO_release -> "rel" | WMO_plain -> "")
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

let pp_location ppf = function
  | Some loc -> Fmt.pf ppf "@[%s:%d@ in@ %s@]" loc.sl_file loc.sl_lineno loc.sl_func
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
        | VT_valid_on_valid -> "Wrote valid on antother valid descriptor"
        | VT_realease_unclean ->
            "Tried to release a page that was still unclean")
        p0xZ addr
  | GSME_not_a_pte (str, addr) ->
      Fmt.pf ppf "Address %a was expected to be a PTE in function %s"
        p0xZ addr str
  | GSME_inconsistent_read -> Fmt.pf ppf "GSME_inconsistent_read"
  | GSME_uninitialised (str, addr) ->
      Fmt.pf ppf "Address %a was uninitialized in function %s"
        p0xZ addr str
  | GSME_unclean_child loc ->
      Fmt.pf ppf "An unclean child has been encountered at address: %a"
        p0xZ loc
  | GSME_double_use_of_pte -> Fmt.pf ppf "GSME_double_use_of_pte"
  | GSME_root_already_exists -> Fmt.pf ppf "GSME_root_already_exists"
  | GSME_unimplemented -> Fmt.pf ppf "GSME_unimplemented"
  | GSME_internal_error e ->
      Fmt.pf ppf "@[GSME_internal_error:@ %s@]"
        (match e with
        | IET_infinite_loop -> "the maximum number of iterations was reached."
        | IET_unexpected_none -> "a None was found where it was unexpected.")

let pp_log ppf = function
  | Inconsistent_read (a, b, c) ->
      Fmt.pf ppf "Inconsistent read, expected %a, got %a at address %a"
        p0xZ a p0xZ b p0xZ c
  | Warning_read_write_non_allocd x ->
      Fmt.pf ppf "Read/wrote a non-alloc'd location at address %a"
        p0xZ x
  | Warning_unsupported_TLBI ->
      Fmt.pf ppf
        "Warning: unsupported TLBI, defaulting to TLBI VMALLS12E1IS;TLBI ALLE2."
  | Log (a, x) -> Fmt.pf ppf "%s: %a" a p0xZ x


let pp_logs ppf log = 
  (Fmt.list ~sep:Fmt.comma pp_log) ppf log

let pp_step_result : (Coq_executable_sm.ghost_simplified_memory, Coq_executable_sm.ghost_simplified_model_error) result Fmt.t =
  Fmt.(result ~ok:(const string "Success!\n") 
  ~error:(fun ppf -> Fmt.pf ppf "@[<v>@[<2>Error:@ @[%a@]@]@]" pp_error))

  (* Automatically derive printers using pretty evil metaprogramming, with
     ppx_import and ppx_deriving.show. 

     Each `type foo = [%import: foo] [@@deriving show]` creates the function
     `pp_foo` and can be replaced with a custom `pp_foo` to control the
     printing.

     Dear future reader: when ppx_import finally totally breaks, please rewrite
     the printers by hand.
  *)

  type stage_t = [%import: Coq_executable_sm.stage_t] [@@deriving show]
  type lIS = [%import: Coq_executable_sm.lIS] [@@deriving show]
  type lVS = [%import: Coq_executable_sm.lVS] [@@deriving show]
  type aut_valid = [%import: Coq_executable_sm.aut_valid] [@@deriving show]
  type owner_t = [%import: Coq_executable_sm.owner_t] [@@deriving show]
  type thread_identifier = [%import: Coq_executable_sm.thread_identifier] [@@deriving show]
  type aut_invalid_clean = [%import: Coq_executable_sm.aut_invalid_clean] [@@deriving show]
  type aut_invalid_unclean = [%import: Coq_executable_sm.aut_invalid_unclean] [@@deriving show]
  type sm_pte_state = [%import: Coq_executable_sm.sm_pte_state] [@@deriving show]
  type ghost_addr_range = [%import: Coq_executable_sm.ghost_addr_range] [@@deriving show]
  type map_data_t = [%import: Coq_executable_sm.map_data_t] [@@deriving show]
  type table_data_t = [%import: Coq_executable_sm.table_data_t] [@@deriving show]
  type pte_rec = [%import: Coq_executable_sm.pte_rec] [@@deriving show]
  type level_t = [%import: Coq_executable_sm.level_t] [@@deriving show]
  type ghost_exploded_descriptor = [%import: Coq_executable_sm.ghost_exploded_descriptor] [@@deriving show]

  let pp_sm_location ppf sl =
    Fmt.pf ppf "@[%a@ %a@]" p0xZ sl.sl_val
    (fun ppf -> function
      | Some pte -> Fmt.pf ppf "@ %a" pp_ghost_exploded_descriptor pte
      | _ -> ()) sl.sl_pte

  type pte_roots = [%import: Coq_executable_sm.pte_roots] [@@deriving show]

  let pp_ghost_simplified_model_state ppf m =
    let pp_k_v =
      Fmt.pair p0xZ pp_sm_location
      ~sep:(fun ppf () -> Fmt.pf ppf "@ ->@ ") |> Fmt.box in
    Fmt.pf ppf "@[<2>{ %a }@]" Fmt.(list ~sep:comma pp_k_v)
    (state_fold (fun k v xs -> (k, v)::xs) [] m |>
    (* Only print PTEs *)
    List.filter (fun x -> Option.is_some (snd x).sl_pte))

  let pp_ghost_simplified_model_zallocd ppf m =
    Fmt.pf ppf "@[<2>{ %a }@]" Fmt.(list ~sep:comma p0xZ)
    (zallocd_fold (fun x xs -> x::xs) [] m)
  let pp_ghost_simplified_memory ppf m = 
    Fmt.pf ppf "roots:@ @[<2>%a@]@. memory:@ @[<2>%a@]@." pp_pte_roots m.gsm_roots
      pp_ghost_simplified_model_state m.gsm_memory

let pp_state state = 
  Fmt.(result ~ok:pp_ghost_simplified_memory ~error:pp_error) state

let pp_tr ppf tr =
  Fmt.pf ppf "%a: @[%a@]" Fmt.(styled `Red string) "TRANS"
  pp_transition tr

  let _ = ignore (pp_ghost_simplified_model_zallocd)
