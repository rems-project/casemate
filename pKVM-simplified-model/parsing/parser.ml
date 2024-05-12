open Extraction.Coq_executable_sm

let strip_prefix ~prefix s =
  let n = String.length s
  and pn = String.length prefix in
  if n < pn then None else
  if String.sub s 0 pn <> prefix then None else
    Some (String.sub s pn (n - pn))

let strip_suffix ~suffix s =
  let n = String.length s
  and sn = String.length suffix in
  if n < sn then None else
  if String.sub s (n - sn) sn <> suffix then None else
    Some (String.sub s 0 (n - sn))

let parse_line line =
  let prefix = "\o033[46;37;1m"
  and suffix = "\o033[0m" in
  match strip_prefix line ~prefix with
  | None -> None
  | Some line' ->
      match strip_suffix line' ~suffix with
      | None -> Fmt.invalid_arg "Ill-formed line: %S" line
      | Some line' ->
          let buf = Lexing.from_string line' in
          try Some (Menhir_parser.trans Lexer.token buf) with
          | Menhir_parser.Error -> Fmt.invalid_arg "Parse error: %S" line

let transitions ic = Iters.lines ic |> Iters.filter_map parse_line

(***************************)
(*  Printers  *)

let pp_transition_data ppf = function
  | GSMDT_TRANS_MEM_WRITE
      { twd_mo = typ; twd_phys_addr = addr; twd_val = value } ->
      Fmt.pf ppf "W%s 0x%Lx 0x%Lx"
        (match typ with WMO_release -> "rel" | WMO_plain -> "")
        (Big_int_Z.int64_of_big_int addr)
        (Big_int_Z.int64_of_big_int value)
  | GSMDT_TRANS_MEM_ZALLOC { tzd_addr = addr; tzd_size = size } ->
      Fmt.pf ppf "ZALLOC 0x%Lx size %Ld"
        (Big_int_Z.int64_of_big_int addr)
        (Big_int_Z.int64_of_big_int size)
  | GSMDT_TRANS_MEM_READ { trd_phys_addr = addr; trd_val = value } ->
      Fmt.pf ppf "R 0x%Lx (=0x%Lx)"
        (Big_int_Z.int64_of_big_int addr)
        (Big_int_Z.int64_of_big_int value)
  | GSMDT_TRANS_BARRIER _ -> Fmt.pf ppf "barrier"
  | GSMDT_TRANS_MSR { tmd_sysreg = reg; tmd_val = value } ->
      Fmt.pf ppf "MSR %s 0x%Lx"
        (match reg with
        | SYSREG_TTBR_EL2 -> "SYSREG_TTBR_EL2"
        | SYSREG_VTTBR -> "SYSREG_VTTBR")
        (Big_int_Z.int64_of_big_int value)
  | GSMDT_TRANS_TLBI _ -> Fmt.pf ppf "TLBI"
  | GSMDT_TRANS_HINT _ -> Fmt.pf ppf "Hint"

let pp_location ppf = function
  | Some loc -> Fmt.pf ppf "%s:%d in %s" loc.sl_file loc.sl_lineno loc.sl_func
  | None -> Fmt.pf ppf "unknown location"

let pp_transition ppf trans =
  Fmt.pf ppf "ID: %d; CPU: %d; %a at %a@\n" trans.gsmt_id
    trans.gsmt_thread_identifier pp_transition_data trans.gsmt_data pp_location
    trans.gsmt_src_loc

let print_string_list = Fmt.pr "%a@." (Fmt.Dump.list Fmt.string)

let print_int_list =
  let pp_z_hex ppf z = Fmt.pf ppf "%x" (Z.to_nat z) in
  Fmt.pr "%a@." (Fmt.Dump.list pp_z_hex)

let print_transition_list =
  let pp ppf x = pp_transition_data ppf x.gsmt_data in
  Fmt.pr "%a@." (Fmt.Dump.list pp)

let pp_error ppf = function
  | GSME_bbm_violation violation ->
      Fmt.pf ppf "BBM violation: %s"
        (match violation with
        | VT_valid_on_invalid_unclean -> "Wrote valid on invalid unclean"
        | VT_valid_on_valid -> "Wrote valid on antother valid descriptor"
        | VT_realease_unclean ->
            "Tried to release a page that was still unclean")
  | GSME_not_a_pte (str, addr) ->
      Fmt.pf ppf "Address %Lx was expected to be a PTE in function %s"
        (Big_int_Z.int64_of_big_int addr)
        str
  | GSME_inconsistent_read -> Fmt.pf ppf "GSME_inconsistent_read"
  | GSME_uninitialised (str, addr) ->
      Fmt.pf ppf "Address %Lx was uninitialized in function %s"
        (Big_int_Z.int64_of_big_int addr)
        str
  | GSME_unclean_child -> Fmt.pf ppf "GSME_unclean_child"
  | GSME_double_use_of_pte -> Fmt.pf ppf "GSME_double_use_of_pte"
  | GSME_root_already_exists -> Fmt.pf ppf "GSME_root_already_exists"
  | GSME_unimplemented -> Fmt.pf ppf "GSME_unimplemented"
  | GSME_internal_error e ->
      Fmt.pf ppf "GSME_internal_error: %s"
        (match e with
        | IET_infinite_loop -> "the maximum number of iterations was reached."
        | IET_unexpected_none -> "a None was found where it was unexpected.")

let pp_log ppf = function
  | Inconsistent_read (a, b, c) ->
      Fmt.pf ppf "Inconsistent read, expected %Lx, got %Lx at address %Lx"
        (Big_int_Z.int64_of_big_int a)
        (Big_int_Z.int64_of_big_int b)
        (Big_int_Z.int64_of_big_int c)
  | Warning_read_write_non_allocd x ->
      Fmt.pf ppf "Read/wrote a non-alloc'd location at address %Lx"
        (Big_int_Z.int64_of_big_int x)
  | Warning_unsupported_TLBI ->
      Fmt.pf ppf
        "Warning: unsupported TLBI, defaulting to TLBI VMALLS12E1IS;TLBI ALLE2."

let pp_result ppf = function
  | SMR_success -> Fmt.pf ppf "Success!"
  | SMR_failure (error_code, trans) ->
      Fmt.pf ppf "Error:\n\t\t%a@.\t@[Transition that failed:\n\t\t@[%a@]@]"
        pp_error error_code pp_transition trans

let pp_model_result ppf res =
  Fmt.pf ppf "Logs:@.\t@[%a@]\nResult:@.\t@[%a@]\n" (Fmt.Dump.list pp_log)
    res.gsmr_log pp_result res.gsmr_result

