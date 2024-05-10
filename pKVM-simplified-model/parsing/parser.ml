open Format
open Lexing
open Extraction.Coq_executable_sm

let filename = ref ""

let loc pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !filename l (c - 1) c

let set_file f s = f := s
let options = []
let usage = "usage: [options] trace file"

let transitions () =
  let begin_str, end_str = ("\o033\\[46;37;1m", "\o033\\[0m") in

  Arg.parse options (set_file filename) usage;

  (* Check that a file has been  *)
  if !filename = "" then (
    eprintf "No trace file to analyze\n@?";
    exit 1);

  (* open file *)
  let ic = open_in !filename in
  let acc = ref [] in
  let buf = ref @@ Lexing.from_string "" in
  let rec loop () =
    let line = input_line ic in
    try
      let start_off =
        String.length begin_str - 1
        + Str.search_forward (Str.regexp begin_str) line 0
      in
      let end_off =
        try Str.search_forward (Str.regexp end_str) line start_off
        with Not_found ->
          eprintf "Ill formed line: @. @[%s@]\n" line;
          exit 1
      in
      buf :=
        Lexing.from_string (String.sub line start_off (end_off - start_off));
      acc := Menhir_parser.trans Lexer.token !buf :: !acc;
      loop ()
    with Not_found -> loop ()
  in
  try
    let xs = List.rev @@ loop () in
    close_in ic;
    xs
  with
  | End_of_file -> List.rev !acc
  | Menhir_parser.Error ->
      let str = Lexing.lexeme !buf in
      Printf.printf "==> \x1b[31m%s\x1b[0m\n" str;
      exit 1

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
  | GSME_bbm_violation -> Fmt.pf ppf "GSME_bbm_violation"
  | GSME_not_a_pte -> Fmt.pf ppf "GSME_not_a_pte"
  | GSME_inconsistent_read -> Fmt.pf ppf "GSME_inconsistent_read"
  | GSME_uninitialised -> Fmt.pf ppf "GSME_uninitialised"
  | GSME_unclean_child -> Fmt.pf ppf "GSME_unclean_child"
  | GSME_double_use_of_pte -> Fmt.pf ppf "GSME_double_use_of_pte"
  | GSME_root_already_exists -> Fmt.pf ppf "GSME_root_already_exists"
  | GSME_unimplemented -> Fmt.pf ppf "GSME_unimplemented"
  | GSME_internal_error -> Fmt.pf ppf "GSME_internal_error"

let pp_result ppf = function
  | SMR_success -> Fmt.pf ppf "Success!"
  | SMR_failure (error_code, trans) ->
      Fmt.pf ppf "Error:\n\t%a Transition that failed:\n\t%a" pp_error
        error_code pp_transition trans

let pp_model_result ppf res =
  Fmt.pf ppf "logs:%a \nresult:%a\n" (Fmt.Dump.list Fmt.string) res.gsmr_log
    pp_result res.gsmr_result
