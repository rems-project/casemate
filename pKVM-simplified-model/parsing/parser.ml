module Z0 = Z (* Don't overwrite Zarith *)
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

let p0xZ ppf z = Fmt.pf ppf "0x%Lx" (Big_int_Z.int64_of_big_int z)

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
  | GSMDT_TRANS_TLBI _ -> Fmt.pf ppf "TLBI"
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
  | GSME_unclean_child -> Fmt.pf ppf "GSME_unclean_child"
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

let pp_result ppf = function
  | SMR_success -> Fmt.pf ppf "Success!"
  | SMR_failure (error_code, trans) ->
      Fmt.pf ppf "@[<2>Error:@ %a.@ @[<2>Transition that failed:@ %a@]@]"
        pp_error error_code pp_transition trans

let pp_model_result ppf res =
  Fmt.pf ppf "@[<2>@[<2>Logs:@ @[%a@]@]@ @[<2>Result:@ @[%a@]@]@]" Fmt.(list ~sep:comma pp_log)
    res.gsmr_log pp_result res.gsmr_result

let _ = ignore (pp_result, pp_model_result)

let pp_error ppf ((error_code, trans), log) =
  Fmt.pf ppf
  "@[<v>@[<2>Logs:@ @[%a@]@]@ @[<2>Error:@ %a.@]@ @[<2>Transition:@ %a@]@]"
  Fmt.(list ~sep:comma pp_log) (List.rev log)
  pp_error error_code
  pp_transition trans

let pp_step_result = Fmt.(result ~ok:(const string "Success!") ~error:pp_error)

(** Entrypoints **)

let with_open_out file f =
  let oc = open_out file in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> f oc)

let marshall_out oc = Iters.iter (fun x -> Marshal.to_channel oc x [])
let marshall_in ic =
  let rec go i = match Marshal.from_channel ic with
  | exception End_of_file -> ()
  | x -> i x; go i in
  Iters.of_f go

let pre_parse bin trace =
  let xs = Iters.in_file trace transitions in
  with_open_out bin @@ fun oc -> marshall_out oc xs

let run_model ?limit src =
  let xs = match src with
  | `Text f -> Iters.in_file f transitions
  | `Bin f -> Iters.in_file f marshall_in in
  let xs = match limit with Some n -> Iters.take n xs | _ -> xs in
  let res = Iters.fold_result step_ state_0 xs in
  Fmt.pr "@[%a@]@." pp_step_result res

(** Cmdline args **)

open Cmdliner

let ($$) f a = Term.(const f $ a)

let info = Cmd.info "parser" ~doc:"Describe me"

let term =
  let open Arg in
  let trace = value @@ pos 0 (some non_dir_file) None @@ info []
              ~docv:"TRACE" ~doc:"The trace file."
  and read  = value @@ opt (some non_dir_file) None @@ info ["r"; "read"]
              ~docv:"FILE" ~doc:"Load a pre-parsed trace. (Cannot have TRACE or --write)"
  and write = value @@ opt (some string) None @@ info ["w"; "write"]
              ~docv:"FILE" ~doc:"Save a pre-parsed trace. (Needs a TRACE, cannot --read.)"
  and limit = value @@ opt (some int) None @@ info ["limit"]
              ~docv:"NUM" ~doc:"Check only the first $(docv) events."
  in
  Term.((fun read write limit trace -> match read, write, trace with
    | None, None, Some f -> Ok (run_model ?limit (`Text f))
    | Some f, None, None -> Ok (run_model ?limit (`Bin f))
    | None, Some e, Some f -> Ok (pre_parse e f)
    | None, None, None -> Error "No input."
    | _ -> Error "Invalid arguments.")
  $$ read $ write $ limit $ trace)
  |> Term.term_result' ~usage:true

let _ = Cmd.v info term |> Cmd.eval
