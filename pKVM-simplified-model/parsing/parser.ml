module Z0 = Z (* Don't overwrite Zarith *)
open Coq_executable_sm
open Pp

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


let run_model ?(dump_state = false) ?(dump_trans = false) ?limit src =
  let xs = match src with
  | `Text f -> Iters.in_file f transitions
  | `Bin f -> Iters.in_file f marshall_in in
  let xs = match limit with Some n -> Iters.take n xs | _ -> xs in
  let step_ state trans =
    let res = Coq_executable_sm.step trans state in
    if res.gsmsr_log != [] then (
      if dump_trans then Fmt.pr "%a@ @[<2>%a@]@." pp_tr trans pp_logs res.gsmsr_log
        else Fmt.pr "%a@." pp_logs res.gsmsr_log;
      if dump_state then Fmt.pr "@[<2>State:@ @[<2>%a@]@]@." pp_state res.gsmsr_data;
    );
    (* If we reach an error, we dump the transition *)
    if Result.is_error res.gsmsr_data then
      Fmt.pr "@[%a@]@." pp_tr trans;
    res.gsmsr_data
  in
  Iters.fold_result step_ memory_0 xs |> Fmt.pr "@[%a@]@." pp_step_result

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
  and dump_s  = value @@ opt bool false @@ info ["dump-states"]
  and dump_t  = value @@ opt bool false @@ info ["dump-transitions"]
  in
  Term.((fun read write limit dump_state dump_trans trace -> match read, write, trace with
    | None, None, Some f -> Ok (run_model ~dump_state ~dump_trans ?limit (`Text f))
    | Some f, None, None -> Ok (run_model ~dump_state ~dump_trans ?limit (`Bin f))
    | None, Some e, Some f -> Ok (pre_parse e f)
    | None, None, None -> Error "No input."
    | _ -> Error "Invalid arguments.")
  $$ read $ write $ limit $ dump_s $ dump_t $ trace)
  |> Term.term_result' ~usage:true

let _ =
  Fmt_tty.setup_std_outputs();
  Cmd.v info term |> Cmd.eval
