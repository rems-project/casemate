module Z0 = Z (* Don't overwrite Zarith *)
open Rocq_casemate
open Pp

let parse_line line =
  (* ignore the final line with "!" *)
  if String.length line = 0 || String.get line 0 = '!' then None
  else
    match Parser.of_line line with
    | None -> Fmt.invalid_arg "Parse error: %S" line
    | res -> res

let transitions ic = Iters.lines ic |> Iters.filter_map parse_line

(** Entrypoints **)

let with_open_out file f =
  let oc = open_out file in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> f oc)

let marshall_out oc = Iters.iter (fun x -> Marshal.to_channel oc x [])

let marshall_in ic =
  let rec go i =
    match Marshal.from_channel ic with
    | exception End_of_file -> ()
    | x ->
        i x;
        go i
  in
  Iters.of_f go

let pre_parse bin trace =
  let xs = Iters.in_file trace transitions in
  with_open_out bin @@ fun oc -> marshall_out oc xs

let run_model ?(dump_state = false) ?(dump_roots = false) ?(dump_trans = false)
    ?limit src =
  let xs =
    match src with
    | `Text f -> Iters.in_file f transitions
    | `Bin f -> Iters.in_file f marshall_in
  in
  let xs = match limit with Some n -> Iters.take n xs | _ -> xs in
  let step_ state trans =
    let res = Rocq_casemate.step trans state in
    if res.cmr_log != [] then (
      if dump_trans then
        Fmt.pr "%a@ @[<2>%a@]@." pp_tr trans pp_logs res.cmr_log
      else Fmt.pr "%a@." pp_logs res.cmr_log;
      if dump_roots then
        Fmt.pr "@[<2>Roots:@ @[<2>%a@]@]@." pp_casemate_model_roots state.cms_roots;
      if dump_state then
        Fmt.pr "@[<2>State:@ @[<2>%a@]@]@." pp_casemate_model_state state);
    (* If we reach an error, we dump the transition *)
    if Result.is_error res.cmr_data then Fmt.pr "@[%a@]@." pp_tr trans;
    res.cmr_data
  in
  Iters.fold_result step_ cms_init xs |> Fmt.pr "@[%a@]@." pp_step_result

(** Cmdline args **)

open Cmdliner

let ( $$ ) f a = Term.(const f $ a)
let info = Cmd.info "parser" ~doc:"Describe me"

let term =
  let open Arg in
  let trace =
    value
    @@ pos 0 (some non_dir_file) None
    @@ info [] ~docv:"TRACE" ~doc:"The trace file."
  and read =
    value
    @@ opt (some non_dir_file) None
    @@ info [ "r"; "read" ] ~docv:"FILE"
         ~doc:"Load a pre-parsed trace. (Cannot have TRACE or --write)"
  and write =
    value
    @@ opt (some string) None
    @@ info [ "w"; "write" ] ~docv:"FILE"
         ~doc:"Save a pre-parsed trace. (Needs a TRACE, cannot --read.)"
  and limit =
    value
    @@ opt (some int) None
    @@ info [ "limit" ] ~docv:"NUM" ~doc:"Check only the first $(docv) events."
  and dump_s = value @@ opt bool false @@ info [ "dump-states" ]
  and dump_r = value @@ opt bool false @@ info [ "dump-roots" ]
  and dump_t = value @@ opt bool false @@ info [ "dump-transitions" ] in
  Term.(
    (fun read write limit dump_state dump_roots dump_trans trace ->
      match (read, write, trace) with
      | None, None, Some f ->
          Ok (run_model ~dump_state ~dump_roots ~dump_trans ?limit (`Text f))
      | Some f, None, None ->
          Ok (run_model ~dump_state ~dump_roots ~dump_trans ?limit (`Bin f))
      | None, Some e, Some f -> Ok (pre_parse e f)
      | None, None, None -> Error "No input."
      | _ -> Error "Invalid arguments.")
    $$ read $ write $ limit $ dump_s $ dump_r $ dump_t $ trace)
  |> Term.term_result' ~usage:true

let _ =
  Fmt_tty.setup_std_outputs ();
  Cmd.v info term |> Cmd.eval
