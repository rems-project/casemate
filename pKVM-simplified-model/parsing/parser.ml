open Extraction.Coq_executable_sm

(* For operations that are not (yet) modeled by the SM *)
exception NotParsed

let parse_write (trans : string) : trans_write_data =
  Scanf.sscanf trans "W%s %Li %Li" (fun str addr value ->
      {
        twd_mo =
          (match str with
          | "" | "page" (* not sure about the page *) -> WMO_plain
          | "rel" -> WMO_release
          | _ ->
              Printf.eprintf "Error while parsing a write transition %s\n" trans;
              exit 1);
        twd_phys_addr = Big_int_Z.big_int_of_int64 addr;
        twd_val = Big_int_Z.big_int_of_int64 value;
      })

let parse_read (trans : string) : trans_read_data =
  Scanf.sscanf trans "R %Li (=%Li)" (fun addr value ->
      {
        trd_phys_addr = Big_int_Z.big_int_of_int64 addr;
        trd_val = Big_int_Z.big_int_of_int64 value;
      })

let parse_DSB (trans : string) : barrier =
  Barrier_DSB
    (match trans with
    | "DSB_ish" -> MBReqDomain_InnerShareable
    | "DSB_ishst" -> MBReqDomain_FullSystem (* Not sure *)
    | "DSB_nsh" -> MBReqDomain_OuterShareable
    | _ ->
        Printf.eprintf "Error while parsing a DSB transition %s\n" trans;
        exit 1)

let parse_TLBI (trans : string) : tLBI =
  try
    Scanf.sscanf trans "%s pfn=%Li level=%Li" (fun typ addr _ ->
        let op, regime, shareability =
          match typ with
          | "TLBI_vmalls12e1" ->
              ( TLBIOp_VMALLS12,
                Regime_EL10,
                Shareability_OSH (* not sure about shareability*) )
          | "TLBI_vmalls12e1is" ->
              (TLBIOp_VMALLS12, Regime_EL10, Shareability_ISH)
          | "TLBI_vmalle1is" -> (TLBIOp_VMALL, Regime_EL10, Shareability_ISH)
          | "TLBI_alle1is" -> (TLBIOp_ALL, Regime_EL10, Shareability_ISH)
          | "TLBI_vmalle1" ->
              ( TLBIOp_VMALL,
                Regime_EL10,
                Shareability_OSH (* not sure about shareability*) )
          | "TLBI_vale2is" ->
              ( TLBIOp_VMALL,
                Regime_EL2,
                Shareability_ISH (* not sure about operation *) )
          | "TLBI_vae2is" -> (TLBIOp_VA, Regime_EL2, Shareability_ISH)
          | "TLBI_ipas2e1is" -> (TLBIOp_IPAS2, Regime_EL10, Shareability_ISH)
          | _ ->
              Printf.eprintf "Unsupported TLBI operation %s\n" typ;
              exit 1
        in
        {
          tLBI_rec =
            {
              tLBIRecord_op = op;
              tLBIRecord_regime = regime;
              tLBIRecord_address = Big_int_Z.big_int_of_int64 addr;
            };
          tLBI_shareability = shareability;
        })
  with End_of_file ->
    let op, regime, shareability =
      match trans with
      | "TLBI_vmalls12e1" ->
          (TLBIOp_VMALLS12, Regime_EL10, Shareability_OSH)
          (* not sure shareability *)
      | "TLBI_vmalle1is" -> (TLBIOp_VMALL, Regime_EL10, Shareability_ISH)
      | "TLBI_vmalls12e1is" -> (TLBIOp_VMALLS12, Regime_EL10, Shareability_ISH)
      | "TLBI_vmalle1" ->
          ( TLBIOp_VMALL,
            Regime_EL10,
            Shareability_OSH (* not sure shareability *) )
      | _ ->
          Printf.eprintf "Unsupported TLBI operation %s\n" trans;
          exit 1
    in
    {
      tLBI_rec =
        {
          tLBIRecord_op = op;
          tLBIRecord_regime = regime;
          tLBIRecord_address = Big_int_Z.zero_big_int;
        };
      tLBI_shareability = shareability;
    }

let parse_MSR (trans : string) : trans_msr_data =
  Scanf.sscanf trans "MSR %s %Li" (fun typ value ->
      {
        tmd_sysreg =
          (match typ with
          | "SYSREG_VTTBR" -> SYSREG_VTTBR
          | "SYSREG_TTBR_EL2" -> SYSREG_TTBR_EL2
          | _ ->
              Printf.printf "Error while parsing a MSR transition %s\n" trans;
              exit 1);
        tmd_val = Big_int_Z.big_int_of_int64 value;
      })

let parse_hint (trans : string) : trans_hint_data =
  try
    Scanf.sscanf trans "HINT %s %Li %Li" (fun typ loc value ->
        {
          thd_hint_kind =
            (match typ with
            | "GHOST_HINT_SET_ROOT_LOCK" -> GHOST_HINT_SET_ROOT_LOCK
            | "GHOST_HINT_SET_OWNER_ROOT" -> GHOST_HINT_SET_OWNER_ROOT
            | _ ->
                Printf.eprintf "Error while parsing a hint transition %s\n"
                  trans;
                exit 1);
          thd_location = Big_int_Z.big_int_of_int64 loc;
          thd_value = Big_int_Z.big_int_of_int64 value;
        })
  with End_of_file -> (* Release table: not yet used *) raise NotParsed

let parse_transition (trans : string) : ghost_simplified_model_transition_data =
  if String.starts_with ~prefix:"W" trans then
    GSMDT_TRANS_MEM_WRITE (parse_write trans)
  else if String.starts_with ~prefix:"R " trans then
    GSMDT_TRANS_MEM_READ (parse_read trans)
  else if String.starts_with ~prefix:"DSB" trans then
    GSMDT_TRANS_BARRIER (parse_DSB trans)
  else if String.starts_with ~prefix:"ISB" trans then
    GSMDT_TRANS_BARRIER (Barrier_ISB ())
  else if String.starts_with ~prefix:"TLBI" trans then
    GSMDT_TRANS_TLBI (parse_TLBI trans)
  else if String.starts_with ~prefix:"MSR" trans then
    GSMDT_TRANS_MSR (parse_MSR trans)
  else if String.starts_with ~prefix:"HINT" trans then
    GSMDT_TRANS_HINT (parse_hint trans)
  else (
    Printf.eprintf "Error while parsing instruction %s\n" trans;
    exit 1)

let get_line_number (str : string) : src_loc =
  match Str.split (Str.regexp " in \\|:") str with
  | [ file; line; func ] ->
      { sl_file = file; sl_lineno = int_of_string line; sl_func = func }
  | _ ->
      Printf.eprintf "Error while parsing location information:\n\t%s\n" str;
      exit 1

let parse_line (line : string) : ghost_simplified_model_transition =
  match Str.split (Str.regexp " at \\|; ") line with
  | [ cpu; transition; src_loc ] ->
      let cpu = Scanf.sscanf cpu "CPU: %Ld" (fun i -> i) in
      print_endline transition;
      {
        gsmt_src_loc = Some (get_line_number src_loc);
        gsmt_thread_identifier = Int64.to_int cpu;
        gsmt_data =
          parse_transition (Str.global_replace (Str.regexp "\\.") "" transition);
      }
  | _ ->
      Printf.eprintf "Error while parsing line:\n\t %s\n\n" line;
      exit 1

let transitions =
  let filename =
    if Array.length Sys.argv == 2 then Sys.argv.(1)
    else "../../pkvm-tester/output/fedoralaptop-2024-04-25T14:29:33+01:00/log"
  in
  (* Open file to read *)
  let file = open_in filename in
  let result = ref [] in
  let str = really_input_string file (in_channel_length file) in
  close_in file;
  let i = ref 0 in
  try
    while true do
      (* Beginning of the next relevant line *)
      i := 10 + Str.search_forward (Str.regexp "\o033\\[46;37;1m") str !i;
      (* Length of the line *)
      let j = Str.search_forward (Str.regexp "\o033\\[0m") str !i - !i in
      try result := parse_line (String.sub str !i j) :: !result
      with NotParsed ->
        ();
        incr i
    done;
    !result
  with Not_found -> List.rev !result

(***************************)
(*  Printers  *)
let rec print_string_list = function
  | [] -> ()
  | t :: q ->
      print_endline t;
      print_string_list q

let rec print_int_list : u64 list -> unit = function
  | [] -> ()
  | t :: q ->
      Printf.printf "%x;" (Z.to_nat t);
      print_int_list q

let print_transition = function
  | GSMDT_TRANS_MEM_WRITE _ -> print_endline "W"
  | GSMDT_TRANS_MEM_READ _ -> print_endline "R"
  | GSMDT_TRANS_BARRIER _ -> print_endline "barrier"
  | GSMDT_TRANS_MSR _ -> print_endline "barrier"
  | GSMDT_TRANS_TLBI _ -> print_endline "TLBI"
  | GSMDT_TRANS_HINT _ -> print_endline "Hint"

let rec print_transition_list = function
  | [] -> ()
  | t :: q ->
      print_transition t.gsmt_data;
      print_transition_list q
