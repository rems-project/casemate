open Extraction.Coq_executable_sm

let parse_write (trans : string) : trans_write_data =
  Scanf.sscanf trans "W%s %Li %Li" (fun str addr value ->
      {
        twd_mo =
          (match str with
          | "" -> WMO_plain
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
  Scanf.sscanf trans "%s pfn=%Li level=%Li" (fun typ addr _ ->
      let op, regime, shareability =
        match typ with
        | "TLBI_vmalls12e1" ->
            ( TLBIOp_VMALLS12,
              Regime_EL10,
              Shareability_OSH (* not sure about shareability*) )
        | "TLBI_vmalls12e1is" -> (TLBIOp_VMALLS12, Regime_EL10, Shareability_ISH)
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
            Printf.eprintf "Error while parsing a TLBI transition %s\n" trans;
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
  print_endline trans;
  Scanf.sscanf trans "HINT %s %Li %Li" (fun typ loc value ->
      {
        thd_hint_kind =
          (match typ with
          | "GHOST_HINT_SET_ROOT_LOCK" -> GHOST_HINT_SET_ROOT_LOCK
          | "GHOST_HINT_SET_OWNER_ROOT" -> GHOST_HINT_SET_OWNER_ROOT
          | _ ->
              Printf.eprintf "Error while parsing a hint transition %s\n" trans;
              exit 1);
        thd_location = Big_int_Z.big_int_of_int64 loc;
        thd_value = Big_int_Z.big_int_of_int64 value;
      })

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
    Printf.fprintf stderr "Error while parsing line %s\n" trans;
    exit 1)

let get_line_number (str : string) : src_loc =
  match Str.split (Str.regexp " in \\|:") str with
  | [ file; line; func ] ->
      { sl_file = file; sl_lineno = int_of_string line; sl_func = func }
  | _ ->
      Printf.eprintf "Error while parsing location information:\n\t%s\n" str;
      exit 1

let rec print_list = function
  | [] -> ()
  | t :: q ->
      print_endline t;
      print_list q

let parse_line (line : string) : ghost_simplified_model_transition =
  match Str.split (Str.regexp " at \\|; ") line with
  | [ cpu; transition; src_loc ] ->
      let cpu = Scanf.sscanf cpu "CPU: %Ld" (fun i -> i) in
      {
        gsmt_src_loc = Some (get_line_number src_loc);
        gsmt_thread_identifier = Int64.to_int cpu;
        gsmt_data =
          parse_transition (Str.global_replace (Str.regexp "\\.") "" transition);
      }
  | _ ->
      Printf.eprintf "Error while parsing line:\n\t %s\n" line;
      exit 1

let parse_line (line : string) : ghost_simplified_model_transition =
  (* remove the color tag at beginning and end of word *)
  print_endline line;
  let line = String.sub line 10 (String.length line - 15) in
  parse_line line

let transitions =
  let filename =
    if Array.length Sys.argv == 2 then Sys.argv.(1)
    else
      "../../../pkvm-tester/output/fedoralaptop-2024-04-24T10:52:45+01:00/log"
  in
  (* Open file to read *)
  let file = open_in filename in
  let result = ref [] in
  try
    while true do
      let line = input_line file in
      if String.starts_with ~prefix:"\o033[46;37;1m" line then
        result := parse_line line :: !result
    done;
    !result
  with End_of_file ->
    close_in file;
    List.rev !result
