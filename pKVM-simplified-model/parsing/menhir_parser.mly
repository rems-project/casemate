
%{
  open Coq_executable_sm
%}

%token AT IN
%token ID CPU
%token COL SCOL
%token <Big_int_Z.big_int> VAL
%token <int> NUM
%token <string> FN
%token W Wrel Wpage
%token READ
%token DSB_ish DSB_ishst DSB_nsh
%token ISB
%token <string> TLBI_ALL
%token <string> TLBI
%token MSR
%token SYSREG_VTTBR SYSREG_TTBR_EL2
%token HINT
%token GHOST_HINT_SET_ROOT_LOCK GHOST_HINT_SET_OWNER_ROOT GHOST_HINT_RELEASE_TABLE
%token ZALLOC SIZE

%start trans

%type <ghost_simplified_model_transition> trans

%%

trans:
    id= trans_id?
    CPU COL cpu = NUM SCOL
    data = trans_data
    AT
    src_loc = location
  {
    {
      gsmt_src_loc = Some src_loc;
        gsmt_thread_identifier = cpu;
        gsmt_data = data;
        gsmt_id = Option.fold ~none:0 ~some:(fun z -> z) id;
    }
  }

trans_id:
| ID COL id = NUM SCOL
    { id }


location:
  filename = FN COL line_num = NUM IN fn_name = FN
  {
    {
      sl_file = filename; sl_lineno = line_num; sl_func = fn_name
    }
  }

trans_data:
  | typ = write_types addr = VAL value = VAL { GSMDT_TRANS_MEM_WRITE {twd_mo = typ; twd_phys_addr = addr; twd_val = value} }
  | READ addr = VAL value = VAL { GSMDT_TRANS_MEM_READ { trd_phys_addr = addr; trd_val = value; } }
  | DSB_ish {GSMDT_TRANS_BARRIER (Barrier_DSB MBReqDomain_InnerShareable)}
  | DSB_ishst {GSMDT_TRANS_BARRIER (Barrier_DSB MBReqDomain_FullSystem(* not sure *))}
  | DSB_nsh {GSMDT_TRANS_BARRIER (Barrier_DSB MBReqDomain_OuterShareable)}
  | ISB { GSMDT_TRANS_BARRIER (Barrier_ISB ()) }
  | tlbi = TLBI_ALL {
    GSMDT_TRANS_TLBI (
    let op, regime, shareability, level =
      match tlbi with
      | "TLBI_vmalls12e1" -> (TLBIOp_VMALLS12, Regime_EL10, Shareability_NSH, TLBILevel_Any)
      | "TLBI_vmalle1is" -> (TLBIOp_VMALL, Regime_EL10, Shareability_ISH, TLBILevel_Any)
      | "TLBI_vmalls12e1is" -> (TLBIOp_VMALLS12, Regime_EL10, Shareability_ISH, TLBILevel_Any)
      | "TLBI_vmalle1" -> (TLBIOp_VMALL, Regime_EL10, Shareability_NSH, TLBILevel_Any)
      | _ ->
          Printf.eprintf "Unsupported TLBI operation %s\n" tlbi;
          exit 1
    in
    {
      tLBI_rec =
        {
          tLBIRecord_op = op;
          tLBIRecord_regime = regime;
          tLBIRecord_level = level;
          tLBIRecord_address = Big_int_Z.zero_big_int;
        };
      tLBI_shareability = shareability;
    })}
  | tlbi = TLBI addr = VAL NUM {
    GSMDT_TRANS_TLBI (
      let op, regime, shareability, level =
        match tlbi with
        | "TLBI_alle1is" -> (TLBIOp_ALL, Regime_EL10, Shareability_ISH, TLBILevel_Any)
        | "TLBI_vale2is" -> (TLBIOp_VA, Regime_EL2, Shareability_ISH, TLBILevel_Last)
        | "TLBI_vae2is" -> (TLBIOp_VA, Regime_EL2, Shareability_ISH, TLBILevel_Any)
        | "TLBI_ipas2e1is" -> (TLBIOp_IPAS2, Regime_EL10, Shareability_ISH, TLBILevel_Any)
        | _ ->
            Printf.eprintf "Unsupported TLBI operation %s\n" tlbi;
            exit 1
      in
      {
        tLBI_rec =
          {
            tLBIRecord_op = op;
            tLBIRecord_regime = regime;
            tLBIRecord_level = level;
            tLBIRecord_address = addr;
          };
        tLBI_shareability = shareability;
      })}
  | MSR reg = sysreg addr = VAL { GSMDT_TRANS_MSR {tmd_sysreg = reg; tmd_val = addr; } }
  | HINT kind = hint_type loc = VAL value = VAL { GSMDT_TRANS_HINT {thd_hint_kind = kind; thd_location = loc; thd_value = value} }
  | HINT kind = hint_type loc = VAL { GSMDT_TRANS_HINT {thd_hint_kind = kind; thd_location = loc; thd_value = Big_int_Z.big_int_of_int 0} }
  | ZALLOC addr = VAL SIZE COL size = int { GSMDT_TRANS_MEM_ZALLOC {tzd_addr = addr; tzd_size = Big_int_Z.big_int_of_int64 size } }

write_types:
  | W {WMO_plain}
  | Wrel {WMO_release}
  | Wpage {WMO_plain}

sysreg:
  | SYSREG_VTTBR {SYSREG_VTTBR}
  | SYSREG_TTBR_EL2 {SYSREG_TTBR_EL2}

hint_type:
  | GHOST_HINT_SET_ROOT_LOCK {GHOST_HINT_SET_ROOT_LOCK}
  | GHOST_HINT_SET_OWNER_ROOT {GHOST_HINT_SET_OWNER_ROOT}
  | GHOST_HINT_RELEASE_TABLE {GHOST_HINT_RELEASE}

int:
  | num = NUM {Int64.of_int num}
  | va = VAL {Big_int_Z.int64_of_big_int va}
