{
  open Menhir_parser
}

let id = ['0'-'9''a'-'f']*+
let value = "0x"'.'*['0'-'9''a'-'f']*+
let value_read = "(=0x"'.'*['0'-'9''a'-'f']*+')'
let tlbi_all = "TLBI_vmall"['0'-'9''a'-'f']*
let tlbi = "TLBI_"['0'-'9''a'-'z']*
let filename = ['0'-'9''a'-'z''_''-''.']*+

rule token = parse
  | "\o033\\[0m"([^ '*']|'*'[^ ')'])*"\o033\\[46;37;1m" {BETWEEN_TRANS}
  | ([^ '*']|'*'[^ ')'])*"\o033\\[46;37;1m" {BEGIN_TRANS}
  | "\o033\\[0m"([^ '*']|'*'[^ ')'])*eof {END_TRANS}
  | "at" {AT}
  | "in" {IN}
  | "ID" {ID}
  | "CPU" {CPU}
  | ':' {COL}
  | ';' {SCOL}
  | value as i {VAL (Scanf.sscanf (Str.global_replace (Str.regexp "\\.") "" i) "%Li" (fun v -> Big_int_Z.big_int_of_int64 v))}
  | value_read as i {VAL (Scanf.sscanf (Str.global_replace (Str.regexp "\\.\\|(=\\|)") "" i) "%Li" (fun v -> Big_int_Z.big_int_of_int64 v))}
  | filename as f {FN f}
  | id as i {NUM (int_of_string i)}
  (* Writes *)
  | "W" {W}
  | "WREL" {Wrel}
  | "WPAGE" {Wpage}
  (* Read *)
  | "R" {READ}
  (* DSB *)
  | "DSB_ish" {DSB_ish}
  | "DSB_ishst" {DSB_ishst}
  | "DSB_nsh" {DSB_nsh}
  (* ISB *)
  | "ISB" {ISB}
  (* TLBI *)
  | tlbi_all as t {TLBI_ALL t}
  | tlbi as t {TLBI t}
  | "pfn=" {PFN}
  | "level=" {LEVEL}
  (* MSR *)
  | "MSR" {MSR}
  | "SYSREG_VTTBR" {SYSREG_VTTBR}
  | "SYSREG_TTBR_EL2" {SYSREG_TTBR_EL2}
  (* HINT *)
  | "HINT" {HINT}
  | "GHOST_HINT_SET_ROOT_LOCK" {GHOST_HINT_SET_ROOT_LOCK}
  | "GHOST_HINT_SET_OWNER_ROOT" {GHOST_HINT_SET_OWNER_ROOT}
  | "GHOST_HINT_RELEASE_TABLE" {GHOST_HINT_RELEASE_TABLE}
  (* ZALLOC *)
  | "ZALLOC" {ZALLOC}
  | eof {EOF}
  | '\n' {Lexing.new_line lexbuf; token lexbuf}
  | _ as c { token lexbuf }
