{
  open Menhir_parser

  let keywords = [
  "at" , AT;
  "in", IN;
  "ID", ID;
  "CPU", CPU;
  (* Writes *)
  "W", W;
  "Wrel", Wrel;
  "Wpage", Wpage;
  (* Read *)
  "R", READ;
  (* DSB *)
  "DSB_ish", DSB_ish;
  "DSB_ishst", DSB_ishst;
  "DSB_nsh", DSB_nsh;
  (* ISB *)
  "ISB", ISB;
  "size", SIZE;
  (* MSR *)
  "MSR", MSR;
  "SYSREG_VTTBR", SYSREG_VTTBR;
  "SYSREG_TTBR_EL2", SYSREG_TTBR_EL2;
  (* HINT *)
  "HINT", HINT;
  "GHOST_HINT_SET_ROOT_LOCK", GHOST_HINT_SET_ROOT_LOCK;
  "GHOST_HINT_SET_OWNER_ROOT", GHOST_HINT_SET_OWNER_ROOT;
  "GHOST_HINT_RELEASE_TABLE", GHOST_HINT_RELEASE_TABLE;
  (* ZALLOC *)
  "ZALLOC", ZALLOC;
]

let lexicon: (string, token) Hashtbl.t =
  let lexicon = Hashtbl.create 0 in
  let add (key, builder) = Hashtbl.add lexicon key builder in
  List.iter add keywords; lexicon

let purify_str = 
  Str.global_replace (Str.regexp "\\.\\|(=\\|)\\|pfn\\=\\|level\\=") ""

let value i =
  VAL (Scanf.sscanf (Str.global_replace (Str.regexp "\\.") "" i) "%Li" (fun v -> Big_int_Z.big_int_of_int64 v))
}

let id = ['0'-'9']*+
let value = "0x"'.'*['0'-'9''a'-'f']*+
let value_read = "(=0x"'.'*['0'-'9''a'-'f']*+')'
let tlbi_all = "TLBI_vmall"['0'-'9''a'-'z']*
let tlbi = "TLBI_"['0'-'9''a'-'z']*
let filename = ['0'-'9''a'-'z''_''-''.''/']*+
let keword_regexpr = ['A'-'Z''a'-'z']['A'-'Z''a'-'z''0'-'9'';''_''=']*+


rule token = parse
  | ':' {COL}
  | ';' {SCOL}
  (* Hexa 0x....0 *)
  | value as i {value i}
  | "(="(value as i)")" {value i}
  | "pfn="(value as i) {value i}
  (* decimal number *)
  | id as i
  | "level="(id as i)
    {NUM (int_of_string i)}
  (* TLBIs *)
  | tlbi_all as t {TLBI_ALL t}
  | tlbi as t {TLBI t}
  | keword_regexpr as id {
      try
        Hashtbl.find lexicon id
      with Not_found ->
        FN id
    }
  | filename as f {FN f}
  | '\n' {Lexing.new_line lexbuf; token lexbuf}
  | ' ' { token lexbuf }
  | _ as str {
      let pos = Lexing.lexeme_start_p lexbuf in
      let loc pos =
        let open Lexing in
        let l = pos.pos_lnum in
        let c = pos.pos_cnum - pos.pos_bol + 1 in
        Printf.eprintf "line %d, characters %d-%d:\n"  l (c - 1) c in
      loc pos;
      Printf.printf "\x1b[33m=>%c<=\x1b[0m\n" str;
      failwith "invalid token"
    }
