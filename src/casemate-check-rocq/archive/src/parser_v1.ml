let of_line line =
  let buf = Lexing.from_string line in
  try Some (Menhir_parser.trans Lexer.token buf)
  with Menhir_parser.Error -> None
