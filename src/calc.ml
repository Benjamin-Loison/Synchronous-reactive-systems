open Ast

let _ =
  try
    let oi = open_in "test.node" in
    let lexbuf = Lexing.from_channel oi in
    let result = Parser.main Lexer.token lexbuf in
    Format.printf "%a" Pp.pp_prog result;
    close_in oi
  with Lexer.Lexing_error s ->
    Format.printf "Code d'erreur:\n\t%s\n\n" s

