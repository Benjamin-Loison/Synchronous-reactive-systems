{
  open Lexing
  open Ast
  open Parser        (* The type token is defined in parser.mli *)

  exception Lexing_error of string

  let id_or_keywork =
    let h = Hashtbl.create 100 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
    [ ("let", LET);
      ("tel", TEL);
      ("node", NODE);
      ("returns", RETURNS);
      ("var", VAR);
      ("int", TYP(Ast.TInt));
      ("real", TYP(Ast.TReal));
      ("bool", TYP(Ast.TBool));
      ("not", MO_not);
      ("mod", BO_mod);
      ("and", BO_and);
      ("or", BO_or);
      ("if", IF);
      ("then", THEN);
      ("else", ELSE);
      ("merge", TO_merge);
      ("when", WHEN);
      ("reset", RESET);
      ("every", EVERY);
      ("pre", MO_pre);
      ("true", CONST_BOOL(true));
      ("false", CONST_BOOL(false));
      ("fby", BO_fby);
      ("automaton", AUTOMAT);
      ("match", MATCH);
      ("with", WITH);
      ("until", UNTIL);
      ("do", DO);
      ("done", DONE);
      ];
    fun s ->
      try Hashtbl.find h s with Not_found -> IDENT s
}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = alpha (alpha | digit | '_')*

rule token = parse
    ['\n' ' ' '\t'] { token lexbuf }     (* skip blanks and newlines *)
  | ident           { id_or_keywork (lexeme lexbuf) }
  | digit+          { CONST_INT(int_of_string (lexeme lexbuf)) }
  | digit*'.'digit+ { CONST_REAL(float_of_string (lexeme lexbuf)) }
  | ','             { COMMA }
  | '='             { EQUAL }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ';'             { SEMICOL }
  | ':'             { COLON }
  | '<'             { CMP_lt }
  | "<="            { CMP_le }
  | '>'             { CMP_gt }
  | ">="            { CMP_ge }
  | "<>"            { CMP_neq }
  | '+'             { PLUS }
  | '-'             { MINUS }
  | '*'             { BO_mul }
  | '/'             { BO_div }
  | '%'             { BO_mod }
  | "->"            { BO_arrow }
  | '|'             { CASE }
  | "--"            { read_single_line_comment lexbuf }
  | eof             { EOF }
  | _               { raise (Lexing_error (Format.sprintf "Error when seeing %s" (lexeme lexbuf)))}

and read_single_line_comment = parse
  | '\n' { token lexbuf }
  | eof { EOF }
  | _ { read_single_line_comment lexbuf }
