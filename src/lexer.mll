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
      ("int", INT);
      ("bool", BOOL);
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
  | ','             { COMMA }
  | '='             { EQUAL }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ';'             { SEMICOL }
  | ':'             { COLON }
  | eof             { EOF }
  | _               { raise (Lexing_error (Format.sprintf "Erruer à la vue de %s" (lexeme lexbuf)))}

