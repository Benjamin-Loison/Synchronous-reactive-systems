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
      ("<=", BO_le);
      (">=", BO_ge);
      ("not", MO_not);
      ("mod", BO_mod);
      ("&&", BO_and);
      ("and", BO_and);
      ("||", BO_or);
      ("or", BO_or);
      ("<>", BO_neq);
      ("if", IF);
      ("then", THEN);
      ("else", ELSE);
      ("≤", BO_le);
      ("≥", BO_ge );
      ("¬", MO_not);
      ("pre", PRE);
      ("true", CONST_BOOL(true));
      ("false", CONST_BOOL(false));
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
  | ','             { COMMA }
  | '='             { EQUAL }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ';'             { SEMICOL }
  | ':'             { COLON }
  | '<'             { BO_lt }
  | '>'             { BO_gt }
  | '+'             { PLUS }
  | '-'             { MINUS }
  | '*'             { BO_mul }
  | '/'             { BO_div }
  | '%'             { BO_mod }
  | "->"            { ARROW }
  | eof             { EOF }
  | _               { raise (Lexing_error (Format.sprintf "Erruer à la vue de %s" (lexeme lexbuf)))}

