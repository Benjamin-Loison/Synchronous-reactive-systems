%{
  let current_location () = symbol_start_pos (), symbol_end_pos ()
%}

%token EOF
%token<string> IDENT
%token LPAREN
%token RPAREN
%token RETURNS
%token SEMICOL
%token COLON
%token BOOL
%token INT
%token LET
%token TEL
%token NODE
%token VAR
%token EQUAL
%token COMMA

/* The Entry Point */
%start main
%type <Ast.p_prog> main

%%

main: nodes EOF { $1 };

nodes:
  | /* empty */ { [] }
  | node nodes  { $1 :: $2 };

node:
  NODE IDENT LPAREN in_params RPAREN
  RETURNS LPAREN out_params RPAREN SEMICOL
  local_params
  LET equations TEL
    { { pn_name       = $2;
        pn_input      = $4;
        pn_output     = $8;
        pn_local_vars = $11;
        pn_equations  = $13;
        pn_loc        = current_location (); }
    } ;

in_params:
  | /* empty */ { [] }
  | param_list  { $1 }
  ;

out_params: param_list { $1 } ;

local_params:
  | /* empty */        { [] }
  | VAR param_list_semicol { $2 }
;

param_list_semicol:
  | param SEMICOL { $1 }
  | param SEMICOL param_list_semicol { $1 @ $3 }

param_list:
  | param                    { $1 }
  | param SEMICOL param_list { $1 @ $3 }
;

param:
  ident_comma_list COLON typ
    { let typ = $3 in List.map (fun i -> (i, typ)) $1 }
;

equations:
  | /* empty */ { [] }
  | equation SEMICOL equations
      { $1 :: $3 }
;

equation:
  pattern EQUAL expr
    { { peq_patt = $1; peq_expr = $3; } }
;

pattern: IDENT { $1 };
expr: IDENT { $1 };

typ:
  | BOOL { Tbool }
  | INT  { Tint }
;

ident_comma_list:
  | IDENT { [$1] }
  | IDENT COMMA ident_comma_list { $1 :: $3 }
;

