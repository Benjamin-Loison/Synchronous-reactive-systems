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
%token PRE
%token ARROW

%token MO_not
%token BO_le
%token BO_lt
%token BO_ge
%token BO_gt
%token BO_mod
%token BO_and
%token BO_or
%token BO_mul
%token BO_neq
%token BO_div

%token PLUS
%token MINUS

%token IF
%token THEN
%token ELSE

%token<int> CONST_INT
%token<bool> CONST_BOOL

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

pattern:
  | IDENT                           { PP_var ($1) }
  | LPAREN IDENT COMMA indent_comma_list RPAREN { PP_tuple ($2 :: $4) };

indent_comma_list:
  | IDENT { [$1] }
  | IDENT COMMA indent_comma_list { $1 :: $3 }

expr:
  /* Note: PLUS, MINUS and EQUAL do not follow the nomenclature BO_ MO_, ... */
  | LPAREN expr RPAREN                 { $2 }
  | IDENT                              { PE_Var $1 }
  | MO_not expr                        { PE_MonOp(MOp_not, $2) }
  | PLUS expr                          { $2 } /* +e = e for all e integer expression. */
  | MINUS expr                         { PE_MonOp(MOp_minus, $2) }
  | expr PLUS expr                     { PE_BinOp(BOp_add, $1, $3) }
  | expr MINUS expr                    { PE_BinOp(BOp_sub, $1, $3) }
  | expr BO_mul expr                   { PE_BinOp(BOp_mul, $1, $3) }
  | expr BO_div expr                   { PE_BinOp(BOp_div, $1, $3) }
  | expr BO_mod expr                   { PE_BinOp(BOp_mod, $1, $3) }
  | expr BO_and expr                   { PE_BinOp(BOp_and, $1, $3) }
  | expr BO_or expr                    { PE_BinOp(BOp_or, $1, $3) }
  | expr EQUAL expr                    { PE_BinOp(BOp_eq, $1, $3) }
  | expr BO_neq expr                   { PE_BinOp(BOp_neq, $1, $3) }
  | expr BO_le expr                    { PE_BinOp(BOp_le, $1, $3) }
  | expr BO_lt expr                    { PE_BinOp(BOp_lt, $1, $3) }
  | expr BO_ge expr                    { PE_BinOp(BOp_ge, $1, $3) }
  | expr BO_gt expr                    { PE_BinOp(BOp_gt, $1, $3) }
  | IF expr THEN expr ELSE expr        { PE_TriOp(TOp_if, $2, $4, $6) }
  | IDENT LPAREN expr_comma_list RPAREN{ PE_app ($1, $3) }
  | LPAREN expr_comma_list RPAREN      { PE_tuple($2) }
  | CONST_INT                          { PE_Const(CInt $1 ) }
  | CONST_BOOL                         { PE_Const(CBool $1 ) }
  | PRE expr                           { PE_pre $2 }
  | expr ARROW expr                    { PE_arrow ($1, $3) }
;

expr_comma_list:
  | expr                       { [$1] }
  | expr COMMA expr_comma_list { $1 :: $3 }

typ:
  | BOOL { Tbool }
  | INT  { Tint }
;

ident_comma_list:
  | IDENT { [$1] }
  | IDENT COMMA ident_comma_list { $1 :: $3 }
;

