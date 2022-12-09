%{
  exception MyParsingError of string

  let current_location () = symbol_start_pos (), symbol_end_pos ()

  let defined_nodes : (Ast.ident, Ast.t_node) Hashtbl.t = Hashtbl.create 100

  let defined_vars : (Ast.ident, Ast.t_var) Hashtbl.t = Hashtbl.create 100

  let fetch_node (n: Ast.ident) =
    match Hashtbl.find_opt defined_nodes n with
    | None ->
        raise (MyParsingError
                ("The node "^n^" does not exist."))
    | Some node -> node

  let fetch_var (n: Ast.ident) =
    match Hashtbl.find_opt defined_vars n with
    | None ->
        raise (MyParsingError
                ("The var "^n^" does not exist."))
    | Some var -> var

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
%token<Ast.base_ty> TYP

%token MO_not
%token MO_pre
%token PLUS
%token MINUS
%token BO_and
%token BO_or
%token BO_mul
%token BO_div
%token BO_mod
%token BO_arrow
%token CMP_le
%token CMP_lt
%token CMP_ge
%token CMP_gt
%token CMP_neq
%token TO_merge

%token WHEN

%token IF
%token THEN
%token ELSE

%token<int> CONST_INT
%token<bool> CONST_BOOL
%token<Ast.real> CONST_REAL

/* The Entry Point */
%start main
%type <Ast.t_nodelist> main

%%

main: nodes EOF { $1 };

nodes:
  | /* empty */ { [] }
  | node nodes  { $1 :: $2 };

node:
  NODE node_content { (* Flush known variables *) Hashtbl.clear defined_vars; $2 }

node_content:
  IDENT LPAREN in_params RPAREN
  RETURNS LPAREN out_params RPAREN SEMICOL
  local_params
  LET equations TEL
    { let node_name = $1 in
      let n: Ast.t_node = 
        { n_name       = node_name;
          n_inputs     = $3;
          n_outputs    = $7;
          n_local_vars = $10;
          n_equations  = $12; } in
      Hashtbl.add defined_nodes node_name n; n
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
  ident_comma_list COLON TYP
    { let typ = $3 in
      let idents = $1 in
      Ast.(
      match typ with
      | TBool ->
          List.map (fun s -> Hashtbl.add defined_vars s (BVar s); BVar s) idents
      | TReal ->
          List.map (fun s -> Hashtbl.add defined_vars s (RVar s); RVar s) idents
      | TInt  ->
          List.map (fun s -> Hashtbl.add defined_vars s (IVar s); IVar s) idents) }
;

ident_comma_list:
  | IDENT { [$1] }
  | IDENT COMMA ident_comma_list { $1 :: $3 }

equations:
  | /* empty */ { [] }
  | equation SEMICOL equations
      {  $1 :: $3 }
;

equation:
  pattern EQUAL expr
    { ($1, $3) }
;

pattern:
  | IDENT                           { [fetch_var $1] }
  | LPAREN ident_comma_list_patt RPAREN { $2 };

ident_comma_list_patt:
  | IDENT { [fetch_var $1] }
  | IDENT COMMA ident_comma_list_patt { (fetch_var $1) :: $3 }

expr:
  /* Note: EQUAL does not follow the nomenclature CMP_, ... */
  | LPAREN expr RPAREN                 { $2 }
  | IDENT                              { EVar (fetch_var $1) }
  /* Unary operators */
  | MO_not expr                        { EMonOp (MOp_not, $2) }
  | MO_pre expr                        { EMonOp (MOp_pre, $2) }
  | MINUS expr                         { EMonOp (MOp_minus, $2) }
  | PLUS expr                          { $2 }
  /* Binary operators */
  | expr PLUS expr                     { EBinOp (BOp_add, $1, $3) }
  | expr MINUS expr                    { EBinOp (BOp_sub, $1, $3) }
  | expr BO_mul expr                   { EBinOp (BOp_mul, $1, $3) }
  | expr BO_div expr                   { EBinOp (BOp_div, $1, $3) }
  | expr BO_mod expr                   { EBinOp (BOp_mod, $1, $3) }
  | expr BO_and expr                   { EBinOp (BOp_and, $1, $3) }
  | expr BO_or expr                    { EBinOp (BOp_or, $1, $3) }
  | expr BO_arrow expr                 { EBinOp (BOp_arrow, $1, $3) }
  /* Comparison operators */
  | expr EQUAL expr                    { EComp (COp_eq, $1, $3) }
  | expr CMP_neq expr                  { EComp (COp_neq, $1, $3) }
  | expr CMP_le expr                   { EComp (COp_le, $1, $3) }
  | expr CMP_lt expr                   { EComp (COp_lt, $1, $3) }
  | expr CMP_ge expr                   { EComp (COp_ge, $1, $3) }
  | expr CMP_gt expr                   { EComp (COp_gt, $1, $3) }
  /* Tertiary operators */
  | IF expr THEN expr ELSE expr        { ETriOp (TOp_if, $2, $4, $6) }
  | TO_merge expr expr expr            { ETriOp (TOp_merge, $2, $3, $4) }
  /* When is neither a binop (a * 'a -> 'a) or a comp ('a * 'a -> bool) */
  | WHEN expr expr                     { EWhen ($2, $3) }
  /* Constants */
  | CONST_INT                          { EConst (CInt $1) }
  | CONST_BOOL                         { EConst (CBool $1) }
  | CONST_REAL                         { EConst (CReal $1) }
  /* Tuples */
  | LPAREN expr_comma_list RPAREN      { $2 }
  /* Applications */
  | IDENT LPAREN expr_comma_list RPAREN
      { let name = $1 in
        let args = $3 in
        EApp (fetch_node name, args) }
;

expr_comma_list:
  | expr
      { let e = $1 in
        match e with
        | ETuple _ -> e
        | _ -> ETuple [e] }
  | expr COMMA expr_comma_list
      { let e = $1 in
        let le = $3 in
        match e, le with
        | ETuple t, ETuple t' -> ETuple (t @ t')
        | _, ETuple t' -> ETuple (e :: t')
        | _, _ -> raise (MyParsingError "This exception should not have been \
                                          raised.") }
;

ident_comma_list:
  | IDENT { [$1] }
  | IDENT COMMA ident_comma_list { $1 :: $3 }
;

