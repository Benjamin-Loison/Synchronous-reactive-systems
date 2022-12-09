%{
  open Ast
  exception MyParsingError of string

  let current_location () = symbol_start_pos (), symbol_end_pos ()

  let defined_nodes : (ident, t_node) Hashtbl.t = Hashtbl.create 100

  let defined_vars : (ident, t_var) Hashtbl.t = Hashtbl.create 100

  let fetch_node (n: ident) =
    match Hashtbl.find_opt defined_nodes n with
    | None ->
        raise (MyParsingError
                ("The node "^n^" does not exist."))
    | Some node -> node

  let fetch_var (n: ident) : t_var =
    match Hashtbl.find_opt defined_vars n with
    | None ->
        raise (MyParsingError
                ("The var "^n^" does not exist."))
    | Some var -> var

  let type_var (v: t_var) =
      match v with
      | IVar _ -> FTBase TInt
      | BVar _ -> FTBase TBool
      | RVar _ -> FTBase TReal

  let type_exp : t_expression -> full_ty = function
    | EVar   (full_ty , _) -> full_ty
    | EMonOp (full_ty , _ , _) -> full_ty
    | EBinOp (full_ty , _ , _ , _) -> full_ty
    | ETriOp (full_ty , _ , _ , _ , _) -> full_ty
    | EComp  (full_ty , _ , _ , _) -> full_ty
    | EWhen  (full_ty , _ , _) -> full_ty
    | EConst (full_ty , _) -> full_ty
    | ETuple (full_ty , _) -> full_ty
    | EApp   (full_ty , _ , _) -> full_ty

  let concat_varlist  (t1, e1) (t2, e2) =
    (
    match t1, t2 with
    | FTList lt1, FTList lt2 -> (FTList (lt1 @ lt2), e1@e2)
    | _ ->
      raise (MyParsingError "This exception should not have been raised."))

  let make_ident (v : t_var) : t_varlist =
    match v with
    | IVar _ -> (FTList [FTBase TInt ], [v])
    | BVar _ -> (FTList [FTBase TBool], [v])
    | RVar _ -> (FTList [FTBase TReal], [v])

  let add_ident (v : t_var) (l: t_varlist) : t_varlist =
    match v, l with
    | IVar _, (FTList tl, l) -> (FTList (FTBase TInt  :: tl), v :: l)
    | BVar _, (FTList tl, l) -> (FTList (FTBase TBool :: tl), v :: l)
    | RVar _, (FTList tl, l) -> (FTList (FTBase TReal :: tl), v :: l)
    | _ -> raise (MyParsingError "This exception should not have been raised.")
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
      let (t_in, e_in) = $3 in
      let (t_out, e_out) = $7 in
      let n: Ast.t_node = 
        { n_name       = node_name;
          n_inputs     = (t_in, e_in);
          n_outputs    = (t_out, e_out);
          n_local_vars = $10;
          n_equations  = $12;
          n_type = FTArr (t_in, t_out); } in
      Hashtbl.add defined_nodes node_name n; n
    } ;

in_params:
  | /* empty */ { (FTList [], []) }
  | param_list  { $1 }
;

out_params: param_list { $1 } ;

local_params:
  | /* empty */        { (FTList [], []) }
  | VAR param_list_semicol { $2 }
;

param_list_semicol:
  | param SEMICOL { $1 }
  | param SEMICOL param_list_semicol { concat_varlist $1 $3 }

param_list:
  | param                    { $1 }
  | param SEMICOL param_list { concat_varlist $1 $3 }
;

param:
  ident_comma_list COLON TYP
    { let typ = $3 in
      let idents = $1 in
      Ast.(
      (FTList
        (List.map
          (fun t -> FTBase t) (Utils.list_repeat (List.length idents) typ)),
      match typ with
      | TBool ->
        List.map (fun s -> Hashtbl.add defined_vars s (BVar s); BVar s) idents
      | TReal ->
        List.map (fun s -> Hashtbl.add defined_vars s (RVar s); RVar s) idents
      | TInt  ->
        List.map (fun s -> Hashtbl.add defined_vars s (IVar s); IVar s) idents)) }
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
  | IDENT
    { let v = fetch_var $1 in
    Ast.(FTList [type_var v], [v])
    }
  | LPAREN ident_comma_list_patt RPAREN { $2 };

ident_comma_list_patt:
  | IDENT { make_ident (fetch_var $1) }
  | IDENT COMMA ident_comma_list_patt { add_ident (fetch_var $1) $3 }

expr:
  /* Note: EQUAL does not follow the nomenclature CMP_, ... */
  | LPAREN expr RPAREN                 { $2 }
  | IDENT                              { let v  = fetch_var $1 in EVar (type_var v, v) }
  /* Unary operators */
  | MO_not expr                        { EMonOp (type_exp $2, MOp_not, $2) }
  | MO_pre expr                        { EMonOp (type_exp $2, MOp_pre, $2) }
  | MINUS expr                         { EMonOp (type_exp $2, MOp_minus, $2) }
  | PLUS expr                          { $2 }
  /* Binary operators */
  | expr PLUS expr                     { EBinOp (type_exp $1, BOp_add, $1, $3) }
  | expr MINUS expr                    { EBinOp (type_exp $1, BOp_sub, $1, $3) }
  | expr BO_mul expr                   { EBinOp (type_exp $1, BOp_mul, $1, $3) }
  | expr BO_div expr                   { EBinOp (type_exp $1, BOp_div, $1, $3) }
  | expr BO_mod expr                   { EBinOp (type_exp $1, BOp_mod, $1, $3) }
  | expr BO_and expr                   { EBinOp (type_exp $1, BOp_and, $1, $3) }
  | expr BO_or expr                    { EBinOp (type_exp $1, BOp_or, $1, $3) }
  | expr BO_arrow expr                 { EBinOp (type_exp $1, BOp_arrow, $1, $3) }
  /* Comparison operators */
  | expr EQUAL expr                    { EComp (Ast.FTBase Ast.TBool, COp_eq, $1, $3) }
  | expr CMP_neq expr                  { EComp (Ast.FTBase Ast.TBool, COp_neq, $1, $3) }
  | expr CMP_le expr                   { EComp (Ast.FTBase Ast.TBool, COp_le, $1, $3) }
  | expr CMP_lt expr                   { EComp (Ast.FTBase Ast.TBool, COp_lt, $1, $3) }
  | expr CMP_ge expr                   { EComp (Ast.FTBase Ast.TBool, COp_ge, $1, $3) }
  | expr CMP_gt expr                   { EComp (Ast.FTBase Ast.TBool, COp_gt, $1, $3) }
  /* Tertiary operators */
  | IF expr THEN expr ELSE expr        { ETriOp (type_exp $4, TOp_if, $2, $4, $6) }
  | TO_merge expr expr expr            { ETriOp (type_exp $4, TOp_merge, $2, $3, $4) }
  /* When is neither a binop (a * 'a -> 'a) or a comp ('a * 'a -> bool) */
  | expr WHEN expr                     { EWhen (type_exp $1, $1, $3) }
  /* Constants */
  | CONST_INT                          { EConst (Ast.FTBase Ast.TInt, CInt $1) }
  | CONST_BOOL                         { EConst (Ast.FTBase Ast.TBool, CBool $1) }
  | CONST_REAL                         { EConst (Ast.FTBase Ast.TReal, CReal $1) }
  /* Tuples */
  | LPAREN expr_comma_list RPAREN      { $2 }
  /* Applications */
  | IDENT LPAREN expr_comma_list RPAREN
      { let name = $1 in
        let node = fetch_node name in
        let args = $3 in
        match node.n_type with
        | Ast.FTArr (_, t) -> EApp (t, fetch_node name, args)
        | _ -> raise (MyParsingError "This exception should not have been raised from the dead.")
         }
;

expr_comma_list:
  | expr
      { let e = $1 in
        match e with
        | ETuple _ -> e
        | _ -> ETuple (Ast.FTList [type_exp e],  [e]) }
  | expr COMMA expr_comma_list
      { let e = $1 in
        let le = $3 in
        match e, le with
        | ETuple (Ast.FTList l1, t), ETuple (Ast.FTList l2, t') -> ETuple (Ast.FTList (l1@l2), t @ t')
        | _, ETuple (Ast.FTList lt, t') -> ETuple (Ast.FTList ((type_exp e)::lt), e :: t')
        | _, _ -> raise (MyParsingError "This exception should not have been \
                                          raised.") }
;

ident_comma_list:
  | IDENT { [$1] }
  | IDENT COMMA ident_comma_list { $1 :: $3 }
;

