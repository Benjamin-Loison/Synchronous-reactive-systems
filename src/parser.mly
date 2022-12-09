%{
  open Ast
  open Utils

  let current_location () = symbol_start_pos (), symbol_end_pos ()

  let defined_nodes : (ident, t_node) Hashtbl.t = Hashtbl.create 100

  let defined_vars : (ident, t_var) Hashtbl.t = Hashtbl.create 100

  let fetch_node (n: ident) =
    match Hashtbl.find_opt defined_nodes n with
    | None ->
        raise (MyParsingError
                ("The node "^n^" does not exist.", current_location()))
    | Some node -> node

  let fetch_var (n: ident) : t_var =
    match Hashtbl.find_opt defined_vars n with
    | None ->
        raise (MyParsingError
                ("The var "^n^" does not exist.", current_location()))
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
      raise (MyParsingError ("This exception should not have been raised.",
              current_location())))

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
    | _ -> raise (MyParsingError ("This exception should not have been raised.",
                  current_location()))

  let monop_condition expr typ_constraint error_msg res =
    if type_exp expr = typ_constraint
      then res
      else raise (MyParsingError (error_msg, current_location()))

  let monop_neg_condition expr typ_constraint error_msg res =
    if type_exp expr <> typ_constraint
      then res
      else raise (MyParsingError (error_msg, current_location()))

  let make_binop_nonbool e1 e2 op error_msg =
    let t1 = type_exp e1 in let t2 = type_exp e2 in
    match t1 with
    | FTBase _ -> (** e1 and e2 should be nunmbers here.*)
      if t1 = t2 && t1 <> FTBase TBool
        then EBinOp (t1, op, e1, e2)
        else raise (MyParsingError (error_msg, current_location()))
    | _ -> raise (MyParsingError (error_msg, current_location()))

  let make_binop_bool e1 e2 op error_msg =
    let t1 = type_exp e1 in let t2 = type_exp e2 in
    if t1 = t2 && t1 = FTBase TBool
      then EBinOp (t1, op, e1, e2)
      else raise (MyParsingError (error_msg, current_location()))

  let make_comp e1 e2 op error_msg =
    let t1 = type_exp e1 in let t2 = type_exp e2 in
    if t1 = t2
      then EComp (FTBase TBool, op, e1, e2)
      else raise (MyParsingError (error_msg, current_location()))

  let make_comp_nonbool e1 e2 op error_msg =
    let t1 = type_exp e1 in let t2 = type_exp e2 in
    match t1 with
    | FTBase _ -> (** e1 and e2 should be numbers here. *)
      if t1 = t2 && t1 <> FTBase TBool
        then EComp (FTBase TBool, op, e1, e2)
        else raise (MyParsingError (error_msg, current_location()))
    | _ -> raise (MyParsingError (error_msg, current_location()))

  let make_tertiary e1 e2 e3 op error_msg =
    let t1 = type_exp e1 in let t2 = type_exp e2 in let t3 = type_exp e3 in
    if t2 = t3 && t1 = FTBase TBool
      then ETriOp (t2, op, e1, e2, e3)
      else raise (MyParsingError (error_msg, current_location()))

  let rec debug_type_pp fmt = function
  | FTBase TBool   -> Format.fprintf fmt "bool"
  | FTBase TReal   -> Format.fprintf fmt "real"
  | FTBase TInt    -> Format.fprintf fmt "int"
  | FTArr (t1, t2) -> Format.fprintf fmt "( %a -> %a )"
                        debug_type_pp t1 debug_type_pp t2
  | FTList []      -> ()
  | FTList (h :: []) -> Format.fprintf fmt "l%a" debug_type_pp h
  | FTList (h :: h' :: t) ->
      Format.fprintf fmt "l%a; %a" debug_type_pp h debug_type_pp (FTList (h' :: t))

  let debug_type =
    Format.printf "Type: %a\n" debug_type_pp

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
%token REAL
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
%token BO_fby
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
  NODE node_content
    { (* Flush known variables *) Hashtbl.clear defined_vars; $2 }

node_content:
  IDENT LPAREN in_params RPAREN
  RETURNS LPAREN out_params RPAREN SEMICOL
  local_params
  LET equations TEL
    { let node_name = $1 in
      let (t_in, e_in) = $3 in
      let (t_out, e_out) = $7 in
      let n: t_node = 
        { n_name       = node_name;
          n_inputs     = (t_in, e_in);
          n_outputs    = (t_out, e_out);
          n_local_vars = $10;
          n_equations  = $12;
          n_type = FTArr (t_in, t_out); } in
      Hashtbl.add defined_nodes node_name n; n };

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
      (
      (FTList
        (List.map
          (fun t -> FTBase t) (list_repeat (List.length idents) typ)),
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
    { let (t_patt, patt) = $1 in
      let expr = $3 in let texpr = type_exp expr in
      if (match texpr with
      | FTList _ -> texpr = t_patt
      | _        -> FTList [texpr] = t_patt)
        then ((t_patt, patt), expr)
        else (debug_type t_patt; debug_type (type_exp expr);
          raise (MyParsingError ("The equation does not type check!",
                    current_location()))) };

pattern:
  | IDENT
    { let v = fetch_var $1 in
    (FTList [type_var v], [v])
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
  | MO_not expr
      { monop_condition $2 (FTBase TBool)
          "You cannot negate a non-boolean expression."
          (EMonOp (type_exp $2, MOp_not, $2)) }
  | MO_pre expr                        { EMonOp (type_exp $2, MOp_pre, $2) }
  | MINUS expr
      { monop_neg_condition $2 (FTBase TBool)
          "You cannot take the opposite of a boolean expression."
          (EMonOp (type_exp $2, MOp_minus, $2)) }
  | PLUS expr
      { monop_neg_condition $2 (FTBase TBool)
          "You cannot take the plus of a boolean expression." $2 }
  /* Binary operators */
  | expr PLUS expr
      { make_binop_nonbool $1 $3 BOp_add
          "You should know better; addition hates booleans" }
  | expr MINUS expr
      { make_binop_nonbool $1 $3 BOp_sub
          "You should know better; subtraction hates booleans" }
  | expr BO_mul expr
      { make_binop_nonbool $1 $3 BOp_mul
          "You should know better; multiplication hates booleans" }
  | expr BO_div expr
      { make_binop_nonbool $1 $3 BOp_div
          "You should know better; division hates booleans" }
  | expr BO_mod expr
      { make_binop_nonbool $1 $3 BOp_mod
          "You should know better; modulo hates booleans" }
  | expr BO_and expr
      { make_binop_bool $1 $3 BOp_and
          "You should know better; conjunction hates numbers" }
  | expr BO_or expr
      { make_binop_bool $1 $3 BOp_or
          "You should know better; disjunction hates numbers" }
  | expr BO_arrow expr
      { let e1 = $1 in let t1 = type_exp e1 in
        let e2 = $3 in let t2 = type_exp e2 in
        if t1 = t2
          then EBinOp (type_exp $1, BOp_arrow, $1, $3)
          else raise (MyParsingError ("The -> does not type-check",
                      current_location())) }
  /* Binary operators, syntactic sugar */
  | expr BO_fby expr
      { (* e fby e' ==> e -> (pre e') *)
        let e1 = $1 in let t1 = type_exp e1 in
        let e2 = $3 in let t2 = type_exp e2 in
        if t1 = t2
          then EBinOp (t1, BOp_arrow, e1, (EMonOp (t1, MOp_pre, e2)))
          else raise (MyParsingError ("The fby does not type-check!",
                      current_location())) }
  /* Comparison operators */
  | expr EQUAL expr
      { make_comp $1 $3 COp_eq "The equality does not type-check!" }
  | expr CMP_neq expr
      { make_comp $1 $3 COp_neq "The inquality does not type-check!" }
  | expr CMP_le expr
      { make_comp_nonbool $1 $3 COp_le "The comparison <= does not type-check!" }
  | expr CMP_lt expr
      { make_comp_nonbool $1 $3 COp_lt "The comparison < does not type-check!" }
  | expr CMP_ge expr
      { make_comp_nonbool $1 $3 COp_ge "The comparison >= does not type-check!" }
  | expr CMP_gt expr
      { make_comp_nonbool $1 $3 COp_gt "The comparison > does not type-check!" }
  /* Tertiary operators */
  | IF expr THEN expr ELSE expr
      { make_tertiary $2 $4 $6 TOp_if "The if-then-else does not type-check!" }
  | TO_merge expr expr expr
      { make_tertiary $2 $3 $4 TOp_merge "The merge does not type-check!" }
  /* When is neither a binop (a * 'a -> 'a) or a comp ('a * 'a -> bool) */
  | expr WHEN expr
      { let e1 = $1 in let t1 = type_exp e1 in
        let e2 = $3 in let t2 = type_exp e2 in
        if t2 = FTBase TBool
         then EWhen (type_exp $1, $1, $3)
         else raise (MyParsingError ("The when does not type-check!",
                    current_location())) }
  /* Constants */
  | CONST_INT                          { EConst (FTBase TInt, CInt $1) }
  | CONST_BOOL                         { EConst (FTBase TBool, CBool $1) }
  | CONST_REAL                         { EConst (FTBase TReal, CReal $1) }
  /* Tuples */
  | LPAREN expr_comma_list RPAREN      { $2 }
  /* Applications */
  | IDENT LPAREN expr_comma_list RPAREN
      { let name = $1 in
        let node = fetch_node name in
        let args = $3 in
        match node.n_type with
        | FTArr (tin, t) ->
            if tin = type_exp args
              then EApp (t, fetch_node name, args)
              else raise (MyParsingError ("The application does not type check!",
                          current_location()))
        | _ -> raise (MyParsingError ("This exception should not have been \
                      raised from the dead.",
                      current_location()))
         }
;

expr_comma_list:
  | expr
      { let e = $1 in
        match e with
        | ETuple _ -> e
        | _ -> ETuple (FTList [type_exp e],  [e]) }
  | expr COMMA expr_comma_list
      { let e = $1 in
        let le = $3 in
        match e, le with
        | ETuple (FTList l1, t), ETuple (FTList l2, t') -> ETuple (FTList (l1@l2), t @ t')
        | _, ETuple (FTList lt, t') -> ETuple (FTList ((type_exp e)::lt), e :: t')
        | _, _ -> raise (MyParsingError ("This exception should not have been \
                                          raised.",
                                          current_location())) }
;

ident_comma_list:
  | IDENT { [$1] }
  | IDENT COMMA ident_comma_list { $1 :: $3 }
;


