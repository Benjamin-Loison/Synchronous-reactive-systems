exception MyTypeError of string

type location = Lexing.position * Lexing.position

type real = float

type ident = string

type base_ty =
  | TBool
  | TInt
  | TReal

type const =
  | CReal of real
  | CBool of bool
  | CInt of int

type monop =
  | MOp_not | MOp_minus | MOp_pre

type binop =
  | BOp_add | BOp_sub | BOp_mul | BOp_div | BOp_mod
  | BOp_and | BOp_or | BOp_arrow

type compop =
  | COp_eq | COp_neq
  | COp_le | COp_lt | COp_ge | COp_gt

type triop =
  | TOp_if | TOp_merge

type t_var =
  | BVar of ident
  | IVar of ident
  | RVar of ident

type t_expression =
  | EVar   of t_var
  | EMonOp of monop * t_expression
  | EBinOp of binop * t_expression * t_expression
  | ETriOp of triop * t_expression * t_expression * t_expression
  | EComp  of  compop * t_expression * t_expression
  | EWhen of t_expression * t_expression
  | EConst of const
  | ETuple of t_expression list
  | EApp   of t_node * t_expression

and t_varlist = t_var list

and t_equation = t_varlist * t_expression

and t_eqlist = t_equation list

and t_node =
  {
    n_name : ident;
    n_inputs: t_varlist;
    n_outputs: t_varlist;
    n_local_vars: t_varlist;
    n_equations: t_eqlist;
  }

type t_nodelist = t_node list


type full_ty =
  | FTArr of full_ty * full_ty
  | FTList of full_ty list
  | FTBase of base_ty

let varlist_get_type (vl: t_varlist): full_ty =
  FTList
    (List.map (function
                | BVar _ -> FTBase TBool
                | IVar _ -> FTBase TInt
                | RVar _ -> FTBase TReal) vl)


let rec expression_get_type : t_expression -> full_ty = function
  | EVar (BVar s) -> FTBase TBool
  | EVar (IVar s) -> FTBase TInt
  | EVar (RVar s) -> FTBase TReal
  | EMonOp (_, e) -> expression_get_type e
  | EBinOp (_, e1, e2) | EComp (_, e1, e2) ->
      begin
        let t1 = expression_get_type e1 in
        let t2 = expression_get_type e2 in
        if t1 = t2
          then t1
          else raise (MyTypeError "A binary operator only works on pairs of \
            expressions of the same type.")
      end
  | ETriOp (_, e1, e2, e3) ->
      begin
        let t1 = expression_get_type e1 in
        let t2 = expression_get_type e2 in
        let t3 = expression_get_type e3 in
        if t1 = FTBase TBool && t2 = t3
          then t2
          else raise (MyTypeError "A tertiary operator only works when its \
            first argument is a boolean expressions, and its other expressions \
            have the same type.")
      end
  | EWhen (e1, e2) ->
      begin
        let t1 = expression_get_type e1 in
        let t2 = expression_get_type e2 in
        if t2 = FTBase TBool
          then t1
          else raise (MyTypeError "The [when] keywork can only be used if its \
            second argument is a boolean expression")
      end
  | EConst (CInt _) -> FTBase TInt
  | EConst (CReal _) -> FTBase TReal
  | EConst (CBool _) -> FTBase TBool
  | ETuple l ->
      begin
        FTList (
          List.fold_left (fun acc (expr: t_expression) -> 
            let t = expression_get_type expr in
            match t with
            | FTList lt -> lt @ acc
            | _ -> t :: acc) [] l)
      end
  | EApp (n, e) ->
      begin
        let tn = node_get_type n in
        let te = expression_get_type e in
        match tn with
        | FTArr (targs, tout) ->
            if te = targs
              then tout
              else raise (MyTypeError "When applying another node [n], the \
                the type of your arguments should match the type of the inputs \
                of [n].")
        | _ -> raise (MyTypeError "You cannot apply something that is not a \
                        node, it does not make sense.")
      end
and node_get_type n =
  FTArr (varlist_get_type n.n_inputs, varlist_get_type n.n_outputs)

