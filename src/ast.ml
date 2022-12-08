type location = Lexing.position * Lexing.position

type ident = string

type real = float

type _ const =
  | CReal: real -> real const
  | CBool: bool -> bool const
  | CInt:  int  -> int const

type monop =
  | MOp_not | MOp_minus | MOp_pre

type binop =
  | BOp_add | BOp_sub | BOp_mul | BOp_div | BOp_mod
  | BOp_and | BOp_or | BOp_when

type compop =
  | BOp_eq | BOp_neq
  | BOp_le | BOp_lt | BOp_ge | BOp_gt

type triop =
  | TOp_if | TOp_merge

type _ t_var =
  | BVar: ident -> bool t_var
  | IVar: ident -> int t_var
  | RVar: ident -> real t_var

type _ t_expression =
  | EVar: 'a t_var -> 'a t_expression
  | EMonOp: monop * 'a t_expression -> 'a t_expression
  | EBinOp: binop * 'a t_expression * 'a t_expression -> 'a t_expression
  | ETriOp: triop * bool t_expression * 'a t_expression * 'a t_expression -> 'a t_expression
  | EComp:  compop * 'a t_expression * 'a t_expression -> bool t_expression
  | EConst: 'a const -> 'a t_expression
  | ETuple: 'a t_expression * 'b t_expression -> ('a * 'b) t_expression
  | EApp: (('a -> 'b) t_node) * 'a t_expression -> 'b t_expression

and _ t_varlist =
  | NVar: 'a t_varlist
  | CVar: 'a t_var * 'b t_varlist -> ('a * 'b) t_varlist

and 'a t_equation = 'a t_varlist * 'a t_expression

and _ t_eqlist =
  | NEql: unit t_eqlist
  | CEql: 'a t_equation * 'b t_eqlist -> ('a * 'b) t_eqlist

and _ t_node =
  | MakeNode:
    ident
    * 'i t_varlist * 'o t_varlist
    * 'l t_varlist * 'e t_eqlist
    -> ('i -> 'o) t_node

type _ t_nodelist =
  | NNode: unit t_nodelist
  | CNode: ('a -> 'b) t_node * 'c t_nodelist -> (('a -> 'b) * 'c) t_nodelist

type base_ty =
  | TBool
  | TInt
  | TReal
