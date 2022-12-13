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

type full_ty = base_ty list

type t_expression =
  | EVar   of full_ty * t_var
  | EMonOp of full_ty * monop * t_expression
  | EBinOp of full_ty * binop * t_expression * t_expression
  | ETriOp of full_ty * triop * t_expression * t_expression * t_expression
  | EComp  of full_ty * compop * t_expression * t_expression
  | EWhen  of full_ty * t_expression * t_expression
  | EReset of full_ty * t_expression * t_expression
  | EConst of full_ty * const
  | ETuple of full_ty * (t_expression list)
  | EApp   of full_ty * t_node * t_expression
  | EAuto  of full_ty * t_state * t_state list (* initial state and transitions *)

and t_varlist = full_ty * (t_var list)

and t_equation = t_varlist * t_expression

and t_eqlist = t_equation list

and t_state = | State of ident * t_eqlist * t_expression * ident

and t_node =
  {
    n_name : ident;
    n_inputs: t_varlist;
    n_outputs: t_varlist;
    n_local_vars: t_varlist;
    n_equations: t_eqlist;
    n_inputs_type : full_ty;
    n_outputs_type : full_ty;
  }

type t_nodelist = t_node list

