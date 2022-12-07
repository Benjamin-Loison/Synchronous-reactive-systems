type ident = string

type location = Lexing.position * Lexing.position

type const =
  | CBool of bool
  | CInt of int

type monop =
  | MOp_not
  | MOp_minus

type binop =
  | BOp_add | BOp_sub | BOp_mul | BOp_div | BOp_mod
  | BOp_and | BOp_or | BOp_eq | BOp_neq
  | BOp_le | BOp_lt | BOp_ge | BOp_gt

type triop =
  | TOp_if

type base_ty =
  | Tbool
  | Tint

type p_pattern =
  | PP_var of ident
  | PP_tuple of ident list

type p_expression =
  | PE_Const of const
  | PE_Var of ident
  | PE_MonOp of monop * p_expression
  | PE_BinOp of binop * p_expression * p_expression
  | PE_TriOp of triop * p_expression * p_expression * p_expression
  | PE_app of ident * p_expression list
  | PE_tuple of p_expression list
  | PE_pre of p_expression
  | PE_arrow of p_expression * p_expression

type p_equation =
  { peq_patt: p_pattern;
    peq_expr: p_expression }

type p_node =
  { pn_name:       ident;
    pn_input:      (ident * base_ty) list;
    pn_output:     (ident * base_ty) list;
    pn_local_vars: (ident* base_ty) list;
    pn_equations:  p_equation list;
    pn_loc:        location; }

type p_prog = p_node list

