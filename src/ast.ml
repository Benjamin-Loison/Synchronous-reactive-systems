type ident = string

type location = Lexing.position * Lexing.position

type base_ty =
  | Tbool
  | Tint

type p_pattern = string
and p_expression = string

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

