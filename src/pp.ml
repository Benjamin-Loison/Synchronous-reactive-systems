open Ast

let pp_ident fmt (s: ident): unit = Format.fprintf fmt "%s" s

let pp_ast fmt (nodes: t_nodelist) = ()

(*open Ast

let pp_loc fmt (start, stop) =
  Lexing.(
    Format.fprintf fmt "%s: <l: %d, c: %d> -- <l: %d, c: %d>"
      start.pos_fname
      start.pos_lnum start.pos_cnum
      stop.pos_lnum stop.pos_cnum)

let pp_pattern fmt pat =
  let rec pp_pattern_aux fmt l =
    match l with
    | [] -> ()
    | h :: [] -> Format.fprintf fmt  "%s" h
    | h :: h' :: l -> Format.fprintf fmt  "%s, %a" h pp_pattern_aux (h' :: l)
    in
  match pat with
  | PP_var v -> Format.fprintf fmt "variable %s" v
  | PP_tuple l -> Format.fprintf fmt "tuple ( %a )" pp_pattern_aux l

let pp_expression =
  let upd_prefix s = s ^ "    " in
  let rec pp_expression_aux prefix fmt expression =
    let rec pp_expression_list prefix fmt exprs =
      match exprs with
      | [] -> ()
      | expr :: exprs ->
          Format.fprintf fmt "%a%a"
            (pp_expression_aux (prefix^" |> ")) expr
            (pp_expression_list prefix) exprs
    in
    match expression with
    | PE_Const c ->
        begin match c with
        | CBool true ->  Format.fprintf fmt "\t\t\t%s<true : bool>\n" prefix
        | CBool false ->  Format.fprintf fmt "\t\t\t%s<false : bool>\n" prefix
        | CInt i ->      Format.fprintf fmt "\t\t\t%s<%5d: int>\n" prefix i
        end
    | PE_Var v -> Format.fprintf fmt "\t\t\t%s<var %s>\n" prefix v
    | PE_MonOp (mop, arg) ->
        begin match mop with
        | MOp_not ->
            Format.fprintf fmt "\t\t\t%s¬\n%a" prefix
              (pp_expression_aux (upd_prefix prefix)) arg
        | MOp_minus ->
            Format.fprintf fmt "\t\t\t%s—\n%a" prefix
              (pp_expression_aux (upd_prefix prefix)) arg
        end
    | PE_BinOp (bop, arg, arg') ->
        begin
        let s = match bop with
        | BOp_add -> " + " | BOp_sub -> " - "
        | BOp_mul -> " ∗ " | BOp_div -> " / " | BOp_mod -> "%  "
        | BOp_and -> "&& " | BOp_or  -> "|| " | BOp_eq  -> "== "
        | BOp_neq -> " ≠ "
        | BOp_le  -> " ≤ " | BOp_lt  -> " < "
        | BOp_ge  -> " ≥ " | BOp_gt  -> " > " in
        Format.fprintf fmt "\t\t\t%s%s\n%a%a" prefix s 
          (pp_expression_aux (upd_prefix prefix)) arg
          (pp_expression_aux (upd_prefix prefix)) arg'
        end
    | PE_TriOp (top, arg, arg', arg'') ->
        begin match top with
        | TOp_if ->
            Format.fprintf fmt "\t\t\t%sIF\n%a\t\t\tTHEN\n%a\t\t\tELSE\n%a"
              prefix
              (pp_expression_aux (upd_prefix prefix)) arg
              (pp_expression_aux (upd_prefix prefix)) arg'
              (pp_expression_aux (upd_prefix prefix)) arg''
        end
    | PE_app (f, args)  ->
        Format.fprintf fmt "\t\t\t%sApp %s\n%a"
          prefix f
          (pp_expression_list prefix) args
    | PE_tuple args ->
        Format.fprintf fmt "\t\t\t%sTuple\n%a" prefix
          (pp_expression_list prefix) args;
    | PE_pre expr ->
        Format.fprintf fmt "\t\t\t%spre\n%a" prefix
          (pp_expression_aux (upd_prefix prefix)) expr
    | PE_arrow (expr, expr') ->
        Format.fprintf fmt "%a%a"
          (pp_expression_aux (upd_prefix prefix)) expr
          (pp_expression_aux (prefix^" -> ")) expr'
    in
  pp_expression_aux ""

let rec pp_equations fmt eqs =
  match eqs with
  | [] -> ()
  | eq :: eqs ->
      Format.fprintf fmt "\t\t∗ left side: %a\n\t\t  right side:\n%a\n%a"
        pp_pattern eq.peq_patt
        pp_expression eq.peq_expr
        pp_equations eqs

let rec pp_node_vars fmt vars =
  match vars with
  | [] -> ()
  | (v, t) :: vars ->
      Format.fprintf fmt "\t\tVariable <name: %10s,\ttype: %s>\n%a"
        v
        (match t with
        | Tbool -> "bool"
        | Tint -> "int")
        pp_node_vars vars

let pp_node fmt node =
  Format.fprintf fmt "\t∗ Nom du nœud : %s\n\t  Inputs:\n%a\n\t  Outputs:\n%a\n\t\
    \ \ Local variables:\n%a\n\t  Equations:\n%a\n\t  Location in the parsed file: %a\n"
                 node.pn_name
    pp_node_vars node.pn_input
    pp_node_vars node.pn_output
    pp_node_vars node.pn_local_vars
    pp_equations node.pn_equations
    pp_loc       node.pn_loc

let rec pp_nodes fmt nodes =
  match nodes with
  | [] -> ()
  | node :: nodes ->
    Format.fprintf fmt "%a\n%a" pp_node node pp_nodes nodes

let pp_prog fmt prog =
  Format.fprintf fmt
    "Le programme est composé de %d nœud(s), listés ci-dessous :\n%a"
    (List.length prog)
    pp_nodes prog

*)
