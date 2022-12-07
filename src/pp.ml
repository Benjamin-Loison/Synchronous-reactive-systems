open Ast

let pp_loc fmt (start, stop) =
  Lexing.(
    Format.fprintf fmt "%s: <l: %d, c: %d> -- <l: %d, c: %d>"
      start.pos_fname
      start.pos_lnum start.pos_cnum
      stop.pos_lnum stop.pos_cnum)

let pp_pattern fmt pat =
  Format.fprintf fmt "%s" pat

let pp_expression fmt expression =
  Format.fprintf fmt "%s" expression

let rec pp_equations fmt eqs =
  match eqs with
  | [] -> ()
  | eq :: eqs ->
      Format.fprintf fmt "\t\tPattern: %a\n\t\tExpression: %a\n%a"
        pp_pattern eq.peq_patt
        pp_expression eq.peq_expr
        pp_equations eqs

let rec pp_node_vars fmt vars =
  match vars with
  | [] -> ()
  | (v, t) :: vars ->
      Format.fprintf fmt "\t\tVariable name: %s\n\t\tVariable type: %s\n%a"
        v
        (match t with
        | Tbool -> "bool"
        | Tint -> "int")
        pp_node_vars vars

let pp_node fmt node =
  Format.fprintf fmt "\tNomdu nœud : %s\n\tInputs:\n%a\n\tOutputs:\n%a\n\t\
    Local variables:\n%a\n\tEquations:\n%a\n\tLocation in the parsed file: %a\n"
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


