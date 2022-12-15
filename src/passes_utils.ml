open Ast

(** [node_pass] is an auxiliary function used to write passes: it will iterate
  * the function passed as argument on all the nodes of the program *)
let node_pass f ast: t_nodelist option =
  Utils.list_map_option f ast

(** [equation_pass] is an auxiliary function used to write passes: it will
  * iterate the function passed as argument on all the equations of the
  * program *)
let equation_pass (f: t_equation -> t_equation option) ast: t_nodelist option =
  let aux (node: t_node): t_node option =
    match Utils.list_map_option f node.n_equations with
    | None -> None
    | Some eqs -> Some {n_name         = node.n_name;
                        n_inputs       = node.n_inputs;
                        n_outputs      = node.n_outputs;
                        n_local_vars   = node.n_local_vars;
                        n_equations    = eqs;
                        n_automata     = node.n_automata;
                        n_inputs_type  = node.n_inputs_type;
                        n_outputs_type = node.n_outputs_type;
                       }
    in
  node_pass aux ast

let expression_pass f: t_nodelist -> t_nodelist option =
  let aux (patt, expr) =
    match f expr with
    | None -> None
    | Some expr -> Some (patt, expr)
  in
  equation_pass aux
