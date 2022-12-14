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

exception PassExn of string

let counter = ref 0
let create_automaton_id : unit -> int = fun () ->
    counter := !counter + 1;
    !counter

let create_automaton_name id = 
    Format.asprintf "_s%d" (id)
