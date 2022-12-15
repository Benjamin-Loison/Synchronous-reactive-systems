open Ast

type sim_var =
  | SIVar of ident * (int option)
  | SBVar of ident * (bool option)
  | SRVar of ident * (real option)

type sim_node_st =
  {
    node_outputs: sim_var list;
    node_loc_vars: sim_var list;
    node_inner_nodes: sim_node list;
  }
and sim_node_step_fn =
  sim_node_st -> sim_var list -> (sim_var list * sim_node_st)
and sim_node = sim_node_st * sim_node_step_fn

let pp_sim fmt ((sn, _): sim_node) =
  let rec aux fmt vars =
    match vars with
    | [] -> ()
    | SIVar (s, None) :: t ->
        Format.fprintf fmt "\t<%s : int> uninitialized yet.\n%a" s aux t
    | SBVar (s, None) :: t ->
        Format.fprintf fmt "\t<%s : bool> uninitialized yet.\n%a" s aux t
    | SRVar (s, None) :: t ->
        Format.fprintf fmt "\t<%s : real> uninitialized yet.\n%a" s aux t
    | SIVar (s, Some i) :: t ->
        Format.fprintf fmt "\t<%s : real> = %d\n%a" s i aux t
    | SBVar (s, Some b) :: t ->
        Format.fprintf fmt "\t<%s : real> = %s\n%a" s (Bool.to_string b) aux t
    | SRVar (s, Some r) :: t ->
        Format.fprintf fmt "\t<%s : real> = %f\n%a" s r aux t
  in
  if sn.node_loc_vars <> []
    then
      Format.fprintf fmt "State of the simulated node:\n\
                          \tOutput variables:\n%a
                          \tLocal variables:\n%a"
        aux sn.node_outputs
        aux sn.node_loc_vars
    else
      Format.fprintf fmt "State of the simulated node:\n\
                          \tOutput variables:\n%a
                          \tThere are no local variables:\n"
        aux sn.node_outputs


exception MySimulationException of string

let fetch_node (p: t_nodelist) (s: ident) : t_node =
  match List.filter (fun n -> n.n_name = s) p with
  | [e] -> e
  | _ -> raise (MySimulationException (Format.asprintf "Node %s undefined." s))

let fetch_var (l: sim_var list) (s: ident) =
  match List.filter
    (function
      | SBVar (v, _) | SRVar (v, _) | SIVar (v, _) -> v = s) l with
  | [v] -> v
  | _ -> raise (MySimulationException
                (Format.asprintf "Variable %s undefined." s))

(** TODO! *)
let make_sim (main_fn: ident) (p: t_nodelist): sim_node =
  let main_n = fetch_node p main_fn in
  let node_outputs =
    List.map
      (function
        | IVar s -> SIVar (s, None)
        | BVar s -> SBVar (s, None)
        | RVar s -> SRVar (s, None))
      (snd main_n.n_outputs) in
  let node_loc_vars: sim_var list =
    List.map
      (function
        | IVar s -> SIVar (s, None)
        | BVar s -> SBVar (s, None)
        | RVar s -> SRVar (s, None))
      (snd main_n.n_local_vars) in
  let node_inner_nodes = (* TODO! *) [] in
  ({node_outputs = node_outputs;
    node_loc_vars = node_loc_vars;
    node_inner_nodes = node_inner_nodes; },
    (fun s l -> (s.node_outputs, s)))



let simulate main_fn ast =
  let sim_ast = make_sim main_fn ast in
  Format.printf "Initial state:\n%a" pp_sim sim_ast

