open Ast
open C_utils
open Cprint
open Utils



(** The following function defines the [node_states] for the nodes of a program,
  * and puts them in a hash table. *)
let make_state_types nodes: (ident, node_state) Hashtbl.t =
  (* Hash table to fill *)
  let h: (ident, node_state) Hashtbl.t = Hashtbl.create (List.length nodes) in

  (** [one_node node pv ty] computes the number of variables of type [ty] in
    * [node] and a mapping from the variables of type ([ty] * bool) to int,
    *   where [pv] is a list of variables used in the pre construct in the
    *   programm. *)
  let one_node node pv ty =
    (* variables of type [ty] among output and local variables *)
    let vars =
      List.filter (fun v -> type_var v = [ty])
        (snd (varlist_concat node.n_outputs node.n_local_vars)) in
    let pre_vars =
      List.filter (fun v -> List.mem v pv) vars in
    let nb = (List.length vars) + (List.length pre_vars) in
    let tyh = Hashtbl.create nb in
    let i =
      List.fold_left
        (fun i v -> let () = Hashtbl.add tyh (v, false) i in i + 1) 0 vars in
    let _ = 
      List.fold_left
        (fun i v -> let () = Hashtbl.add tyh (v, true) i in i + 1) i pre_vars in
    (nb, tyh)
  in

  (** [find_prevars n] returns the list of variables appearing after a pre in
    * the node [n].
    * Note that the only occurence of pre are of the form pre (var), due to the
    * linearization pass.
    *)
  let find_prevars node =
    let rec find_prevars_expr = function
      | EConst _ | EVar _ -> []
      | EMonOp (_, MOp_pre, EVar (_, v)) -> [v]
      | EMonOp (_, _, e) -> find_prevars_expr e
      | ETriOp (_, _, e, e', e'') ->
          (find_prevars_expr e) @ (find_prevars_expr e') @ (find_prevars_expr e'')
      | EComp  (_, _, e, e')
      | EBinOp (_, _, e, e')
      | EWhen  (_, e, e')
      | EReset (_, e, e') -> (find_prevars_expr e) @ (find_prevars_expr e')
      | ETuple (_, l) -> List.flatten (List.map (find_prevars_expr) l)
      | EApp   (_, _, e) -> find_prevars_expr e
    in
    list_remove_duplicates
      (List.fold_left
        (fun acc (_, expr) -> (find_prevars_expr expr) @ acc)
        [] node.n_equations)
  in

  (** [aux] iterates over all nodes of the program to build the required hash
    * table *)
  let rec aux nodes =
    match nodes with
    | [] -> h
    | node :: nodes ->
        begin
        let h = aux nodes in
        let node_name = node.n_name in
        let pv = find_prevars node in
        let nb_int_vars,  h_int  = one_node node pv TInt in
        let nb_bool_vars, h_bool = one_node node pv TBool in
        let nb_real_vars, h_real = one_node node pv TReal in
        let node_out_vars = snd node.n_outputs in
        let h_out = Hashtbl.create (List.length node_out_vars) in
        let () = List.iteri
          (fun n v ->
            match v with
            | IVar _ ->
                let i = Hashtbl.find h_int (v, false) in
                Hashtbl.add h_out n ("ivars", i)
            | BVar _ ->
                let i = Hashtbl.find h_bool (v, false) in
                Hashtbl.add h_out n ("bvars", i)
            | RVar _ ->
                let i = Hashtbl.find h_real (v, false) in
                Hashtbl.add h_out n ("rvars", i))
          (snd node.n_outputs) in
        let () = Hashtbl.add h node_name
          {
            nt_name = Format.asprintf "t_state_%s" node.n_name;
            nt_nb_int = nb_int_vars;
            nt_nb_bool = nb_bool_vars;
            nt_nb_real = nb_real_vars;
            nt_map_int = h_int;
            nt_map_bool = h_bool;
            nt_map_real = h_real;
            nt_output_map = h_out;
          } in
        h
        end
    in
  aux nodes



(*let ast_to_c*)



let ast_to_c prog =
  let prog_st_types = make_state_types prog in
  Format.printf "%s\n\n%a\n\n/* Node Prototypes: */\n%a"
    Config.c_includes
    cp_state_types prog_st_types
    cp_prototypes (prog, prog_st_types)

