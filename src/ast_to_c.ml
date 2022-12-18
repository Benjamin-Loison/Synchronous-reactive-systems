open Ast
open Intermediate_ast
open Intermediate_utils
open Cprint
open Cast
open Utils
open Ctranslation



(** [ast_to_intermediate_ast] translates a [t_nodelist] into a [i_nodelist] *)
let ast_to_intermediate_ast (nodes: t_nodelist) (h: node_states): i_nodelist =
  let c = ref 1 in
  let ast_to_intermediate_ast_varlist vl = snd vl in
  let rec ast_to_intermediate_ast_expr hloc = function
    | EVar   (_, v) ->
        begin
        match Hashtbl.find_opt hloc (Utils.name_of_var v, false) with
        | None -> IEVar (CVInput (name_of_var v))
        | Some (s, i) -> IEVar (CVStored (s, i))
        end
    | EMonOp (_, op, e) -> IEMonOp (op, ast_to_intermediate_ast_expr hloc e)
    | EBinOp (_, op, e, e') ->
       IEBinOp (op, ast_to_intermediate_ast_expr hloc e, ast_to_intermediate_ast_expr hloc e')
    | ETriOp (_, op, e, e', e'') ->
        IETriOp
          (op, ast_to_intermediate_ast_expr hloc e, ast_to_intermediate_ast_expr hloc e', ast_to_intermediate_ast_expr hloc e'')
    | EComp  (_, op, e, e') ->
        IEComp (op, ast_to_intermediate_ast_expr hloc e, ast_to_intermediate_ast_expr hloc e')
    | EWhen  (_, e, e') ->
        IEWhen (ast_to_intermediate_ast_expr hloc e, ast_to_intermediate_ast_expr hloc e')
    | EReset  (_, e, e') ->
        IEReset (ast_to_intermediate_ast_expr hloc e, ast_to_intermediate_ast_expr hloc e')
    | EConst (_, c) -> IEConst c
    | ETuple (_, l) -> IETuple (List.map (ast_to_intermediate_ast_expr hloc) l)
    | EApp   (_, n, e) ->
      begin
        let e = ast_to_intermediate_ast_expr hloc e in
        let res = IEApp (!c, n, e) in
        let () = incr c in
        res
      end
  in
  let ast_to_intermediate_ast_eq hloc (patt, expr) : i_equation =
    (ast_to_intermediate_ast_varlist patt, ast_to_intermediate_ast_expr hloc expr) in
  List.map
    begin
    fun node ->
      let () = c := 1 in
      let hloc = (Hashtbl.find h node.n_name).nt_map in
      {
        in_name = node.n_name;
        in_inputs = ast_to_intermediate_ast_varlist node.n_inputs;
        in_outputs = ast_to_intermediate_ast_varlist node.n_outputs;
        in_local_vars = ast_to_intermediate_ast_varlist node.n_local_vars;
        in_equations = List.map (ast_to_intermediate_ast_eq hloc) node.n_equations;
      }
    end
    nodes

(** The following function defines the [node_states] for the nodes of a program,
  * and puts them in a hash table. *)
let make_state_types nodes: node_states =
  (* Hash table to fill *)
  let h: (ident, node_state) Hashtbl.t = Hashtbl.create (List.length nodes) in

  (** [one_node node pv ty] computes the number of variables of type [ty] in
    * [node] and a mapping from the variables of type ([ty] * bool) to int,
    *   where [pv] is a list of variables used in the pre construct in the
    *   program. *)
  let one_node node pv ty =
    (* variables of type [ty] among output and local variables *)
    let vars =
      List.filter (fun v -> type_var v = [ty])
        (snd (varlist_concat node.n_outputs node.n_local_vars)) in
    let all_vars =
      List.filter (fun v -> type_var v = [ty])
        (snd (varlist_concat (varlist_concat node.n_inputs node.n_outputs) node.n_local_vars)) in
    let pre_vars =
      List.filter (fun v -> List.mem v pv) all_vars in
    let vars = List.map Utils.name_of_var vars in
    let pre_vars = List.map Utils.name_of_var pre_vars in
    let nb = (List.length vars) + (List.length pre_vars) in
    let tyh: (ident * bool, int) Hashtbl.t = Hashtbl.create nb in
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
    * Note that the only occurrence of pre are of the form pre (var), due to
    * the linearization pass.
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

  (** [count_app n] count the number of auxiliary nodes calls in [n] *)
  let count_app n =
    let rec count_app_expr = function
      | EConst _ | EVar _ -> 0
      | EMonOp (_, _, e) -> count_app_expr e
      | ETriOp (_, _, e, e', e'') ->
          (count_app_expr e) + (count_app_expr e') + (count_app_expr e'')
      | EComp  (_, _, e, e')
      | EBinOp (_, _, e, e')
      | EWhen  (_, e, e')
      | EReset (_, e, e') -> (count_app_expr e) + (count_app_expr e')
      | ETuple (_, l) ->
          List.fold_left (fun acc e -> acc + count_app_expr e) 0 l
      | EApp   (_, _, e) -> 1 + count_app_expr e
    in
    List.fold_left
      (fun i (_, expr) -> i + count_app_expr expr)
      0 n.n_equations
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

        (** h_map gathers information from h_* maps above *)
        let h_map =
          Hashtbl.create (nb_int_vars + nb_bool_vars + nb_real_vars) in
        let () =
          Hashtbl.iter (fun k v -> Hashtbl.add h_map k ("ivars", v)) h_int in
        let () =
          Hashtbl.iter (fun k v -> Hashtbl.add h_map k ("bvars", v)) h_bool in
        let () =
          Hashtbl.iter (fun k v -> Hashtbl.add h_map k ("rvars", v)) h_real in

        let node_out_vars = snd node.n_outputs in
        let h_out = Hashtbl.create (List.length node_out_vars) in
        let () = List.iteri
          (fun n (v: t_var) ->
            match v with
            | IVar s ->
                let i = Hashtbl.find h_int (s, false) in
                Hashtbl.add h_out n ("ivars", i)
            | BVar s ->
                let i = Hashtbl.find h_bool (s, false) in
                Hashtbl.add h_out n ("bvars", i)
            | RVar s ->
                let i = Hashtbl.find h_real (s, false) in
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
            nt_map = h_map;
            nt_output_map = h_out;
            nt_prevars = pv;
            nt_count_app = count_app node;
          } in
        h
        end
    in
  aux nodes



(** The following C-printer functions are in this file, as they need to work on
  * the AST and are not simple printers. *)



(** The following function prints the code to remember previous values of
  * variables used with the pre construct. *)
let cp_prevars fmt (node, h) =
  let node_st = Hashtbl.find h node.in_name in
  match (Hashtbl.find h node.in_name).nt_prevars with
  | [] -> ()
  | l ->
      Format.fprintf fmt
        "\n\t/* Remember the values used in the [pre] construct */\n";
      List.iter
        (fun v -> (** Note that «dst_array = src_array» should hold. *)
          match Hashtbl.find_opt node_st.nt_map (v, false) with
          | Some (src_array, src_idx) ->
            let (dst_array, dst_idx) = Hashtbl.find node_st.nt_map (v, true) in
            Format.fprintf fmt "\tstate->%s[%d] = state->%s[%d];\n"
              dst_array dst_idx src_array src_idx
          | None -> 
            let (dst_array, dst_idx) = Hashtbl.find node_st.nt_map (v, true) in
            Format.fprintf fmt "\tstate->%s[%d] = %s;\n"
              dst_array dst_idx v
          )
        (List.map Utils.name_of_var l)



(** The following function defines the behaviour to have at the first
  * execution of a node, namely:
  *   - initialize the states of auxiliary nodes
  *)
let cp_init_aux_nodes fmt (node, h) =
  let rec aux fmt (node, nst, i) =
    match find_app_opt node.in_equations i with
    | None -> () (** All auxiliary nodes have been initialized *)
    | Some n ->
      begin
      Format.fprintf fmt "%a\t\tstate->aux_states[%d] = malloc (sizeof (%s));\n\
          \t\t((%s*)(state->aux_states[%d]))->is_init = true;\n"
        aux (node, nst, i-1)
        (i-1) (Format.asprintf "t_state_%s" n.n_name)
        (Format.asprintf "t_state_%s" n.n_name) (i-1)
      end
  in
  let nst = Hashtbl.find h node.in_name in
  if nst.nt_count_app = 0
    then ()
    else begin
      Format.fprintf fmt "\t/* Initialize the auxiliary nodes */\n\
          \tif (state->is_init) {\n%a\t}\n\n\n"
        aux (node, nst, nst.nt_count_app)
    end



(** [cp_equations] prints the node equations. *)
let cp_equations fmt (eqs, hloc, h) =
  (** [main_block] is modified through some optimization passes, eg:
    * - merge two CIf blocks using the same condition
    * - replace [if (! c) { b1 } else { b2 }] by [if(c) { b2 } else { b1 }]
    *
    *  These passes are defined in [ctranslation.ml]
      *)
  let main_block: c_block =
    List.map (fun eq -> equation_to_expression (hloc, h, eq)) eqs in
  let main_block = remove_ifnot main_block in
  let main_block = merge_neighbour_ifs main_block in
  Format.fprintf fmt "\t/*Main code :*/\n%a"
    cp_block (main_block, hloc.nt_map)

(** [cp_node] prints a single node *)
let cp_node fmt (node, h) =
  Format.fprintf fmt "%a\n{\n%a%a\n\n\tstate->is_init = false;\n%a}\n"
    cp_prototype (node, h)
    cp_init_aux_nodes (node, h)
    cp_equations (node.in_equations, Hashtbl.find h node.in_name, h)
    cp_prevars (node, h)

(** [cp_nodes] recursively prints all the nodes of a program. *)
let rec cp_nodes fmt (nodes, h) =
  match nodes with
  | [] -> ()
  | node :: nodes ->
      Format.fprintf fmt "%a\n%a"
        cp_node (node, h)
        cp_nodes (nodes, h)



let dump_var_locations (st: node_states) =
  Hashtbl.iter
    (fun n st ->
      Format.printf "\n\n\tNODE: %s\n" n;
    Hashtbl.iter
    (fun (s, (ispre: bool)) ((arr: string), (idx: int)) ->
      match ispre with
      | true -> Format.printf "PRE Variable %s stored as %s[%d]\n" s arr idx
      | false -> Format.printf "    Variable %s stored as %s[%d]\n" s arr idx)
    st.nt_map)
    st;
    Format.printf "\n\n"



(** main function that prints a C-code from a term of type [t_nodelist]. *)
let ast_to_c (debug: bool) prog =
  let prog_st_types = make_state_types prog in
  let () =
    if debug
      then dump_var_locations prog_st_types
      else ()
    in
  let prog: i_nodelist = ast_to_intermediate_ast prog prog_st_types in
  Format.printf "%a\n\n%a\n\n/* Node Prototypes: */\n%a\n\n/* Nodes: */\n%a"
    cp_includes (Config.c_includes)
    cp_state_types prog_st_types
    cp_prototypes (prog, prog_st_types)
    cp_nodes (prog, prog_st_types)

