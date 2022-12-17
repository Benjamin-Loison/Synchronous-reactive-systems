open C_utils
open Ast

let cp_node_state fmt (st: node_state) =
  let maybeprint fmt (ty, nb, name): unit =
    if nb = 0
      then ()
      else Format.fprintf fmt "\n\t%s %s[%d];" ty name nb
  in
  Format.fprintf fmt "typedef struct {%a%a%a\n\tbool is_init;\n} %s;\n\n"
    maybeprint ("int", st.nt_nb_int, "ivars")
    maybeprint ("bool", st.nt_nb_bool, "bvars")
    maybeprint ("double", st.nt_nb_real, "rvars")
    st.nt_name

let cp_state_types fmt (h: (ident, node_state) Hashtbl.t): unit =
  Hashtbl.iter (fun n nst ->
    Format.fprintf fmt "/* Struct holding states of the node %s: */\n%a" n
      cp_node_state nst) h

let cp_var fmt = function
  | IVar s -> Format.fprintf fmt "int %s" s
  | BVar s -> Format.fprintf fmt "bool %s" s
  | RVar s -> Format.fprintf fmt "double %s" s

let rec cp_varlist fmt vl =
  let maybeprint fmt = function
    | [] -> ()
    | _ :: _ -> Format.fprintf fmt ", "
  in
  match vl with
  | [] -> ()
  | v :: vl ->
    Format.fprintf fmt "%a%a%a"
    cp_var v
    maybeprint vl
    cp_varlist vl

let cp_prototype fmt (node, h): unit =
  match Hashtbl.find_opt h node.n_name with
  | None -> failwith "This should not happend!"
  | Some nst ->
      begin
        Format.fprintf fmt "void %s (%s *state, %a)"
          node.n_name
          nst.nt_name
          cp_varlist (snd node.n_inputs)
      end

let rec cp_prototypes fmt (nodes, h) =
  match nodes with
  | [] -> ()
  | node :: nodes ->
      Format.fprintf fmt "%a;\n%a"
        cp_prototype (node, h)
        cp_prototypes (nodes, h)

(** The ollowing function prints the code to remember previous values of
  * variables used with the pre construct. *)
let cp_prevars fmt (node, h) =
  Format.fprintf fmt
    "\n\t/* Remember the values of variables used in the [pre] construct */\n";
  let node_st = Hashtbl.find h node.n_name in
  List.iter
    (fun v -> (** Note that «dst_array = src_array» should hold. *)
      let (src_array, src_idx) = Hashtbl.find node_st.nt_map (v, false) in
      let (dst_array, dst_idx) = Hashtbl.find node_st.nt_map (v, true) in
      Format.fprintf fmt "\t%s[%d] = %s[%d];\n"
        dst_array dst_idx src_array src_idx)
    node_st.nt_prevars

let rec cp_node fmt (node, h) =
  Format.fprintf fmt "%a\n{\n\t\tTODO...\n\n\tstate->is_init = false;\n%a}\n"
    cp_prototype (node, h)
    cp_prevars (node, h)

let rec cp_nodes fmt (nodes, h) =
  match nodes with
  | [] -> ()
  | node :: nodes ->
      Format.fprintf fmt "%a\n%a"
        cp_node (node, h)
        cp_nodes (nodes, h)
