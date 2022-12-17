open C_utils
open Cast
open Ast

(** This file contains extrimely simple functions printing C code. *)

let rec cp_includes fmt = function
  | [] -> ()
  | h :: t ->
      Format.fprintf fmt "#include <%s>\n%a" h cp_includes t

let cp_node_state fmt (st: node_state) =
  let maybeprint fmt (ty, nb, name): unit =
    if nb = 0
      then ()
      else Format.fprintf fmt "\n\t%s %s[%d];" ty name nb
  in
  if st.nt_count_app = 0
    then
      Format.fprintf fmt "typedef struct {%a%a%a\n\
            \tbool is_init;\n\
            } %s;\n\n"
        maybeprint ("int", st.nt_nb_int, "ivars")
        maybeprint ("bool", st.nt_nb_bool, "bvars")
        maybeprint ("double", st.nt_nb_real, "rvars")
        st.nt_name
    else
      Format.fprintf fmt "typedef struct {%a%a%a\n\
            \tbool is_init;\n\
            \tvoid* aux_states[%d]; /* stores the states of auxiliary nodes */\n\
            } %s;\n\n"
        maybeprint ("int", st.nt_nb_int, "ivars")
        maybeprint ("bool", st.nt_nb_bool, "bvars")
        maybeprint ("double", st.nt_nb_real, "rvars")
        st.nt_count_app st.nt_name

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
  match Hashtbl.find_opt h node.cn_name with
  | None -> failwith "This should not happend!"
  | Some nst ->
      begin
        Format.fprintf fmt "void fn_%s (%s *state, %a)"
          node.cn_name
          nst.nt_name
          cp_varlist node.cn_inputs
      end

let rec cp_prototypes fmt ((nodes, h): c_nodelist * node_states) =
  match nodes with
  | [] -> ()
  | node :: nodes ->
      Format.fprintf fmt "%a;\n%a"
        cp_prototype (node, h)
        cp_prototypes (nodes, h)

