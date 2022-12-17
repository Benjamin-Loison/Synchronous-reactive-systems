open Intermediate_utils
open Intermediate_ast
open Ast
open Cast

(** This file contains extrimely simple functions printing C code. *)

let rec cp_includes fmt = function
  | [] -> ()
  | h :: t ->
      Format.fprintf fmt "#include <%s.h>\n%a" h cp_includes t

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
  match Hashtbl.find_opt h node.in_name with
  | None -> failwith "This should not happend!"
  | Some nst ->
      begin
        Format.fprintf fmt "void fn_%s (%s *state, %a)"
          node.in_name
          nst.nt_name
          cp_varlist node.in_inputs
      end

let rec cp_prototypes fmt ((nodes, h): i_nodelist * node_states) =
  match nodes with
  | [] -> ()
  | node :: nodes ->
      Format.fprintf fmt "%a;\n%a"
        cp_prototype (node, h)
        cp_prototypes (nodes, h)



let rec cp_value fmt (value, (hloc: (ident * bool, string * int) Hashtbl.t)) =
  let string_of_binop = function
    | BOp_add -> "+"
    | BOp_sub -> "-"
    | BOp_mul -> "*"
    | BOp_div -> "/"
    | BOp_mod -> "%"
    | BOp_and -> "&&"
    | BOp_or  -> "||"
    | BOp_arrow -> failwith "[cprint.ml] string_of_binop undefined on (->)"
  in
  let string_of_compop = function
    | COp_eq -> "=="
    | COp_neq -> "!="
    | COp_le -> "<="
    | COp_lt -> "<"
    | COp_ge -> ">="
    | COp_gt -> ">"
  in
  match value with
  | CVariable (CVInput s) -> Format.fprintf fmt "%s" s
  | CVariable (CVStored (arr, idx)) -> Format.fprintf fmt "state->%s[%d]" arr idx
  | CConst (CInt i) -> Format.fprintf fmt "%d" i
  | CConst (CBool true) -> Format.fprintf fmt "true"
  | CConst (CBool false) -> Format.fprintf fmt "false"
  | CConst (CReal r) -> Format.fprintf fmt "%f" r
  | CMonOp (MOp_not, v) -> Format.fprintf fmt "! (%a)" cp_value (v, hloc)
  | CMonOp (MOp_minus, v) -> Format.fprintf fmt "- (%a)" cp_value (v, hloc)
  | CMonOp (MOp_pre, (CVariable v)) ->
      let varname = (match v with
                    | CVStored (arr, idx) ->
                      begin
                        match find_varname hloc (arr, idx) with
                        | None -> failwith "[cprint.ml] This varname should be defined."
                        | Some (n, _) -> n
                      end
                    | CVInput n -> n) in
      let (arr, idx) = Hashtbl.find hloc (varname, true) in
      Format.fprintf fmt "state->%s[%d]" arr idx
  | CBinOp (BOp_arrow, v, v') ->  failwith "[cprint.ml] (->) TODO!"
  | CBinOp (op, v, v') ->
      Format.fprintf fmt "(%a) %s (%a)"
        cp_value (v, hloc) (string_of_binop op) cp_value (v', hloc)
  | CComp (op, v, v') ->
      Format.fprintf fmt "(%a) %s (%a)"
        cp_value (v, hloc) (string_of_compop op) cp_value (v', hloc)
  | CMonOp (MOp_pre, _) ->
      failwith "[cprint.ml] The linearization should have removed this case."


(** The following function prints one transformed equation of the program into a
  * set of instruction ending in assignments. *)
let rec cp_expression fmt (expr, hloc) =
  let prefix = "\t" in
  match expr with
  | CAssign (CVStored (arr, idx), value) ->
    begin
      Format.fprintf fmt "%sstate->%s[%d] = %a;\n"
        prefix arr idx cp_value (value, hloc)
    end
  | CAssign (CVInput _, _) -> failwith "should not happend."
  | CSeq (e, e') ->
      Format.fprintf fmt "%a%a"
        cp_expression (e, hloc)
        cp_expression (e', hloc)
  (**| CIf of c_value * c_block * c_block
  | CApplication of c_var list * c_expression*)
  | _ -> failwith "[cprint.ml] TODO!"

