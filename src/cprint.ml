open Intermediate_utils
open Intermediate_ast
open Ast
open Cast

(** This file contains extremely simple functions printing C code. *)

let rec cp_includes fmt = function
  | [] -> ()
  | h :: t ->
      Format.fprintf fmt "#include <%s.h>\n%a" h cp_includes t

let cp_node_state fmt (st: node_state) =
  let print_if_any fmt (ty, nb, name): unit =
    if nb = 0
      then ()
      else Format.fprintf fmt "\n\t%s %s[%d];" ty name nb
  in
  if st.nt_count_app = 0
    then
      Format.fprintf fmt "typedef struct {%a%a%a\n\
            \tbool is_init, is_reset;\n\
            } %s;\n\n"
        print_if_any ("int", st.nt_nb_int, "ivars")
        print_if_any ("bool", st.nt_nb_bool, "bvars")
        print_if_any ("double", st.nt_nb_real, "rvars")
        st.nt_name
    else
      Format.fprintf fmt "typedef struct {%a%a%a\n\
            \tbool is_init, is_reset;\n\
            \tvoid* aux_states[%d]; /* stores the states of auxiliary nodes */\n\
            } %s;\n\n"
        print_if_any ("int", st.nt_nb_int, "ivars")
        print_if_any ("bool", st.nt_nb_bool, "bvars")
        print_if_any ("double", st.nt_nb_real, "rvars")
        st.nt_count_app st.nt_name

let cp_state_types fmt (h: (ident, node_state) Hashtbl.t): unit =
  Hashtbl.iter (fun n nst ->
    Format.fprintf fmt "/* Struct holding states of the node %s: */\n%a" n
      cp_node_state nst) h

let cp_var' fmt = function
  | CVStored (arr, idx) -> Format.fprintf fmt "state->%s[%d]" arr idx
  | CVInput s -> Format.fprintf fmt "%s" s

let cp_var fmt = function
  | IVar s -> Format.fprintf fmt "int %s" s
  | BVar s -> Format.fprintf fmt "bool %s" s
  | RVar s -> Format.fprintf fmt "double %s" s

let rec cp_varlist' fmt vl =
  let print_if_any fmt = function
    | [] -> ()
    | _ :: _ -> Format.fprintf fmt ", "
  in
  match vl with
  | [] -> ()
  | v :: vl ->
    Format.fprintf fmt "%a%a%a"
    cp_var' v
    print_if_any vl
    cp_varlist' vl

let rec cp_varlist fmt vl =
  let print_if_any fmt = function
    | [] -> ()
    | _ :: _ -> Format.fprintf fmt ", "
  in
  match vl with
  | [] -> ()
  | v :: vl ->
    Format.fprintf fmt "%a%a%a"
    cp_var v
    print_if_any vl
    cp_varlist vl

let cp_prototype fmt (node, h): unit =
  match Hashtbl.find_opt h node.in_name with
  | None -> failwith "This should not happened!"
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
    | BOp_arrow -> failwith "string_of_binop undefined on (->)"
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
  | CConst (CBool b) -> Format.fprintf fmt "%s" (Bool.to_string b)
  | CConst (CReal r) -> Format.fprintf fmt "%f" r
  | CMonOp (MOp_not, v) -> Format.fprintf fmt "! (%a)" cp_value (v, hloc)
  | CMonOp (MOp_minus, v) -> Format.fprintf fmt "- (%a)" cp_value (v, hloc)
  | CMonOp (MOp_pre, (CVariable v)) ->
      let varname = (match v with
                    | CVStored (arr, idx) ->
                      begin
                        match find_varname hloc (arr, idx) with
                        | None -> failwith "This varname should be defined."
                        | Some (n, _) -> n
                      end
                    | CVInput n -> n) in
      let (arr, idx) = Hashtbl.find hloc (varname, true) in
      Format.fprintf fmt "state->%s[%d]" arr idx
  | CBinOp (BOp_arrow, v, v') ->
      Format.fprintf fmt "(state->is_init ? (%a) : (%a))"
        cp_value (v, hloc) cp_value (v', hloc)
  | CBinOp (op, v, v') ->
      Format.fprintf fmt "(%a) %s (%a)"
        cp_value (v, hloc) (string_of_binop op) cp_value (v', hloc)
  | CComp (op, v, v') ->
      Format.fprintf fmt "(%a) %s (%a)"
        cp_value (v, hloc) (string_of_compop op) cp_value (v', hloc)
  | CMonOp (MOp_pre, _) ->
      failwith "The linearization should have removed this case."

let prefix_ = ref "\t"

(** The following function prints one transformed equation of the program into a
  * set of instruction ending in assignments. *)
let rec cp_block fmt (b, hloc) =
  match b with
  | [] -> ()
  | e :: b ->
    Format.fprintf fmt "%a%a" cp_expression (e, hloc) cp_block (b, hloc)
and cp_expression fmt (expr, hloc) =
  let prefix = !prefix_ in
  match expr with
  | CAssign (CVStored (arr, idx), value) ->
    begin
      Format.fprintf fmt "%sstate->%s[%d] = %a;\n"
        prefix arr idx cp_value (value, hloc)
    end
  | CAssign (CVInput _, _) -> failwith "never assign an input."
  | CSeq (e, e') ->
      Format.fprintf fmt "%a%a"
        cp_expression (e, hloc)
        cp_expression (e', hloc)
  | CApplication (fn, nb, argl, destl, h) ->
    begin
      let aux_node_st = Hashtbl.find h fn in
      let h_out = aux_node_st.nt_output_map in
      Format.fprintf fmt "%sfn_%s(%s, %a);\n"
        prefix fn
        (Format.asprintf "state->aux_states[%d]" (nb-1))
        cp_varlist' argl;
      let _ = List.fold_left
        (fun i var ->
          match var with
          | CVStored (arr, idx) ->
            let (arr', idx') = Hashtbl.find h_out i in
            Format.fprintf fmt "%sstate->%s[%d] = ((%s*)(state->aux_states[%d]))->%s[%d];\n"
              prefix arr idx
              aux_node_st.nt_name (nb-1)
              arr' idx';
            i+1
          | CVInput _ -> failwith "Impossible!")
        0 destl in ()
    end
  | CReset (node_name, i, v, b) ->
    begin
      Format.fprintf fmt "\tif (%a) {\n\
        \t\t((t_state_%s*)(state->aux_states[%d]))->is_init = true;\n\
        \t\t((t_state_%s*)(state->aux_states[%d]))->is_reset = true;\n\
        \t}\n\
        %a\n"
        cp_value (v, hloc)
        node_name
        (i - 1)
        node_name
        (i - 1)
        cp_block (b, hloc)
    end
  | CIf (v, b1, []) ->
      let p = prefix in
      prefix_ := prefix^"\t";
      Format.fprintf fmt "%sif (%a) {\n%a%s}\n"
        p
        cp_value (v, hloc)
        cp_block (b1, hloc)
        p;
        prefix_ := p
  | CIf (v, b1, b2) ->
      let p = prefix in
      prefix_ := prefix^"\t";
      Format.fprintf fmt "%sif (%a) {\n%a%s} else {\n%a%s}\n"
        p
        cp_value (v, hloc)
        cp_block (b1, hloc)
        p
        cp_block (b2, hloc)
        p;
      prefix_  := p



(** [cp_main] tries to print a main function to the C code.
  * If there is a function [main] in the lustre program, it will generate a main
  * function in the C code, otherwise it does not do anything.
  *)
let cp_main_fn fmt (prog, sts) =
  let rec cp_array fmt (vl: t_var list): unit =
    match vl with
    | [] -> ()
    | v :: vl ->
      let typ, name =
        match v with
        | IVar s -> ("int", s)
        | RVar s -> ("double", s)
        | BVar s ->
            Format.fprintf fmt "\tchar _char_of_%s;\n" s;
            ("bool", s)
        in
      Format.fprintf fmt "\t%s %s;\n%a" typ name
      cp_array vl
  in
  let rec cp_inputs fmt (f, l) =
    match l with
    | [] -> ()
    | h :: t ->
      (if f
        then Format.fprintf fmt ", %s%a"
        else Format.fprintf fmt "%s%a")
        (Utils.name_of_var h)
        cp_inputs (true, t)
  in
  let cp_scanf fmt vl =
    let rec cp_scanf_str fmt (b, vl) =
      match vl with
      | [] -> ()
      | h :: t ->
        (if b
          then Format.fprintf fmt " %s%a"
          else Format.fprintf fmt "%s%a")
        (match h with
        | IVar _ -> "%d"
        | BVar _ -> "%c"
        | RVar _ -> "%lf")
        cp_scanf_str (true, t)
    in
    let rec cp_scanf_args fmt vl =
      match vl with
      | [] -> ()
      | RVar s :: vl | IVar s :: vl ->
        Format.fprintf fmt ", &%s%a" s cp_scanf_args vl
      | BVar s :: vl ->
        Format.fprintf fmt ", &%s%a" (Format.sprintf "_char_of_%s" s)
          cp_scanf_args  vl
    in
    Format.fprintf fmt "\"%a\"%a"
      cp_scanf_str (false, vl)
      cp_scanf_args vl
  in
  let cp_printf fmt vl =
    let rec cp_printf_str fmt (b, vl) =
      match vl with
      | [] -> ()
      | h :: t ->
        (if b
          then Format.fprintf fmt " %s%a"
          else Format.fprintf fmt "%s%a")
        (match h with
        | IVar _ -> "%d"
        | BVar _ -> "%c"
        | RVar _ -> "%f")
        cp_printf_str (true, t)
    in
    let rec cp_printf_arg fmt (h, i) =
      match Hashtbl.find_opt h i with
      | None -> ()
      | Some (s, i) ->
        Format.fprintf fmt ", state.%s[%d]%a"
          s i cp_printf_arg (h, i+1)
    in
    Format.fprintf fmt "\"%a\"%a"
      cp_printf_str (false, vl)
      cp_printf_arg ((Hashtbl.find sts "main").nt_output_map, 0)
  in
  let rec cp_char_to_bool fmt vl =
    match vl with
    | [] -> ()
    | RVar _ :: vl | IVar _ :: vl -> Format.fprintf fmt "%a" cp_char_to_bool vl
    | BVar s :: vl ->
      Format.fprintf fmt "\t\t%s = (%s == 't') ? true : false;\n%a"
        s (Format.sprintf "_char_of_%s" s)
        cp_char_to_bool vl
  in
  match List.find_opt (fun n -> n.n_name = "main") prog with
  | None -> ()
  | Some node ->
    Format.fprintf fmt "int main (int argc, char **argv)\n\
      {\n%a\n\
        \tchar _buffer[1024];\n\
        \tt_state_main state; state.is_init = true;\n\
        \twhile(true) {\n\
          \t\tscanf(\"%%s\", _buffer);\n\
          \t\tif(!strcmp(_buffer, \"exit\")) { exit (EXIT_SUCCESS); }\n\
          \t\tsscanf(_buffer, %a);\n%a\
          \t\tfn_main(&state, %a);\n\
          \t\tprintf(%a);\n\
        \t}\n\
        \treturn EXIT_SUCCESS;\n\
      }\n"
      cp_array (snd node.n_inputs)
      cp_scanf (snd node.n_inputs)
      cp_char_to_bool (snd node.n_inputs)
      cp_inputs (false, snd node.n_inputs)
      cp_printf (snd node.n_outputs)
