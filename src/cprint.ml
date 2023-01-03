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



(** [cp_state_frees] prints the required code to recursively free the node
  * states. *)
let cp_state_frees fmt (iprog, sts) =
  let rec find_callee (i: int) (f: i_node) =
    let rec aux_expr = function
      | IETuple [] | IEVar   _ | IEConst _ -> None
      | IEMonOp (_, e) -> aux_expr e
      | IEWhen  (e, e')
      | IEReset (e, e')
      | IEComp  (_, e, e')
      | IEBinOp (_, e, e') ->
        begin
          match aux_expr e with
          | None -> aux_expr e'
          | Some res -> Some res
        end
      | IETriOp (_, e, e', e'') ->
        begin
          match aux_expr e with
          | None ->
            (match aux_expr e' with
            | None -> aux_expr e''
            | Some res -> Some res)
          | Some res -> Some res
        end
      | IETuple (h :: t) ->
        begin
          match aux_expr h with
          | None -> aux_expr (IETuple t)
          | Some res -> Some res
        end
      | IEApp   (j, n, e) ->
          if i = j
            then Some n.n_name
            else aux_expr e
    in
    List.fold_right
      (fun (_, expr) acc ->
        match acc with
        | Some _ -> acc
        | None -> aux_expr expr)
      f.in_equations None
  in
  let rec cp_free_aux fmt (i, caller_name) =
    let idx = i - 1 in
    match find_callee i (List.find (fun n -> n.in_name = caller_name) iprog)with
    | None -> ()
    | Some callee_name ->
      let callee_st = Hashtbl.find sts callee_name in
      if callee_st.nt_count_app > 0
        then
          Format.fprintf fmt "\tif (st->aux_states[%d]) {\n\
            \t\tfree_state_%s((t_state_%s*)(st->aux_states[%d]));\n\
            \t\tfree (st->aux_state[%d]);\n\t}\n%a"
            idx callee_name callee_name idx
            idx cp_free_aux (i+1, caller_name)
        else Format.fprintf fmt "\tif (st->aux_states[%d])\n\
            \t\tfree(st->aux_states[%d]);\n%a"
            idx idx cp_free_aux (i+1, caller_name)
  in
  Hashtbl.iter
    (fun node_name node_st ->
      if node_st.nt_count_app = 0
        then () (** Nothing to free for the node [node_name]. *)
        else
          Format.fprintf fmt "void free_state_%s(t_state_%s *);\n"
            node_name node_name) sts;
  Hashtbl.iter
    (fun node_name node_st ->
      if node_st.nt_count_app = 0
        then () (** Nothing to free for the node [node_name]. *)
        else
          Format.fprintf fmt "void free_state_%s(t_state_%s *st)\n\
            {\n\
              %a\
            }\n"
            node_name node_name
            cp_free_aux (1, node_name)) sts



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



(** [cp_prototype] prints functions prototypes (without the «;»). It is only
  * used to write the beginning of functions right now. If we later allow to
  * use auxiliary nodes before their definition, it might be useful to declare
  * all the prototypes at the beginning of the file (Cf. [cp_prototypes] below.
  *)
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



(** [cp_value] prints values, that is unary or binary operations which can be
  * inlined in the final code without requiring many manipulations.
  * It uses a lot of parenthesis at the moment. An improvement would be to
  * remove useless ones at some point. *)
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



(** [cp_main] prints  a main function to the C code if necessary:
  * if there is a function [main] in the lustre program, it will generate a main
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
        | BVar _ -> "%hd"
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
        | BVar _ -> "%hd"
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
    Format.fprintf fmt "\"%a\\n\"%a"
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
  let cp_free fmt () =
    let main_st = Hashtbl.find  sts "main" in
    if main_st.nt_count_app = 0
      then ()
      else Format.fprintf fmt "\tfree_state_main(&state);\n"
  in
  match List.find_opt (fun n -> n.n_name = "main") prog with
  | None -> ()
  | Some node ->
    Format.fprintf fmt "int main (int argc, char **argv)\n\
      {\n%a\n\
        \tchar buffer[BUFFER_SIZE];\n\
        \tt_state_main state;\n\
        \tstate.is_init = true;\n\
        \tstate.is_reset = false;\n\
        \twhile(true) {\n\
          \t\tprintf(\"input: \");\n\
          \t\tfor(unsigned short idx = 0; idx < BUFFER_SIZE; idx++) {\n\
          \t\t\tif(idx == (BUFFER_SIZE - 1) || (buffer[idx] = getchar()) == '\\n') {\n\
          \t\t\t\tbuffer[idx] = '\\0';\n\
          \t\t\t\tbreak;\n\
          \t\t\t}\n\
          \t\t}\n\
          \t\tif(!strcmp(buffer, \"exit\")) { break; }\n\
          \t\tsscanf(buffer, %a);\n%a\
          \t\tfn_main(&state, %a);\n\
          \t\tprintf(\"output: \");\n\
          \t\tprintf(%a);\n\
          \t\tprintf(\"\\n\");\n\
        \t}\n\
        %a\treturn EXIT_SUCCESS;\n\
      }\n"
      cp_array (snd node.n_inputs)
      cp_scanf (snd node.n_inputs)
      cp_char_to_bool (snd node.n_inputs)
      cp_inputs (false, snd node.n_inputs)
      cp_printf (snd node.n_outputs)
      cp_free ()

