open Ast

let pp_loc fmt (start, stop) =
  Lexing.(
    Format.fprintf fmt "%s: <l: %d, c: %d> -- <l: %d, c: %d>"
      start.pos_fname
      start.pos_lnum start.pos_cnum
      stop.pos_lnum stop.pos_cnum)

type var_list_delim =
  | Base
  | Arg
  | Dec

let rec pp_varlist var_list_delim fmt : t_varlist -> unit = function
  | ([], []) -> ()
  | ([TInt] , IVar h :: []) -> Format.fprintf fmt (
      match var_list_delim with
          | Base -> "%s"
          | Arg -> "int %s"
          | Dec -> "int %s;") h
  | ([TReal], RVar h :: []) -> Format.fprintf fmt (
      match var_list_delim with
          | Base -> "%s"
          | Arg -> "float %s"
          | Dec -> "float %s;") h
  | ([TBool], BVar h :: []) -> Format.fprintf fmt (
      match var_list_delim with
          | Base -> "%s"
          | Arg -> "bool %s"
          | Dec -> "bool %s;") h
  | (TInt :: tl,  IVar h :: h' :: l) ->
      Format.fprintf fmt (
          match var_list_delim with
              | Base -> "%s, %a"
              | Arg -> "int %s, %a"
              | Dec -> "int %s;\n\t%a") h (pp_varlist var_list_delim) (tl, h' :: l)
  | (TBool :: tl, BVar h :: h' :: l) ->
      Format.fprintf fmt (
          match var_list_delim with
              | Base -> "%s, %a"
              | Arg -> "bool %s, %a"
              | Dec -> "bool %s;\n\t%a") h (pp_varlist var_list_delim) (tl, h' :: l)
  | (TReal :: tl, RVar h :: h' :: l) ->
      Format.fprintf fmt (
          match var_list_delim with
              | Base -> "%s, %a"
              | Arg -> "float %s, %a"
              | Dec -> "float %s;\n\t%a") h (pp_varlist var_list_delim) (tl, h' :: l)
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let rec pp_retvarlist fmt : t_varlist -> unit = function
  | ([], []) -> ()
  | ([TInt] , IVar h :: []) -> Format.fprintf fmt "int"
  | ([TReal], RVar h :: []) -> Format.fprintf fmt "float"
  | ([TBool], BVar h :: []) -> Format.fprintf fmt "bool"
  | (TInt :: tl,  IVar h :: h' :: l) ->
      Format.fprintf fmt "int, %a" pp_retvarlist (tl, h' :: l)
  | (TBool :: tl, BVar h :: h' :: l) ->
      Format.fprintf fmt "float, %a" pp_retvarlist (tl, h' :: l)
  | (TReal :: tl, RVar h :: h' :: l) ->
      Format.fprintf fmt "bool, %a" pp_retvarlist (tl, h' :: l)
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let rec pp_prevarlist node_name fmt : t_varlist -> unit = function
  | ([], []) -> ()
  | ([TInt] , IVar h :: []) -> Format.fprintf fmt "int pre_%s_%s;" node_name h
  | ([TReal], RVar h :: []) -> Format.fprintf fmt "float pre_%s_%s;" node_name h
  | ([TBool], BVar h :: []) -> Format.fprintf fmt "bool pre_%s_%s;" node_name h
  | (TInt :: tl,  IVar h :: h' :: l) ->
      Format.fprintf fmt "int pre_%s_%s;\n%a" node_name h (pp_prevarlist node_name) (tl, h' :: l)
  | (TBool :: tl, BVar h :: h' :: l) ->
      Format.fprintf fmt "float pre_%s_%s;\n%a" node_name h (pp_prevarlist node_name) (tl, h' :: l)
  | (TReal :: tl, RVar h :: h' :: l) ->
      Format.fprintf fmt "bool pre_%s_%s;\n%a" node_name h (pp_prevarlist node_name) (tl, h' :: l)
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let rec pp_asnprevarlist node_name fmt : t_varlist -> unit = function
  | ([], []) -> ()
  | ([TInt] , IVar h :: []) | ([TReal], RVar h :: []) | ([TBool], BVar h :: []) -> Format.fprintf fmt "\tpre_%s_%s = %s;" node_name h h
  | (TInt :: tl,  IVar h :: h' :: l) | (TBool :: tl, BVar h :: h' :: l) | (TReal :: tl, RVar h :: h' :: l) ->
      Format.fprintf fmt "\tpre_%s_%s = %s;\n%a" node_name h h (pp_asnprevarlist node_name) (tl, h' :: l)
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let reset_expressions_counter = ref 0;;

let outputs = ref [];;

let pp_expression node_name =
  let rec pp_expression_aux fmt expression =
    let rec pp_expression_list fmt exprs =
      match exprs with
      | ETuple([], []) -> ()
      | ETuple (_ :: tt, expr :: exprs) ->
          Format.fprintf fmt "%a%s%a"
            pp_expression_aux expr
            (if (List.length tt > 0) then ", " else "")
            pp_expression_list (ETuple (tt, exprs))
      | _ -> raise (MyTypeError "This exception should not have been raised.")
    in
    match expression with
    | EWhen (_, e1, e2) ->
        begin
          Format.fprintf fmt "%a ? %a : 0"
            pp_expression_aux e2
            pp_expression_aux e1
        end
    | EReset (_, e1, e2) ->
        begin
            incr reset_expressions_counter;
            (* Use following trick as we can't use `;`:
               if(((var = val) && false) || condition)
               is equivalent to an incorrect statement like
               if({var = val; condition})
               We also use this trick with the fact that `0` can be interpreted as a `bool`, an `int` and a `float` *)
            (* could use C macros to simplify the C code *)
            Format.fprintf fmt "(((tmp_reset[%i] = %a) && false) || init_%s) ? (((init[%i] = tmp_reset[%i]) || true) ? tmp_reset[%i] : 0) : (%a ? init[%i] : tmp_reset[%i])"
            (!reset_expressions_counter - 1)
            pp_expression_aux e1
            node_name
            (!reset_expressions_counter - 1)
            (!reset_expressions_counter - 1)
            (!reset_expressions_counter - 1)
            pp_expression_aux e2
            (!reset_expressions_counter - 1)
            (!reset_expressions_counter - 1)
        end
    | EConst (_, c) ->
        begin match c with
        | CBool b -> Format.fprintf fmt "%s" (Bool.to_string b)
        | CInt i ->  Format.fprintf fmt "%i" i
        | CReal r -> Format.fprintf fmt "%f" r
        end
    | EVar (_, IVar v) | EVar (_, BVar v) | EVar (_, RVar v) -> Format.fprintf fmt "%s" v
    | EMonOp (_, mop, arg) ->
        begin match mop with
        | MOp_not ->
            Format.fprintf fmt "!%a"
              pp_expression_aux arg
        | MOp_minus ->
            Format.fprintf fmt "-%a"
              pp_expression_aux arg
        | MOp_pre ->
            Format.fprintf fmt "pre_%s_%a" node_name
              pp_expression_aux arg
        end
    | EBinOp (_, BOp_arrow, arg, arg') ->
        Format.fprintf fmt "init_%s ? %a : %a"
          node_name
          pp_expression_aux arg
          pp_expression_aux arg'
    | EBinOp (_, bop, arg, arg') ->
        begin
        let s = match bop with
        | BOp_add -> " + " | BOp_sub -> " - "
        | BOp_mul -> " * " | BOp_div -> " / " | BOp_mod -> " % "
        | BOp_and -> " && " | BOp_or  -> " || " | _ -> "" (* `ocamlc` doesn't detect that `BOp_arrow` can't match here *) in
        Format.fprintf fmt "%a%s%a"
          pp_expression_aux arg
          s
          pp_expression_aux arg'
        end
    | EComp (_, cop, arg, arg') ->
        begin
        let s = match cop with
        | COp_eq  -> " == "
        | COp_neq -> " != "
        | COp_le  -> " <= " | COp_lt  -> " < "
        | COp_ge  -> " >= " | COp_gt  -> " > " in
        Format.fprintf fmt "%a%s%a"
          pp_expression_aux arg
          s
          pp_expression_aux arg'
        end
    | ETriOp (_, top, arg, arg', arg'') ->
        begin
            Format.fprintf fmt "%a ? %a : %a"
              pp_expression_aux arg
              pp_expression_aux arg'
              pp_expression_aux arg''
        end
    | EApp (_, f, args)  ->
        Format.fprintf fmt "%s(%a)"
          f.n_name
          pp_expression_list args
    | ETuple _ ->
        Format.fprintf fmt "%a"
          pp_expression_list expression;
    in
  pp_expression_aux

(* deterministic *)
let nodes_outputs = Hashtbl.create Config.maxvar;;

let prepend_output_aux node_name name =
    "output_" ^ node_name ^ "_" ^ name

let prepend_output output node_name =
    match output with
    | BVar name -> BVar (prepend_output_aux node_name name)
    | IVar name -> IVar (prepend_output_aux node_name name)
    | RVar name -> RVar (prepend_output_aux node_name name)

let rec pp_equations node_name fmt: t_eqlist -> unit = function
  | [] -> ()
  | ((l_types, vars), (EApp (r_types, node, exprs))) :: eqs when l_types <> [] -> Format.fprintf fmt "%a" (pp_equations node_name) ((([], []), (EApp (r_types, node, exprs))) :: ((l_types, vars), (ETuple (fst node.n_outputs, List.map (fun output -> EVar (fst node.n_outputs, prepend_output output node.n_name)) (snd node.n_outputs)))) :: eqs)
  | (([], []), (ETuple ([], []))) :: eqs -> Format.fprintf fmt "%a" (pp_equations node_name) eqs
  | ((l_type :: l_types, var :: vars), (ETuple (r_type :: r_types, expr :: exprs))) :: eqs -> Format.fprintf fmt "%a" (pp_equations node_name) ((([l_type], [var]), expr) :: ((l_types, vars), (ETuple (r_types, exprs))) :: eqs)
  | (([], []), expr) :: eqs ->
      Format.fprintf fmt "\t%a;\n%a"
        (pp_expression node_name) expr
        (pp_equations node_name) eqs
  | (patt, expr) :: eqs ->
      Format.fprintf fmt "\t%a = %a;\n%a"
        (pp_varlist Base) patt
        (pp_expression node_name) expr
        (pp_equations node_name) eqs

(* By prepending to the `Format.formatter` `fmt` we could just declare these arrays once with a size of the maximum `reset_expressions_counter` *)
let pp_resvars reset_expressions_counter =
    (* use the fact that any boolean and any integer can be encoded as a float, concerning integers [-2^(23+1) + 1; 2^(23+1) + 1] are correctly encoded (cf https://stackoverflow.com/a/53254438) *)
    Format.sprintf "float tmp_reset[%i], init[%i];" reset_expressions_counter reset_expressions_counter

let pp_return node_name fmt outputs =
    if node_name = "main" then
    (Format.fprintf fmt "return %a;"
    (pp_varlist Base) outputs)
    else
        Format.fprintf fmt "%s" (String.concat "\n\t" (List.map (fun output -> match output with | BVar name | IVar name | RVar name -> "output_" ^ node_name ^ "_" ^ name ^ " = " ^ name ^ ";") (snd outputs)))

let pp_node fmt node =
    (* undefined behavior if the initial code uses a variable with name:
        - `init_{NODE_NAME}`
        - `tmp_reset_{int}`
        - `init_{int}`
        - `pre_{NODE_NAME}_{VARIABLE}`
        - `output_{NODE_NAME}_{VARIABLE}` *)
  reset_expressions_counter := 0;
  let _ = (pp_equations node.n_name) Format.str_formatter node.n_equations in
  reset_expressions_counter := 0;
  Format.fprintf fmt "bool init_%s = true;\n\n%a\n\n%a\n\n%a\n\n%s\n\n%s %s(%a)\n{\n\t%a\n\n\t%a\n\n%a\n\n\tinit_%s = false;\n\n%a\n\n%a\n\n%a\n\n\t%a\n}\n"
    node.n_name
    (* could avoid declaring unused variables *)
    (pp_prevarlist node.n_name) node.n_inputs
    (pp_prevarlist node.n_name) node.n_local_vars
    (pp_prevarlist node.n_name) node.n_outputs
    (pp_resvars !reset_expressions_counter)
    (if node.n_name = "main" then "int" else "void")
    node.n_name
    (* could avoid newlines if they aren't used to seperate statements *)
    (pp_varlist Arg) node.n_inputs
    (pp_varlist Dec) node.n_local_vars
    (pp_varlist Dec) node.n_outputs
    (pp_equations node.n_name) node.n_equations
    node.n_name
    (pp_asnprevarlist node.n_name) node.n_inputs
    (pp_asnprevarlist node.n_name) node.n_local_vars
    (pp_asnprevarlist node.n_name) node.n_outputs
    (pp_return node.n_name) node.n_outputs

let rec pp_nodes fmt nodes =
  match nodes with
  | [] -> ()
  | node :: nodes ->
    Format.fprintf fmt "%a\n%a" pp_node node pp_nodes nodes

let rec load_outputs_from_vars node_name n_outputs =
  match n_outputs with
  | [] -> ()
  | BVar n_output :: n_outputs
  | IVar n_output :: n_outputs
  | RVar n_output :: n_outputs ->
    (if (not (List.mem n_output !outputs)) then outputs := (node_name ^ "_" ^ n_output) :: !outputs;); load_outputs_from_vars node_name n_outputs

let rec load_outputs_from_nodes nodes =
  match nodes with
  | [] -> ()
  | node :: nodes ->
          (if node.n_name <> "main" then (load_outputs_from_vars node.n_name (snd node.n_outputs)); Hashtbl.add nodes_outputs node.n_name (snd node.n_outputs)); load_outputs_from_nodes nodes

let ast_to_c fmt prog =
  load_outputs_from_nodes prog;
  Format.fprintf fmt
    (* could verify that uses, possibly indirectly (cf `->` implementation), a boolean in the ast before including `<stdbool.h>` *)
    "#include <stdbool.h>\n\n%s\n\n%a"
    ("float " ^ (String.concat ", " (List.map (fun output -> "output_" ^ output) !outputs)) ^ ";") pp_nodes prog

