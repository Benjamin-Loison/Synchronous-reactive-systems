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
          (* as don't use a variable assigned when the condition holds, can define it even if the condition doesn't hold *)
          Format.fprintf fmt "%a"
            pp_expression_aux e1
        end
    (* TODO: *)
    | EReset (_, e1, e2) ->
        begin
          Format.fprintf fmt "\t\t\tRESET\n%a\t\t\tRESET\n%a"
            pp_expression_aux e1
            pp_expression_aux e2
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
    | EAuto _ -> failwith "todo"
    in
  pp_expression_aux

let rec pp_equations node_name fmt: t_eqlist -> unit = function
  | [] -> ()
  | (([], []), (ETuple ([], []))) :: eqs -> Format.fprintf fmt "%a" (pp_equations node_name) eqs
  | ((l_type :: l_types, var :: vars), (ETuple (r_type :: r_types, expr :: exprs))) :: eqs -> Format.fprintf fmt "%a" (pp_equations node_name) ((([l_type], [var]), expr) :: ((l_types, vars), (ETuple (r_types, exprs))) :: eqs)
  | (patt, expr) :: eqs ->
      Format.fprintf fmt "\t%a = %a;\n%a"
        (pp_varlist Base) patt
        (pp_expression node_name) expr
        (pp_equations node_name) eqs

(* TODO: manage general outputs *)
let pp_node fmt node =
  (* undefined behavior if the initial code uses a variable with name `init_{NODE_NAME}` or `pre_{NODE_MAIN}_{VARIABLE}` *)
  Format.fprintf fmt "bool init_%s = true;\n\n%a\n\n%a\n\n%a\n\n%a %s(%a)\n{\n\t%a\n\n\t%a\n\n%a\n\tinit_%s = false;\n\n%a\n\n%a\n\n%a\n\n\treturn %a;\n}\n"
    node.n_name
    (* could avoid declaring unused variables *)
    (pp_prevarlist node.n_name) node.n_inputs
    (pp_prevarlist node.n_name) node.n_local_vars
    (pp_prevarlist node.n_name) node.n_outputs
    pp_retvarlist node.n_outputs
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
    (pp_varlist Base) node.n_outputs

let rec pp_nodes fmt nodes =
  match nodes with
  | [] -> ()
  | node :: nodes ->
    Format.fprintf fmt "%a\n%a" pp_node node pp_nodes nodes

let ast_to_c fmt prog =
  Format.fprintf fmt
    (* could verify that uses, possibly indirectly (cf `->` implementation), a boolean in the ast before including `<stdbool.h>` *)
    "#include <stdbool.h>\n\n%a"
    pp_nodes prog

