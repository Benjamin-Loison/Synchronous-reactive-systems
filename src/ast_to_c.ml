open Ast

let pp_loc fmt (start, stop) =
  Lexing.(
    Format.fprintf fmt "%s: <l: %d, c: %d> -- <l: %d, c: %d>"
      start.pos_fname
      start.pos_lnum start.pos_cnum
      stop.pos_lnum stop.pos_cnum)

(* could use an argument instead of redefining these functions, if possible *)
let rec pp_varlist fmt : t_varlist -> unit = function
  | ([], []) -> ()
  | ([TInt] ,  IVar h :: []) -> Format.fprintf fmt  "%s" h
  | ([TReal],  RVar h :: []) -> Format.fprintf fmt  "%s" h
  | ([TBool],  BVar h :: []) -> Format.fprintf fmt  "%s" h
  | (TInt :: tl,  IVar h :: h' :: l) ->
      Format.fprintf fmt  "%s, %a" h pp_varlist (tl, h' :: l)
  | (TBool :: tl, BVar h :: h' :: l) ->
      Format.fprintf fmt  "%s, %a" h pp_varlist (tl, h' :: l)
  | (TReal :: tl, RVar h :: h' :: l) ->
      Format.fprintf fmt  "%s, %a" h pp_varlist (tl, h' :: l)
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let rec pp_argvarlist fmt : t_varlist -> unit = function
  | ([], []) -> ()
  | ([TInt] ,  IVar h :: []) -> Format.fprintf fmt  "int %s" h
  | ([TReal],  RVar h :: []) -> Format.fprintf fmt  "float %s" h
  | ([TBool],  BVar h :: []) -> Format.fprintf fmt  "bool %s" h
  | (TInt :: tl,  IVar h :: h' :: l) ->
      Format.fprintf fmt  "int %s, %a" h pp_argvarlist (tl, h' :: l)
  | (TBool :: tl, BVar h :: h' :: l) ->
      Format.fprintf fmt  "bool %s, %a" h pp_argvarlist (tl, h' :: l)
  | (TReal :: tl, RVar h :: h' :: l) ->
      Format.fprintf fmt  "real %s, %a" h pp_argvarlist (tl, h' :: l)
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let rec pp_decvarlist fmt : t_varlist -> unit = function
  | ([], []) -> ()
  | ([TInt] ,  IVar h :: []) -> Format.fprintf fmt  "int %s;" h
  | ([TReal],  RVar h :: []) -> Format.fprintf fmt  "float %s;" h
  | ([TBool],  BVar h :: []) -> Format.fprintf fmt  "bool %s;" h
  | (TInt :: tl,  IVar h :: h' :: l) ->
      Format.fprintf fmt  "%s: int, %a" h pp_decvarlist (tl, h' :: l)
  | (TBool :: tl, BVar h :: h' :: l) ->
      Format.fprintf fmt  "%s: bool, %a" h pp_decvarlist (tl, h' :: l)
  | (TReal :: tl, RVar h :: h' :: l) ->
      Format.fprintf fmt  "%s: real, %a" h pp_decvarlist (tl, h' :: l)
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let rec pp_retvarlist fmt : t_varlist -> unit = function
  | ([], []) -> ()
  | ([TInt] ,  IVar h :: []) -> Format.fprintf fmt  "int"
  | ([TReal],  RVar h :: []) -> Format.fprintf fmt  "float"
  | ([TBool],  BVar h :: []) -> Format.fprintf fmt  "bool"
  | (TInt :: tl,  IVar h :: h' :: l) ->
      Format.fprintf fmt  "int, %a" pp_retvarlist (tl, h' :: l)
  | (TBool :: tl, BVar h :: h' :: l) ->
      Format.fprintf fmt  "float, %a" pp_retvarlist (tl, h' :: l)
  | (TReal :: tl, RVar h :: h' :: l) ->
      Format.fprintf fmt  "bool, %a" pp_retvarlist (tl, h' :: l)
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let pp_expression =
  let rec pp_expression_aux prefix fmt expression =
    let rec pp_expression_list prefix fmt exprs =
      match exprs with
      | ETuple([], []) -> ()
      | ETuple (_ :: tt, expr :: exprs) ->
          Format.fprintf fmt "%a%a"
            (pp_expression_aux (prefix^" |> ")) expr
            (pp_expression_list prefix) (ETuple (tt, exprs))
      | _ -> raise (MyTypeError "This exception should not have been raised.")
    in
    match expression with
    | EWhen (_, e1, e2) ->
        begin
          (* as don't use a variable assigned when the condition holds, can define it even if the condition doesn't hold *)
          Format.fprintf fmt "%s%a"
            prefix
            (pp_expression_aux prefix) e1
        end
    (* TODO: *)
    | EReset (_, e1, e2) ->
        begin
          Format.fprintf fmt "\t\t\t%sRESET\n%a\t\t\tRESET\n%a"
            prefix
            (pp_expression_aux prefix) e1
            (pp_expression_aux prefix) e2
        end
    | EConst (_, c) ->
        begin match c with
        | CBool b ->  Format.fprintf fmt "%s%s" prefix (Bool.to_string b)
        | CInt i ->      Format.fprintf fmt "%s%i" prefix i
        | CReal r ->      Format.fprintf fmt "%s%f" prefix r
        end
    | EVar (_, IVar v) -> Format.fprintf fmt "%s%s" prefix v
    | EVar (_, BVar v) -> Format.fprintf fmt "%s%s" prefix v
    | EVar (_, RVar v) -> Format.fprintf fmt "%s%s" prefix v
    | EMonOp (_, mop, arg) ->
        begin match mop with
        | MOp_not ->
            Format.fprintf fmt "!%s%a" prefix
              (pp_expression_aux prefix) arg
        | MOp_minus ->
            Format.fprintf fmt "-%s%a" prefix
              (pp_expression_aux prefix) arg
        (* TODO *)
        | MOp_pre ->
            Format.fprintf fmt "pre %s%a" prefix
              (pp_expression_aux prefix) arg
        end
    | EBinOp (_, bop, arg, arg') ->
        begin
        let s = match bop with
        | BOp_add -> " + " | BOp_sub -> " - "
        | BOp_mul -> " * " | BOp_div -> " / " | BOp_mod -> " % "
        (* TODO: -> *)
        | BOp_and -> " && " | BOp_or  -> " || " | BOp_arrow -> " -> " in
        Format.fprintf fmt "%s%a%s%a" prefix 
          (pp_expression_aux prefix) arg
          s
          (pp_expression_aux prefix) arg'
        end
    | EComp (_, cop, arg, arg') ->
        begin
        let s = match cop with
        | COp_eq  -> " == "
        | COp_neq -> " != "
        | COp_le  -> " <= " | COp_lt  -> " < "
        | COp_ge  -> " >= " | COp_gt  -> " > " in
        Format.fprintf fmt "%s%a%s%a" prefix 
          (pp_expression_aux prefix) arg
          s
          (pp_expression_aux prefix) arg'
        end
    | ETriOp (_, top, arg, arg', arg'') ->
        begin match top with
        | TOp_if | TOp_merge ->
            Format.fprintf fmt "%s%a ? %a : %a"
              prefix
              (pp_expression_aux prefix) arg
              (pp_expression_aux prefix) arg'
              (pp_expression_aux prefix) arg''
        end
    (* TODO *)
    | EApp (_, f, args)  ->
        Format.fprintf fmt "%s%s(%a)"
          prefix f.n_name
          (pp_expression_list prefix) args
    | ETuple _ ->
        Format.fprintf fmt "%s%a" prefix
          (pp_expression_list prefix) expression;
    in
  pp_expression_aux ""

(* should add a prefix for indentation *)
let rec pp_equations fmt: t_eqlist -> unit = function
  | [] -> ()
  | (patt, expr) :: eqs ->
      Format.fprintf fmt "%a = %a;\n%a"
        pp_varlist patt
        pp_expression expr
        pp_equations eqs

(* TODO: manage general outputs *)
let pp_node fmt node =
  Format.fprintf fmt "%a %s(%a)\n{\n\t%a\n\t%a\n%a\n\treturn %a;\n}\n"
    pp_retvarlist (node.n_outputs)
                 node.n_name
    (* could avoid newlines if they aren't used to seperate statements *)
    pp_argvarlist node.n_inputs
    pp_decvarlist node.n_local_vars
    pp_decvarlist node.n_outputs
    pp_equations node.n_equations
    pp_varlist node.n_outputs

let rec pp_nodes fmt nodes =
  match nodes with
  | [] -> ()
  | node :: nodes ->
    Format.fprintf fmt "%a\n%a" pp_node node pp_nodes nodes

let ast_to_c fmt prog =
  Format.fprintf fmt
    (* could verify that uses a boolean in the ast before including `<stdbool.h>` *)
    "#include <stdbool.h>\n\n%a"
    pp_nodes prog

