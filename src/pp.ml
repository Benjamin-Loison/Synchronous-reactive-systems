open Ast

let pp_loc fmt (start, stop) =
  Lexing.(
    Format.fprintf fmt "%s: <l: %d, c: %d> -- <l: %d, c: %d>"
      start.pos_fname
      start.pos_lnum start.pos_cnum
      stop.pos_lnum stop.pos_cnum)

let rec pp_varlist fmt : t_varlist -> unit = function
  | (FTList [], []) -> ()
  | (FTList (FTBase TInt :: _),  IVar h :: []) -> Format.fprintf fmt  "%s" h
  | (FTList (FTBase TReal :: _), RVar h :: []) -> Format.fprintf fmt  "%s" h
  | (FTList (FTBase TBool :: _), BVar h :: []) -> Format.fprintf fmt  "%s" h
  | (FTList (FTBase TInt :: tl),  (IVar h) :: h' :: l) ->
      Format.fprintf fmt  "%s, %a" h pp_varlist (FTList tl, (h' :: l))
  | (FTList (FTBase TBool :: tl), (BVar h) :: h' :: l) ->
      Format.fprintf fmt  "%s, %a" h pp_varlist (FTList tl, (h' :: l))
  | (FTList (FTBase TReal :: tl), (RVar h) :: h' :: l) ->
      Format.fprintf fmt  "%s, %a" h pp_varlist (FTList tl, (h' :: l))
  | _ -> raise (MyTypeError "This exception should not have beed be raised.")

let pp_expression =
  let upd_prefix s = s ^ " |  " in
  let rec pp_expression_aux prefix fmt expression =
    let rec pp_expression_list prefix fmt exprs =
      match exprs with
      | ETuple(FTList [], []) -> ()
      | ETuple (FTList (_ :: tt), expr :: exprs) ->
          Format.fprintf fmt "%a%a"
            (pp_expression_aux (prefix^" |> ")) expr
            (pp_expression_list prefix) (ETuple (FTList tt, exprs))
      | _ -> raise (MyTypeError "This exception should not have been raised.")
    in
    match expression with
    | EFby (_, e1, e2) ->
        begin
          Format.fprintf fmt "\t\t\t%sFBY\n%a\t\t\tFBY\n%a"
            prefix
            (pp_expression_aux (upd_prefix prefix)) e1
            (pp_expression_aux (upd_prefix prefix)) e2
        end
    | EWhen (_, e1, e2) ->
        begin
          Format.fprintf fmt "\t\t\t%sWHEN\n%a\t\t\tWHEN\n%a"
            prefix
            (pp_expression_aux (upd_prefix prefix)) e1
            (pp_expression_aux (upd_prefix prefix)) e2
        end
    | EConst (_, c) ->
        begin match c with
        | CBool true ->  Format.fprintf fmt "\t\t\t%s<true : bool>\n" prefix
        | CBool false ->  Format.fprintf fmt "\t\t\t%s<false : bool>\n" prefix
        | CInt i ->      Format.fprintf fmt "\t\t\t%s<%5d: int>\n" prefix i
        | CReal r ->      Format.fprintf fmt "\t\t\t%s<%5f: float>\n" prefix r
        end
    | EVar (_, IVar v) -> Format.fprintf fmt "\t\t\t%s<int var %s>\n" prefix v
    | EVar (_, BVar v) -> Format.fprintf fmt "\t\t\t%s<bool var %s>\n" prefix v
    | EVar (_, RVar v) -> Format.fprintf fmt "\t\t\t%s<real var %s>\n" prefix v
    | EMonOp (_, mop, arg) ->
        begin match mop with
        | MOp_not ->
            Format.fprintf fmt "\t\t\t%s ¬ \n%a" prefix
              (pp_expression_aux (upd_prefix prefix)) arg
        | MOp_minus ->
            Format.fprintf fmt "\t\t\t%s — \n%a" prefix
              (pp_expression_aux (upd_prefix prefix)) arg
        | MOp_pre ->
            Format.fprintf fmt "\t\t\t%spre\n%a" prefix
              (pp_expression_aux (upd_prefix prefix)) arg
        end
    | EBinOp (_, bop, arg, arg') ->
        begin
        let s = match bop with
        | BOp_add -> " + " | BOp_sub -> " - "
        | BOp_mul -> " ∗ " | BOp_div -> " / " | BOp_mod -> "%  "
        | BOp_and -> "&& " | BOp_or  -> "|| " | BOp_arrow -> "-> " in
        Format.fprintf fmt "\t\t\t%s%s\n%a%a" prefix s 
          (pp_expression_aux (upd_prefix prefix)) arg
          (pp_expression_aux (upd_prefix prefix)) arg'
        end
    | EComp (_, cop, arg, arg') ->
        begin
        let s = match cop with
        | COp_eq  -> "== "
        | COp_neq -> " ≠ "
        | COp_le  -> " ≤ " | COp_lt  -> " < "
        | COp_ge  -> " ≥ " | COp_gt  -> " > " in
        Format.fprintf fmt "\t\t\t%s%s\n%a%a" prefix s 
          (pp_expression_aux (upd_prefix prefix)) arg
          (pp_expression_aux (upd_prefix prefix)) arg'
        end
    | ETriOp (_, top, arg, arg', arg'') ->
        begin match top with
        | TOp_if ->
            Format.fprintf fmt "\t\t\t%sIF\n%a\t\t\tTHEN\n%a\t\t\tELSE\n%a"
              prefix
              (pp_expression_aux (upd_prefix prefix)) arg
              (pp_expression_aux (upd_prefix prefix)) arg'
              (pp_expression_aux (upd_prefix prefix)) arg''
        | TOp_merge ->
            Format.fprintf fmt "\t\t\t%sMERGE ON CLK\n%a\t\t\tE1\n%a\t\t\tE2\n%a"
              prefix
              (pp_expression_aux (upd_prefix prefix)) arg
              (pp_expression_aux (upd_prefix prefix)) arg'
              (pp_expression_aux (upd_prefix prefix)) arg''
        end
    | EApp (_, f, args)  ->
        Format.fprintf fmt "\t\t\t%sApp %s\n%a"
          prefix f.n_name
          (pp_expression_list prefix) args
    | ETuple _ ->
        Format.fprintf fmt "\t\t\t%sTuple\n%a" prefix
          (pp_expression_list prefix) expression;
    in
  pp_expression_aux ""

let rec pp_equations fmt: t_eqlist -> unit = function
  | [] -> ()
  | (patt, expr) :: eqs ->
      Format.fprintf fmt "\t\t∗ left side: %a\n\t\t  right side:\n%a\n%a"
        pp_varlist patt
        pp_expression expr
        pp_equations eqs

let pp_node fmt node =
  Format.fprintf fmt "\t∗ Nom du nœud : %s\n\t  Inputs:\n%a\n\t  Outputs:\n%a\n\t\
    \ \ Local variables:\n%a\n\t  Equations:\n%a\n"
                 node.n_name
    pp_varlist node.n_inputs
    pp_varlist node.n_outputs
    pp_varlist node.n_local_vars
    pp_equations node.n_equations

let rec pp_nodes fmt nodes =
  match nodes with
  | [] -> ()
  | node :: nodes ->
    Format.fprintf fmt "%a\n%a" pp_node node pp_nodes nodes

let pp_ast fmt prog =
  Format.fprintf fmt
    "Le programme est composé de %d nœud(s), listés ci-dessous :\n%a"
    (List.length prog)
    pp_nodes prog

