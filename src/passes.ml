(** This file contains simplification passes for our Lustre-like AST *)

open Ast
open Passes_utils
open Utils



(** [pass_when_lin] linearises the when construct so that it only appears as
  * main construction of right members of equations. *)
let pass_when_lin verbose debug =
  (* prefix of the fresh variables to use and counter to make them unique. *)
  let varname_prefix = "_whenlin" in
  let count = ref 0 in
  (** Auxiliary function that linearises an expression. *)
  let rec aux_expr vars expr toplevel conds =
    match expr with
    | EVar _ | EConst _ -> [], vars, expr
    | EMonOp (t, op, e) ->
      let eqs, vars, e = aux_expr vars e false conds in
      eqs, vars, EMonOp (t, op, e)
    | EBinOp (t, op, e, e') ->
      let eqs, vars, e = aux_expr vars e false conds in
      let eqs', vars, e' = aux_expr vars e' false conds in
      eqs'@eqs, vars, EBinOp (t, op, e, e')
    | EComp (t, op, e, e') ->
      let eqs, vars, e = aux_expr vars e false conds in
      let eqs', vars, e' = aux_expr vars e' false conds in
      eqs'@eqs, vars, EComp (t, op, e, e')
    | EReset (t, e, e') ->
      let eqs, vars, e = aux_expr vars e false conds in
      let eqs', vars, e' = aux_expr vars e' false conds in
      eqs'@eqs, vars, EReset (t, e, e')
    | ETuple (t, l) ->
      let eqs, vars, l = List.fold_right
        (fun e (eqs, vars, l) ->
          let eqs', vars, e = aux_expr vars e false conds in
          eqs' @ eqs, vars, (e :: l))
        l ([], vars, []) in
      eqs, vars, ETuple (t, l)
    | EApp (t, n, e) ->
      let eqs, vars, e = aux_expr vars e false conds in
      eqs, vars, EApp (t, n, e)
    | ETriOp (t, op, e, e', e'') ->
      let eqs, vars, e = aux_expr vars e false conds in
      let eqs', vars, e' = aux_expr vars e' false conds in
      let eqs'', vars, e'' = aux_expr vars e'' false conds in
      eqs''@eqs'@eqs, vars, ETriOp (t, op, e, e', e'')
    | EWhen (t, e, e') ->
      let eqs, vars, e = aux_expr vars e false conds in
      let eqs', vars, e' = aux_expr vars e' false (e :: conds) in
      let e =
        List.fold_left
          (fun e e' -> EBinOp ([TBool], BOp_and, e,e'))
          e conds
      in
      if toplevel
        then
          eqs'@eqs, vars, EWhen (t, e, e')
        else
          begin
            if List.length t = 1
              then
                begin
                let newvar = Format.sprintf "%s%d" varname_prefix !count in
                let newvar =
                  match List.hd t with
                  | TInt -> IVar newvar
                  | TBool -> BVar newvar
                  | TReal -> RVar newvar
                  in
                let () = incr count in
                let vars = (t @ (fst vars), newvar :: (snd vars)) in
                ((t, [newvar]), EWhen (t, e, e')) :: eqs'@eqs, vars, EVar (t, newvar)
                end
              else
                  raise (PassExn "When should only happened on unary expressions.")
          end
  in
  (** For each node: *)
  let aux_when_lin node =
    (** Loop on equations to get additional equations and variables. *)
    let eqs, vars =
      List.fold_left
        (fun (eqs, vars) (patt, expr) ->
          let eqs', vars, expr = aux_expr vars expr true [] in
          (patt, expr) :: eqs' @ eqs, vars)
        ([], node.n_local_vars) node.n_equations
      in
    Some { node with n_local_vars = vars; n_equations = eqs }
  in
  node_pass aux_when_lin



(** [pass_merge_lin] linearises ther merges so that they only appear as main
  * construct of right sides of equations.
  * This simplifies their handling in next passes and in the C printer. *)
let pass_merge_lin verbose debug =
  (* prefix of the fresh variables to use and counter to make them unique. *)
  let varname_prefix = "_mergelin" in
  let count = ref 0 in
  (** Auxiliary function that linearises an expression. *)
  let rec aux_expr vars expr toplevel =
    match expr with
    | EVar _ | EConst _ -> [], vars, expr
    | EMonOp (t, op, e) ->
      let eqs, vars, e = aux_expr vars e false in
      eqs, vars, EMonOp (t, op, e)
    | EBinOp (t, op, e, e') ->
      let eqs, vars, e = aux_expr vars e false in
      let eqs', vars, e' = aux_expr vars e' false in
      eqs'@eqs, vars, EBinOp (t, op, e, e')
    | EComp (t, op, e, e') ->
      let eqs, vars, e = aux_expr vars e false in
      let eqs', vars, e' = aux_expr vars e' false in
      eqs'@eqs, vars, EComp (t, op, e, e')
    | EReset (t, e, e') ->
      let eqs, vars, e = aux_expr vars e false in
      let eqs', vars, e' = aux_expr vars e' false in
      eqs'@eqs, vars, EReset (t, e, e')
    | ETuple (t, l) ->
      let eqs, vars, l = List.fold_right
        (fun e (eqs, vars, l) ->
          let eqs', vars, e = aux_expr vars e false in
          eqs' @ eqs, vars, (e :: l))
        l ([], vars, []) in
      eqs, vars, ETuple (t, l)
    | EApp (t, n, e) ->
      let eqs, vars, e = aux_expr vars e false in
      eqs, vars, EApp (t, n, e)
    | ETriOp (_, TOp_if, _, _, _) ->
        raise (PassExn "There should no longer be any condition.")
    | EWhen (t, e, e') ->
      let eqs, vars, e = aux_expr vars e false in
      let eqs', vars, e' = aux_expr vars e' false in
      eqs @ eqs', vars, EWhen (t, e, e')
    | ETriOp (t, TOp_merge, c, e, e') ->
      begin
        if toplevel
          then
            begin
            let eqs, vars, c = aux_expr vars c false in
            let eqs', vars, e = aux_expr vars e false in
            let eqs'', vars, e' = aux_expr vars e' false in
            eqs@eqs'@eqs'', vars, ETriOp (t, TOp_merge, c, e, e')
            end
          else
            begin
            if List.length t = 1
              then
                let newvar = Format.sprintf "%s%d" varname_prefix !count in
                let newvar =
                  match List.hd t with
                  | TInt -> IVar newvar
                  | TBool -> BVar newvar
                  | TReal -> RVar newvar
                  in
                let () = incr count in
                let vars = (t @ (fst vars), newvar :: (snd vars)) in
                let eqs, vars, c = aux_expr vars c false in
                let eqs', vars, e = aux_expr vars e false in
                let eqs'', vars, e' = aux_expr vars e' false in
                ((t, [newvar]), ETriOp (t, TOp_merge, c, e, e')) :: eqs @ eqs' @ eqs'', vars, EVar (t, newvar)
              else
                raise (PassExn "Merges should only happened on unary expressions.")
            end
      end
  in
  (** For each node: *)
  let aux_merge_lin node =
    (** Loop on equations to get additional equations and variables. *)
    let eqs, vars =
      List.fold_left
        (fun (eqs, vars) (patt, expr) ->
          let eqs', vars, expr = aux_expr vars expr true in
          (patt, expr) :: eqs' @ eqs, vars)
        ([], node.n_local_vars) node.n_equations
      in
    Some { node with n_local_vars = vars; n_equations = eqs }
  in
  node_pass aux_merge_lin



(** [pass_if_removal] replaces the `if` construct with `when` and `merge` ones.
  *
  *     [x1, ..., xn = if c then e_l else e_r;]
  * is replaced by:
  *     (t1, ..., tn) = e_l;
  *     (u1, ..., un) = e_r;
  *     (v1, ..., vn) = (t1, ..., tn) when c;
  *     (w1, ..., wn) = (u1, ..., un) when (not c);
  *     (x1, ..., xn) = merge c (v1, ..., vn) (w1, ..., wn);
  *
  * Note that the first two equations (before the use of when) is required in
  * order to have the expressions active at each step.
  *)
let pass_if_removal verbose debug =
  let varcount = ref 0 in (** new variables are called «_ifrem[varcount]» *)
  (** Makes a pattern (t_varlist) of fresh variables matching the type t *)
  let make_patt t: t_varlist =
    (t, List.fold_right
      (fun ty acc ->
        let nvar: ident = Format.sprintf "_ifrem%d" !varcount in
        let nvar =
          match ty with
          | TInt -> IVar nvar
          | TReal -> RVar nvar
          | TBool -> BVar nvar
          in
        incr varcount;
        nvar :: acc)
      t [])
  in
  (** If a tuple contains a single element, it should not be. *)
  let simplify_tuple t =
    match t with
    | ETuple (t, [elt]) -> elt
    | _ -> t
  in
  (** For each equation, build a list of equations and a new list of local
    * variables as well as an updated version of the original equation. *)
  let rec aux_eq vars eq: t_eqlist * t_varlist * t_equation =
    let patt, expr = eq in
    match expr with
    | EConst _ | EVar   _ -> [], vars, eq
    | EMonOp (t, op, e) ->
        let eqs, vars, (patt, e) = aux_eq vars (patt, e) in
        eqs, vars, (patt, EMonOp (t, op, e))
    | EBinOp (t, op, e, e') ->
        let eqs, vars, (_, e) = aux_eq vars (patt, e) in
        let eqs', vars, (_, e') = aux_eq vars (patt, e') in
        eqs @ eqs', vars, (patt, EBinOp (t, op, e, e'))
    | ETriOp (t, TOp_if, e, e', e'') ->
        let eqs, vars, (_, e) = aux_eq vars (patt, e) in
        let eqs', vars, (_, e') = aux_eq vars (patt, e') in
        let eqs'', vars, (_, e'') = aux_eq vars (patt, e'') in
        let patt_l: t_varlist = make_patt t in
        let patt_r: t_varlist = make_patt t in
        let patt_l_when: t_varlist = make_patt t in
        let patt_r_when: t_varlist = make_patt t in
        let expr_l: t_expression =
          simplify_tuple
          (ETuple
            (fst patt_l, List.map (fun v -> EVar (type_var v, v)) (snd patt_l)))
          in
        let expr_r: t_expression =
          simplify_tuple
          (ETuple
            (fst patt_r, List.map (fun v -> EVar (type_var v, v)) (snd patt_r)))
          in
        let expr_l_when: t_expression =
          simplify_tuple
          (ETuple
            (fst patt_l_when, List.map (fun v -> EVar (type_var v, v))
              (snd patt_l_when)))
          in
        let expr_r_when: t_expression =
          simplify_tuple
          (ETuple
            (fst patt_r_when, List.map (fun v -> EVar (type_var v, v))
              (snd patt_r_when)))
          in
        let equations: t_eqlist =
          [(patt_l, e');
            (patt_r, e'');
            (patt_l_when,
              EWhen (t, expr_l, e));
            (patt_r_when,
                EWhen (t,
                  expr_r,
                  (EMonOp (type_exp e, MOp_not, e))))]
            @ eqs @ eqs' @eqs'' in
        let vars: t_varlist =
          varlist_concat
            vars
            (varlist_concat patt_l_when (varlist_concat patt_r_when
            (varlist_concat patt_r patt_l))) in
        let expr =
          ETriOp (t, TOp_merge, e, expr_l_when, expr_r_when) in
        equations, vars, (patt, expr)
    | ETriOp (t, op, e, e', e'') ->
        let eqs, vars, (_, e) = aux_eq vars (patt, e) in
        let eqs', vars, (_, e') = aux_eq vars (patt, e') in
        let eqs'', vars, (_, e'') = aux_eq vars (patt, e'') in
        eqs @ eqs' @ eqs'', vars, (patt, ETriOp (t, op, e, e', e''))
    | EComp  (t, op, e, e') ->
        let eqs, vars, (_, e) = aux_eq vars (patt, e) in
        let eqs', vars, (_, e') = aux_eq vars (patt, e') in
        eqs @ eqs', vars, (patt, EComp (t, op, e, e'))
    | EWhen  (t, e, e') ->
        let eqs, vars, (_, e) = aux_eq vars (patt, e) in
        let eqs', vars, (_, e') = aux_eq vars (patt, e') in
        eqs @ eqs', vars, (patt, EWhen (t, e, e'))
    | EReset (t, e, e') ->
        let eqs, vars, (_, e) = aux_eq vars (patt, e) in
        let eqs', vars, (_, e') = aux_eq vars (patt, e') in
        eqs @ eqs', vars, (patt, EReset (t, e, e'))
    | ETuple (t, l) ->
        let eqs, vars, l, _ =
          List.fold_right
            (fun e (eqs, vars, l, remaining_patt) ->
              let patt_l, patt_r = split_patt remaining_patt e in
              let eqs', vars, (_, e) = aux_eq vars (patt_l, e) in
              eqs' @ eqs, vars, (e :: l), patt_r)
            l ([], vars, [], patt) in
          eqs, vars, (patt, ETuple (t, l))
    | EApp   (t, n, e) ->
        let eqs, vars, (_, e) = aux_eq vars (patt, e) in
        eqs, vars, (patt, EApp (t, n, e))
  in
  (** For each node, apply the previous function to all equations. *)
  let aux_if_removal node =
    let new_equations, new_locvars =
      List.fold_left
        (fun (eqs, vars) eq ->
          let eqs', vars, eq = aux_eq vars eq in
          eq :: eqs' @ eqs, vars)
        ([], node.n_local_vars) node.n_equations
      in
    Some { node with n_equations = new_equations; n_local_vars = new_locvars }
  in
  node_pass aux_if_removal



(** [pass_linearization_reset] makes sure that all reset constructs in the program
  * are applied to functions.
  * This is required, since the reset construct is translated into resetting the
  * function state in the final C code. *)
let pass_linearization_reset verbose debug =
  (** [node_lin] linearises a single node. *)
  let node_lin (node: t_node): t_node option =
    (** [reset_aux_expression] takes an expression and returns:
      *   - a list of additional equations
      *   - the new list of local variables
      *   - an updated version of the original expression *)
    let rec reset_aux_expression vars expr: t_eqlist * t_varlist * t_expression =
      match expr with
      | EVar _ -> [], vars, expr
      | EMonOp (t, op, e) ->
          let eqs, vars, e = reset_aux_expression vars e in
          eqs, vars, EMonOp (t, op, e)
      | EBinOp (t, op, e, e') ->
          let eqs, vars, e = reset_aux_expression vars e in
          let eqs', vars, e' = reset_aux_expression vars e' in
          eqs @ eqs', vars, EBinOp (t, op, e, e')
      | ETriOp (t, op, e, e', e'') ->
          let eqs, vars, e = reset_aux_expression vars e in
          let eqs', vars, e' = reset_aux_expression vars e' in
          let eqs'', vars, e'' = reset_aux_expression vars e'' in
          eqs @ eqs' @ eqs'', vars, ETriOp (t, op, e, e', e'')
      | EComp  (t, op, e, e') ->
          let eqs, vars, e = reset_aux_expression vars e in
          let eqs', vars, e' = reset_aux_expression vars e' in
          eqs @ eqs', vars, EComp (t, op, e, e')
      | EWhen  (t, e, e') ->
          let eqs, vars, e = reset_aux_expression vars e in
          let eqs', vars, e' = reset_aux_expression vars e' in
          eqs @ eqs', vars, EWhen (t, e, e')
      | EReset (t, e, e') ->
          (
            match e with
              | EApp (t_app, n_app, e_app) ->
                let eqs, vars, e = reset_aux_expression vars e in
                eqs, vars, EReset (t, e, e')
              | e -> reset_aux_expression vars e
          )
      | EConst _ -> [], vars, expr
      | ETuple (t, l) ->
          let eqs, vars, l = List.fold_right
            (fun e (eqs, vars, l) ->
              let eqs', vars, e = reset_aux_expression vars e in
              eqs' @ eqs, vars, (e :: l))
            l ([], vars, []) in
          eqs, vars, ETuple (t, l)
      | EApp (t, n, e) ->
          let eqs, vars, e = reset_aux_expression vars e in
          eqs, vars, EApp (t, n, e)
      in
    (** Applies the previous function to the expressions of every equation. *)
    let new_equations, new_locvars =
      List.fold_left
        (fun (eqs, vars) (patt, expr) ->
          let eqs', vars, expr = reset_aux_expression vars expr in
          (patt, expr)::eqs' @ eqs, vars)
        ([], node.n_local_vars)
        node.n_equations
      in
    Some { node with n_local_vars = new_locvars; n_equations = new_equations }
  in
  node_pass node_lin



(** [pass_linearization_pre] makes sure that all pre constructs in the program
  * are applied to variables.
  * This is required, since the pre construct is translated into a variable in
  * the final C code. *)
let pass_linearization_pre verbose debug =
  (** [node_lin] linearises a single node. *)
  let node_lin (node: t_node): t_node option =
    (** [pre_aux_expression] takes an expression and returns:
      *   - a list of additional equations
      *   - the new list of local variables
      *   - an updated version of the original expression *)
    let rec pre_aux_expression vars expr: t_eqlist * t_varlist * t_expression =
      match expr with
      | EVar _ -> [], vars, expr
      | EMonOp (t, op, e) ->
          begin
          match op, e with
          | MOp_pre, EVar _ ->
              let eqs, vars, e = pre_aux_expression vars e in
              eqs, vars, EMonOp (t, op, e)
          | MOp_pre, _ ->
              let eqs, vars, e = pre_aux_expression vars e in
              let nvar: string = fresh_var_name vars 6 in
              let nvar = match t with
                          | [TInt]  -> IVar nvar
                          | [TBool] -> BVar nvar
                          | [TReal] -> RVar nvar
                          | _ -> failwith "Should not happened. (pass_linearization_pre)" in
              let neq_patt: t_varlist = (t, [nvar]) in
              let neq_expr: t_expression = e in
              let vars = varlist_concat (t, [nvar]) vars in
              (neq_patt, neq_expr) :: eqs, vars, EMonOp (t, MOp_pre, EVar (t, nvar))
          | _, _ ->
              let eqs, vars, e = pre_aux_expression vars e in
              eqs, vars, EMonOp (t, op, e)
          end
      | EBinOp (t, op, e, e') ->
          let eqs, vars, e = pre_aux_expression vars e in
          let eqs', vars, e' = pre_aux_expression vars e' in
          eqs @ eqs', vars, EBinOp (t, op, e, e')
      | ETriOp (t, op, e, e', e'') -> (** Do we always want a new var here? *)
          let eqs, vars, e = pre_aux_expression vars e in
          let nvar: string = fresh_var_name vars 6 in
          let nvar: t_var = BVar nvar in
          let neq_patt: t_varlist = ([TBool], [nvar]) in
          let neq_expr: t_expression = e in
          let vars = varlist_concat vars (neq_patt) in
          let eqs', vars, e' = pre_aux_expression vars e' in
          let eqs'', vars, e'' = pre_aux_expression vars e'' in
          (neq_patt, neq_expr) :: eqs @ eqs' @ eqs'', vars, ETriOp (t, op, e, e', e'')
      | EComp  (t, op, e, e') ->
          let eqs, vars, e = pre_aux_expression vars e in
          let eqs', vars, e' = pre_aux_expression vars e' in
          eqs @ eqs', vars, EComp (t, op, e, e')
      | EWhen  (t, e, e') ->
          let eqs, vars, e = pre_aux_expression vars e in
          let eqs', vars, e' = pre_aux_expression vars e' in
          eqs @ eqs', vars, EWhen (t, e, e')
      | EReset (t, e, e') ->
          let eqs, vars, e = pre_aux_expression vars e in
          let eqs', vars, e' = pre_aux_expression vars e' in
          eqs @ eqs', vars, EReset (t, e, e')
      | EConst _ -> [], vars, expr
      | ETuple (t, l) ->
          let eqs, vars, l = List.fold_right
            (fun e (eqs, vars, l) ->
              let eqs', vars, e = pre_aux_expression vars e in
              eqs' @ eqs, vars, (e :: l))
            l ([], vars, []) in
          eqs, vars, ETuple (t, l)
      | EApp   (t, n, e) ->
          let eqs, vars, e = pre_aux_expression vars e in
          eqs, vars, EApp (t, n, e)
      in
    (** Applies the previous function to the expressions of every equation. *)
    let new_equations, new_locvars =
      List.fold_left
        (fun (eqs, vars) (patt, expr) ->
          let eqs', vars, expr = pre_aux_expression vars expr in
          (patt, expr)::eqs' @ eqs, vars)
        ([], node.n_local_vars)
        node.n_equations
      in
    Some { node with n_local_vars = new_locvars; n_equations = new_equations }
  in
  node_pass node_lin



(** [pass_linearization_tuples] transforms expressions of the form
  *     (x1, ..., xn) = (e1, ..., em);
  * into:
  *     p1 = e1;
  *       ...
  *     pm = em;
  * where flatten (p1, ..., pm) = x1, ..., xn
  *
  * Idem for tuples hidden behind merges and when:
  *     patt = (...) when c;
  *     patt = merge c (...) (...);
  *)
let pass_linearization_tuples verbose debug ast =
  (** [split_tuple] takes an equation and produces an equation list
    * corresponding to the [pi = ei;] above. *)
  let rec split_tuple (eq: t_equation): t_eqlist =
    let patt, expr = eq in
    match expr with
    | ETuple (_, expr_h :: expr_t) ->
      begin
        let t_l = type_exp expr_h in
        let patt_l, patt_r = list_select (List.length t_l) (snd patt) in
        let t_r = List.flatten (List.map type_var patt_r) in
        ((t_l, patt_l), expr_h) ::
          split_tuple ((t_r, patt_r), ETuple (t_r, expr_t))
      end
    | ETuple (_, []) -> []
    | _ -> [eq]
  in
  (** For each node, apply the previous function to all equations.
    * It builds fake equations in order to take care of tuples behind
    *  merge/when. *)
  let aux_linearization_tuples node =
    let new_equations = List.flatten
     (List.map
        (fun eq ->
          match snd eq with
          | ETuple _ -> split_tuple eq
          | EWhen (t, ETuple (_, l), e') ->
              List.map
                (fun (patt, expr) -> (patt, EWhen (type_exp expr, expr, e')))
                (split_tuple (fst eq, ETuple (t, l)))
          | ETriOp (t, TOp_merge, c, ETuple (_, l), ETuple (_, l')) ->
            begin
              if List.length l <> List.length l'
                || List.length t <> List.length (snd (fst eq))
                then raise (PassExn "Error while merging tuples.")
                else
                  fst
                    (List.fold_left2
                    (fun (eqs, remaining_patt) el er ->
                      let patt, remaining_patt = split_patt remaining_patt el in
                      let t = type_exp el in
                      (patt, ETriOp (t, TOp_merge, c, el, er))
                        :: eqs, remaining_patt)
                    ([], fst eq) l l')
            end
          | _ -> [eq])
        node.n_equations) in
    Some { node with n_equations = new_equations }
  in
  try node_pass aux_linearization_tuples ast with
  | PassExn err -> (debug err; None)



(** [pass_linearization_app] makes sure that any argument to a function is
  * either a variable, or of the form [pre _] (which will be translated as a
  * variable in the final C code. *)
let pass_linearization_app verbose debug =
  let applin_count = ref 0 in (* new variables are called «_applin[varcount]» *)
  (** [aux_expr] recursively explores the AST in order to find applications, and
    * adds the requires variables and equations. *)
  let rec aux_expr vars expr: t_eqlist * t_varlist * t_expression =
    match expr with
    | EConst _ | EVar   _ -> [], vars, expr
    | EMonOp (t, op, expr) ->
        let eqs, vars, expr = aux_expr vars expr in
        eqs, vars, EMonOp (t, op, expr)
    | EBinOp (t, op, e, e') ->
        let eqs, vars, e = aux_expr vars e in
        let eqs', vars, e' = aux_expr vars e' in
        eqs @ eqs', vars, EBinOp (t, op, e, e')
    | ETriOp (t, op, e, e', e'') ->
        let eqs, vars, e = aux_expr vars e in
        let eqs', vars, e' = aux_expr vars e' in
        let eqs'', vars, e'' = aux_expr vars e'' in
        eqs @ eqs' @ eqs'', vars, ETriOp (t, op, e, e', e'')
    | EComp  (t, op, e, e') ->
        let eqs, vars, e = aux_expr vars e in
        let eqs', vars, e' = aux_expr vars e' in
        eqs @ eqs', vars, EComp (t, op, e, e')
    | EWhen  (t, e, e') ->
        let eqs, vars, e = aux_expr vars e in
        let eqs', vars, e' = aux_expr vars e' in
        eqs @ eqs', vars, EWhen (t, e, e')
    | EReset (t, e, e') ->
        let eqs, vars, e = aux_expr vars e in
        let eqs', vars, e' = aux_expr vars e' in
        eqs @ eqs', vars, EReset (t, e, e')
    | ETuple (t, l) ->
        let eqs, vars, l =
          List.fold_right
            (fun e (eqs, vars, l) ->
              let eqs', vars, e = aux_expr vars e in
              eqs' @ eqs, vars, (e :: l))
            l ([], vars, []) in
        eqs, vars, ETuple (t, l)
    | EApp   (tout, n, ETuple (tin, l)) ->
        let eqs, vars, l =
          List.fold_right
            (fun e (eqs, vars, l) ->
              let eqs', vars, e = aux_expr vars e in
              match e with
              | EVar _ | EMonOp (_, MOp_pre, _) -> (** No need for a new var. *)
                  eqs' @ eqs, vars, (e :: l)
              | _ -> (** Need for a new var. *)
                  let ty = match type_exp e with
                           | [ty] -> ty
                           | _ -> failwith "One should not provide
                           tuples as arguments to an auxiliary node."
                           in
                  let nvar: string = Format.sprintf "_applin%d" !applin_count in
                  incr applin_count;
                  let nvar: t_var =
                    match ty with
                    | TBool -> BVar nvar
                    | TInt -> IVar nvar
                    | TReal -> RVar nvar
                    in
                  let neq_patt: t_varlist = ([ty], [nvar]) in
                  let neq_expr: t_expression = e in
                  let vars = varlist_concat neq_patt vars in
                  (neq_patt, neq_expr)::eqs'@eqs, vars, EVar([ty], nvar) :: l)
            l ([], vars, []) in
        eqs, vars, EApp (tout, n, ETuple (tin, l))
    | EApp _ -> failwith "Should not happened (parser)"
  in
  (** [aux_linearization_app] applies the previous function to every equation *)
  let aux_linearization_app node =
    let new_equations, new_locvars =
      List.fold_left
        (fun (eqs, vars) eq ->
          let eqs', vars, expr = aux_expr vars (snd eq) in
          (fst eq, expr) :: eqs' @ eqs, vars)
        ([], node.n_local_vars)
        node.n_equations
      in
    Some { node with n_local_vars = new_locvars; n_equations = new_equations }
  in
  node_pass aux_linearization_app



let pass_ensure_assignment_value verbose debug =
  let varcount = ref 0 in
  let rec aux_expr should_be_value vars expr =
    match expr with
    | EConst _ | EVar   _ -> [], vars, expr
    | EMonOp (t, op, e) ->
        let eqs, vars, e = aux_expr true vars e in
        eqs, vars, EMonOp (t, op, e)
    | EBinOp (t, op, e, e') ->
        let eqs, vars, e = aux_expr true vars e in
        let eqs', vars, e' = aux_expr true vars e' in
        eqs @ eqs', vars, EBinOp (t, op, e, e')
    | ETriOp (t, op, e, e', e'') ->
        let eqs, vars, e = aux_expr should_be_value vars e in
        let eqs', vars, e' = aux_expr should_be_value vars e' in
        let eqs'', vars, e'' = aux_expr should_be_value vars e'' in
        eqs @ eqs' @ eqs'', vars, ETriOp (t, op, e, e', e'')
    | EComp  (t, op, e, e') ->
        let eqs, vars, e = aux_expr true vars e in
        let eqs', vars, e' = aux_expr true vars e' in
        eqs @ eqs', vars, EComp (t, op, e, e')
    | EWhen  (t, e, e') ->
        let eqs, vars, e = aux_expr should_be_value vars e in
        let eqs', vars, e' = aux_expr should_be_value vars e' in
        eqs @ eqs', vars, EWhen (t, e, e')
    | EReset (t, e, e') ->
        let eqs, vars, e = aux_expr should_be_value vars e in
        let eqs', vars, e' = aux_expr should_be_value vars e' in
        eqs @ eqs', vars, EReset (t, e, e')
    | ETuple (t, l) ->
        let eqs, vars, l =
          List.fold_right
            (fun e (eqs, vars, l) ->
              let eqs', vars, e = aux_expr true vars e in
              eqs' @ eqs, vars, e :: l)
            l ([], vars, []) in
        eqs, vars, ETuple (t, l)
    | EApp   (t, n, e) ->
        let eqs, vars, e = aux_expr true vars e in
        if should_be_value
          then
            let nvar = Format.sprintf "_assignval%d" !varcount in
            incr varcount;
            let nvar: t_var =
              match t with
              | [TBool] -> BVar nvar
              | [TReal] -> RVar nvar
              | [TInt]  -> IVar nvar
              | _ ->
                failwith "An application occurring here should return a single element."
              in
            let neq_patt: t_varlist = (t, [nvar]) in
            let neq_expr: t_expression = EApp (t, n, e) in
            let vars = varlist_concat neq_patt vars in
            (neq_patt, neq_expr) :: eqs, vars, EVar (t, nvar)
          else
            eqs, vars, EApp (t, n, e)
  in
  let aux_ensure_assign_val node =
    let new_equations, vars =
      List.fold_left
        (fun (eqs, vars) eq ->
          let eqs', vars, expr = aux_expr false vars (snd eq) in
          (fst eq, expr) :: eqs' @ eqs, vars
          )
        ([], node.n_local_vars) node.n_equations
      in
    Some { node with n_equations = new_equations; n_local_vars = vars }
  in
  node_pass aux_ensure_assign_val



(** [sanity_pass_assignment_unicity] makes sure that there is at most one
  * equation defining each variable (and that no equation tries to redefine an
  * input).
  *
  * This is required, since the equations are not ordered in Lustre. *)
let sanity_pass_assignment_unicity verbose debug : t_nodelist -> t_nodelist option =
  (** For each node, test the node. *)
  let aux (node: t_node) : t_node option =
    let incr_aux h n =
      match Hashtbl.find_opt h n with
      | None -> raise (PassExn "should not happened.")
      | Some num -> Hashtbl.replace h n (num + 1)
      in
    let incr_eq h (((_, patt), _): t_equation) =
      List.iter (fun v -> incr_aux h (name_of_var v)) patt
      in
    let rec incr_eqlist h = function
      | [] -> ()
      | eq :: eqs -> (incr_eq h eq; incr_eqlist h eqs)
      in
    let incr_branch h (State (_, eqs, _, _): t_state) = incr_eqlist h eqs in
    let incr_automata h ((_, states): t_automaton) =
      let acc = Hashtbl.copy h in
        List.iter
          (fun st ->
            let h_st = Hashtbl.copy h in
            incr_branch h_st st;
            Hashtbl.iter
              (fun varname num' ->
                match Hashtbl.find_opt acc varname with
                | None -> failwith "no!"
                | Some num -> Hashtbl.replace acc varname (Int.max num num')
                ) h_st) states;
          Hashtbl.iter (fun v n -> Hashtbl.replace h v n) acc
        in
    let check_now h : bool=
      Hashtbl.fold
        (fun varname num old_res ->
          if num > 1
            then (verbose (Format.asprintf "%s initialized twice!" varname); false)
            else old_res) h true
      in
    (*let purge_initialized h =
      Hashtbl.iter
        (fun varname num ->
          if num > 0
            then (verbose (Format.asprintf "Purging %s" varname); Hashtbl.remove h varname)
            else ()) h
      in*)
    let h = Hashtbl.create Config.maxvar in
    let add_var n v =
      match v with
      | IVar s -> Hashtbl.add h s n
      | BVar s -> Hashtbl.add h s n
      | RVar s -> Hashtbl.add h s n
    in
    let add_var_in = add_var 1 in
    let add_var_loc = add_var 0 in
    List.iter add_var_loc (snd node.n_outputs);
    List.iter add_var_loc (snd node.n_local_vars);
    List.iter add_var_in (snd node.n_inputs);
    (** Usual Equations *)
    incr_eqlist h node.n_equations;
    if check_now h = false
      then None
      else
        begin
          List.iter (* 0. *) (incr_automata h) node.n_automata;
          if check_now h
            then Some node
            else None
        end
    (** never purge -> failwith never executed! purge_initialized h; *)
  in
  node_pass aux

let rec tpl debug ((pat, exp): t_equation) =
  match exp with
  | ETuple (_, hexps :: texps) ->
      debug "An ETuple has been recognized, inlining...";
      let p1, p2 =
        list_select
          (List.length (type_exp hexps))
          (snd pat) in
      let t1 = List.flatten (List.map type_var p1) in
      let t2 = List.flatten (List.map type_var p2) in
      ((t1, p1), hexps)
        :: (tpl debug ((t2, p2),
            ETuple (List.flatten (List.map type_exp texps), texps)))
  | ETuple (_, []) -> []
  | _ -> [(pat, exp)]



(** [pass_eq_reordering] orders the equation such that an equation should not
  * appear before all equations defining the variables it depends on are. *)
let pass_eq_reordering verbose debug ast =
  (** [pick_equations] takes a list of equations and initialized variables.
    * it either returns:
    *  - a list of equations in a correct order
    *  - nothing *)
  let rec pick_equations init_vars eqs remaining_equations =
    match remaining_equations with
    | [] -> (* There are no equations left to order: we are done. *) Some eqs
    | _ ->
      begin
        (** The filter below provides the equations whose dependencies have
          * already been defined *)
        match List.filter
                (fun (patt, expr) ->
                  List.for_all
                    (fun v -> List.mem v init_vars)
                    (vars_of_expr expr))
                remaining_equations with
        | [] -> (** There are remaining equations to order, but none whose all
                  * dependencies have already been defined yet.*)
          raise (PassExn "[equation ordering] The equations cannot be ordered.")
        | h :: t -> (** [h :: t] is a list of equations whose dependencies have
                      * all already been defined. *)
            let init_vars = (* new set of initialized variables *)
              List.fold_left
                (fun acc vs ->
                  (vars_of_patt (fst vs)) @ acc) init_vars (h :: t) in
            (** The filter below removes the equation  of [h :: t] to those to
              * the list of equations to be ordered *)
            pick_equations init_vars (eqs @ (h :: t))
              (List.filter
                (fun eq -> List.for_all (fun e -> eq <> e) (h :: t)) remaining_equations)
      end
  in
  (* main function of the (node-)pass. *)
  let node_eq_reorganising  (node: t_node): t_node option =
    let init_vars = List.map name_of_var (snd node.n_inputs) in
    try
      begin
      match pick_equations init_vars [] node.n_equations with
      | None -> None
      | Some eqs -> Some { node with n_equations = eqs }
      end
    with PassExn err -> (verbose err; None)
  in
  (** iterate the pass over the nodes of the program. *)
  node_pass node_eq_reorganising ast



let pass_typing verbose debug ast =
  let htbl = Hashtbl.create (List.length ast) in
  let () = debug "[typing verification]" in
  let () = List.iter
    (fun n -> Hashtbl.add htbl n.n_name (fst n.n_inputs, fst n.n_outputs))
    ast in
  let rec check_varlist vl =
    let t = fst vl in
    let l = snd vl in
    match t, l with
    | [], [] -> true
    | TInt  :: t, IVar _ :: l -> check_varlist (t, l)
    | TBool :: t, BVar _ :: l -> check_varlist (t, l)
    | TReal :: t, RVar _ :: l -> check_varlist (t, l)
    | _, _ -> false
    in
  let rec check_expr vl = function
    | EVar   (t, v) -> t = type_var v
    | EMonOp (t, _, e) -> check_expr vl e && type_exp e = t
    | EBinOp (t, _, e, e') -> check_expr vl e && check_expr vl e'
                              && t = type_exp e && t = type_exp e'
    | ETriOp (t, _, c, e, e') ->
        check_expr vl e && check_expr vl e' && check_expr vl c
        && type_exp c = [TBool] && type_exp e = t && type_exp e' = t
    | EComp  (t, _, e, e') ->
        check_expr vl e && check_expr vl e' && t = [TBool]
    | EWhen  (t, e, e') ->
        check_expr vl e && check_expr vl e'
        && t = type_exp e && [TBool] = type_exp e'
    | EReset (t, e, e') ->
        check_expr vl e && check_expr vl e' && t = type_exp e && type_exp e' = [TBool]
    | EConst (t, c) -> type_const c = t
    | ETuple (t, l) ->
        List.for_all (check_expr vl) l
        && t = List.flatten (List.map type_exp l)
    | EApp   (t, n, e) ->
        check_expr vl e && t = (fst n.n_outputs) && type_exp e = (fst n.n_inputs)
  in
  let check_equation vl ((peq, eeq): t_equation) =
    if check_varlist peq
      then
        if check_expr vl eeq
          then fst peq = type_exp eeq
          else false
      else false
  in
  let rec check_equations vl = function
    | [] -> true
    | eq :: eqs ->
        if check_equation vl eq
          then check_equations vl eqs
          else false
  in
  let check_one_node node =
    check_varlist (node.n_inputs)
    && check_varlist (node.n_outputs)
    && check_varlist (node.n_local_vars)
    && check_equations
        (varlist_concat node.n_inputs
          (varlist_concat node.n_outputs node.n_local_vars))
        node.n_equations
    in
  let rec aux = function
    | [] -> Some ast
    | n :: nodes ->
        if check_one_node n
          then aux nodes
          else None
  in aux ast

let check_automata_validity verbose debug = 
  let check_automaton_branch_vars automaton = 
    let (init, states) = automaton in
    let left_side = Hashtbl.create 10 in

    let rec init_left_side eqlist = match eqlist with
    | [] -> ()
    | (varlist, exp)::q -> 
        begin
          Hashtbl.add left_side varlist true;
          init_left_side q;
        end
    in
    let check_state s = match s with
    | State(name, eqs, cond, next) ->
        List.for_all (fun (varlist, exp) -> (Hashtbl.mem left_side varlist)) eqs
    in
    begin
    match init with | State(name, eqs, cond, next) -> init_left_side eqs;
    let validity = List.for_all (fun s -> (check_state s)) states in
    if not validity then
      raise (PassExn "Automaton branch has different variables assignment in different branches")
    end
  in
  let aux node = 
    try
    List.iter check_automaton_branch_vars node.n_automata;
    Some node
    with
    | PassExn err -> (verbose err; None)
  in
  node_pass aux

let automaton_translation debug automaton =

  let id = create_automaton_id () in
  let automat_name = create_automaton_name id in
  let new_vars = Hashtbl.create Config.maxvar in
  let var_seen = Hashtbl.create Config.maxvar in
  let var_merged = Hashtbl.create Config.maxvar in
  let state_to_int = Hashtbl.create Config.maxvar in
  let default_constant ty =
    let defaults ty = match ty with
    | TInt  -> EConst([ty], CInt(0))
    | TBool -> EConst([ty], CBool(false))
    | TReal -> EConst([ty], CReal(0.0))
    in
    match ty with
    | [TInt]  -> EConst(ty, CInt(0))
    | [TBool] -> EConst(ty, CBool(false))
    | [TReal] -> EConst(ty, CReal(0.0))
    | _ -> ETuple(ty, List.map defaults ty)
  in
  let get_branch_var var branch = 
      Format.asprintf "_%s_%s_%d" var branch id in
  let create_var_name var branch ty = 
      let s = get_branch_var var branch in
      Hashtbl.replace new_vars s (var, branch, ty);
      Hashtbl.add var_seen var (s, branch, ty);
      s
  in
  let get_branch_bool branch = 
    Format.asprintf "_b_%s_%d" branch id in
  let create_branch_name branch = 
      let s = get_branch_bool branch in
      Hashtbl.replace new_vars s ("", branch, TBool);
      s
  in
  let create_merge_var varname branch ty = 
      let s = Format.asprintf "_%s_%s_merge_%d" varname branch id in
      Hashtbl.replace new_vars s (varname, branch, ty);
      s
  in
  let create_next_var branch = 
      let s = Format.asprintf "_next_%s_%d" branch id in
      Hashtbl.replace new_vars s ("", branch, TInt);
      s
  in
  let create_type_var_name var branch = match var with
  | BVar(name) -> create_var_name name branch TBool
  | IVar(name) -> create_var_name name branch TInt
  | RVar(name) -> create_var_name name branch TReal
  in
  let to_var varname ty = match ty with
  | TInt  -> IVar(varname)
  | TBool -> BVar(varname)
  | TReal -> RVar(varname)
  in
  let rec init_state_translation states c = match states with
  | [] -> ()
  | State(name, _, _, _)::q -> 
      Hashtbl.replace state_to_int name c; (init_state_translation q (c+1))
  in
  let rec find_state name = 
    match Hashtbl.find_opt state_to_int name with
    | None -> failwith "Unknown state in automaton"
    | Some v -> v
  in
  let translate_eqlist eqlist branch = 
      let aux eq = 
          let ((ty, vlist), expr ) = eq in 
            ((ty, List.map2 (fun l ty -> to_var (create_type_var_name l branch) ty ) vlist ty ), 
                EWhen(type_exp expr, expr, EVar([TBool], to_var (get_branch_bool branch) TBool ))) 
      in
      List.map aux eqlist
  in
  let rec next_construct exprs nexts = match exprs, nexts with
  | [], [] -> EConst([TInt], CInt(1))
  | e::exprs, n::nexts -> ETriOp([TInt], TOp_if, e, EConst([TInt], CInt(find_state n)), next_construct exprs nexts)
  | _, _ -> failwith "Automata translation: next construct: should not happen"
  in
  let state_translation state = 
      match state with
      | State( name, equations, expr, next ) ->
        let b = create_branch_name name in
        let eqs = translate_eqlist equations name in
        let bool_expr = EComp([TBool], COp_eq, EVar([TInt], to_var automat_name TInt), EConst([TInt], CInt(find_state name))) in
        let next_expr = EWhen([TInt], next_construct expr next, EVar([TBool], to_var (get_branch_bool name) TBool)) in
        (([TBool], [to_var b TBool]), bool_expr)::(([TInt], [to_var (create_next_var name) TInt]), next_expr)::eqs
  in
  let rec iter_states states = 
      match states with
      | [] -> []
      | s::q -> (state_translation s) @ (iter_states q)
  in
  let combine_one_var varname ty = 
      let default = default_constant [ty] in
      let rec merge_branches previous branchlist = match branchlist with
      | [] -> Hashtbl.replace var_merged varname true ; [(([ty], [to_var varname ty]), previous)]
      | (var, branch, ty2)::q -> 
              let merge_var = create_merge_var varname branch ty in
              (([ty], [to_var merge_var ty]), 
        ETriOp([ty], TOp_merge, EVar([TBool], to_var (get_branch_bool branch) TBool), EVar([ty], to_var var ty), 
            EWhen([ty], previous, EMonOp([TBool], MOp_not, EVar([TBool], to_var (get_branch_bool branch) TBool))))) 
              :: ( merge_branches (EVar([ty], to_var merge_var ty2)) q )
      in
      let l = Hashtbl.find_all var_seen varname in
      merge_branches default l
      
  in
  let combine_var varname = 
      if Hashtbl.mem var_merged varname then [] 
      else let (_, _, ty) = Hashtbl.find var_seen varname in combine_one_var varname ty
  in
  let rec merge_state states = match states with
  | [] -> EConst([TInt], CInt(1))
  | State(name, _, _, _)::q -> 
          let end_state = merge_state q in
          let bool_var = EVar([TBool], to_var (get_branch_bool name) TBool) in
          ETriOp([TInt], TOp_merge, bool_var, EVar([TInt], to_var (create_next_var name) TInt),
            EWhen([TInt], end_state, EMonOp([TBool], MOp_not, bool_var)))
  in
  let extract_new_var (varname, (_, _, ty)) = to_var varname ty in
  let rec build_type varlist = match varlist with
  |IVar(_)::q -> TInt::build_type q
  |BVar(_)::q -> TBool::build_type q
  |RVar(_)::q -> TReal::build_type q
  |[] -> []
  in

  let init, states = automaton in
  init_state_translation states 1;
  let transition_eq = (([TInt], [IVar(automat_name)]), EBinOp([TInt], BOp_arrow, EConst([TInt], CInt(1)), EMonOp([TInt], MOp_pre, merge_state states))) in
  let state_eqs = (iter_states states) in
  let new_eqs = state_eqs @ (List.flatten (List.map combine_var (List.of_seq (Hashtbl.to_seq_keys var_seen)))) in
  let new_vars = List.map extract_new_var (List.of_seq (Hashtbl.to_seq new_vars)) in
  (transition_eq)::new_eqs, (TInt::(build_type new_vars), IVar(automat_name)::new_vars)

let automata_translation_pass verbose debug = 
    let rec iter_automata autolist = match autolist with
    | [] -> [], ([], [])
    | a::q -> let (eqs, (ty, vars)) = automaton_translation debug a in
                let (eqs_end, (ty_end, vars_end)) = iter_automata q in
                eqs@eqs_end, (ty@ty_end, vars@vars_end)
    in
    let aux node = 
        try
            let eqs, (ty, vars) = iter_automata node.n_automata in
            let (ty_old, vars_old) = node.n_local_vars in
            Some { node with n_local_vars = (ty@ty_old, vars@vars_old); n_equations = node.n_equations@eqs; n_automata = []}
        with
        |PassExn err -> (verbose err; None)
    in
  node_pass aux

let clock_unification_pass verbose debug ast = 

  let known_clocks = Hashtbl.create 100 in
  let used = Hashtbl.create 100 in (*keep track of variables that appear on right side of equation*)
  let changed = ref false in

  let rec count_not e acc = match e with
    | EVar([TBool], var) -> acc, e
    | EConst([TBool], cons) -> acc, e
    | EMonOp([TBool], MOp_not, e) -> count_not e (acc + 1)
    | _ -> raise (PassExn "verify_when failure")
  in

  let verify_when e1 e2 =
      let n1, var1 = count_not e1 0
      and n2, var2 = count_not e2 0 in
      if n1 mod 2 <> n2 mod 2 || var1 <> var2 then
          raise (PassExn "clock unification failure")
  in

  let get_var_name var = match var with
  | RVar(name)
  | BVar(name)
  | IVar(name) -> name
  in

  let rec clk_to_string clk = match clk with
  | Base -> "Base"
  | Unknown -> "Unknown"
  | On(clk, exp) -> 
          let n, var = count_not exp 0 in
          let s = if n mod 2 = 1 then "not " else "" in
          let v = match var with |EVar(_, var) -> get_var_name var | EConst(_, CBool(false)) -> "false" |_ -> "true" in
          (clk_to_string clk) ^ " on " ^ s ^ v
  in

  let add_clock var clock = 
      match Hashtbl.find known_clocks var with
      | Unknown -> changed := true; (debug ("Found clock for "^(get_var_name var)^": "^(clk_to_string clock))); Hashtbl.replace known_clocks var clock
      | c when c = clock -> ()
      | c -> raise (PassExn ("Clock conflict "^(get_var_name var) ^" "^(clk_to_string c) ^ " " ^ (clk_to_string clock)))
  in

  let rec update_clock exp clk = match exp with
  | EConst(_, _) -> ()
  | EVar(_, var) -> add_clock var clk; Hashtbl.replace used var var
  | EMonOp(_, _, e) -> update_clock e clk

  | EComp(_, _, e1, e2)
  | EReset(_, e1, e2)
  | EBinOp(_, _, e1, e2) -> update_clock e1 clk; update_clock e2 clk
  | ETriOp(_, TOp_merge, e1, e2, e3) ->
          update_clock e1 clk;
          update_clock e2 (On(clk, e1));
          update_clock e3 (On(clk, EMonOp([TBool], MOp_not, e1)))
  | ETriOp(_, TOp_if, e1, e2, e3) ->
          (* The 3 expressions should have the same clock *)
          begin
          update_clock e1 clk;
          update_clock e2 clk;
          update_clock e3 clk
          end
  | ETuple(_, explist) -> List.iter (fun e -> update_clock e clk) explist
  | EApp(_, node, e) -> update_clock e clk
  | EWhen(_, e1, e2) -> 
      match clk with
      | On(clk2, e) -> verify_when e e2; update_clock e1 clk2
      | _ -> raise (PassExn "Clock unification failure: when")
      in

  let rec propagate_clock eqs =
    let rec step ((ty, vars), exp)= match vars with
    | [] -> ()
    | v::t -> let clk = Hashtbl.find known_clocks v in
      begin
      if clk <> Unknown then update_clock exp clk
      else ();
      step ((ty, t), exp)
      end
    in
    List.iter step eqs
  in
  
  let rec iter_til_stable eqs = 
    changed := false;
    propagate_clock eqs;
    if !changed then
        iter_til_stable eqs
  in

  let check_unification node =
    let (_, node_inputs) = node.n_inputs in
    let rec check_vars_aux acc = match acc with
    | [(v, c)] -> if c = Unknown && (Hashtbl.mem used v) then raise (PassExn ("Clock unification failure: Unkwown clock for "^(get_var_name v))) else c
    | (v, t)::q -> let c = check_vars_aux q in
        if c <> t then raise (PassExn "Clock unification failure: Non homogeneous equation") else c
    | [] -> raise (PassExn "Clock unification failure: empty equation")
    in
    let rec check_vars ((ty, vars), exp) acc = match vars with
    | [] -> let _ = check_vars_aux acc in ()
    | v::t -> check_vars ((ty, t), exp) ((v, Hashtbl.find known_clocks v)::acc)
    in
    let rec check_inputs inputs = match inputs with
    | [] -> ()
    | i::q -> let c = Hashtbl.find known_clocks i in
        match c with
        | On(_, e) -> let _, var = count_not e 0 in 
            begin
            match var with
            | EConst(_, _) -> ()
            | EVar(_, var) -> if not (List.mem var node_inputs) then raise (PassExn "Clock unification failure: input clock depends on non input clock")
                else check_inputs q
            | _ -> failwith "Should not happen. (clock_unification)"
            end
        | _ -> check_inputs q
    in
    (*Check that all variables used have a clock
       and that inputs clocks do not depend on local vars or outputs*)
    List.iter (fun eq -> check_vars eq []) node.n_equations;
    check_inputs node_inputs;
  in


  let compute_clock_node n = 
    begin
      Hashtbl.clear known_clocks;
      List.iter (fun v -> Hashtbl.replace known_clocks v Unknown) (
        snd n.n_inputs); (* Initializing inputs to Unknown clock *)
      List.iter (fun v -> Hashtbl.replace known_clocks v Unknown) (
        snd n.n_local_vars); (* Initializing local variables to Unknown clock *)
      List.iter (fun v -> Hashtbl.replace known_clocks v Base) (
        snd n.n_outputs); (* Initializing outputs to base clock *)
      try
        begin
          iter_til_stable n.n_equations;
          (* catch potential errors and test for unification *)
          check_unification n;
          Some n
        end
      with
      | PassExn err -> (verbose err; None)
    end
  in node_pass compute_clock_node ast
