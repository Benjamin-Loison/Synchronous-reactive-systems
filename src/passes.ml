(** This file contains simplification passes for our Lustre-like AST *)

open Ast

(** [node_pass] is an auxiliary function used to write passes: it will iterate
  * the function passed as argument on all the nodes of the program *)
let node_pass f ast: t_nodelist option =
  Utils.list_map_option f ast

(** [equation_pass] is an auxiliary function used to write passes: it will
  * iterate the function passed as argument on all the equations of the
  * program *)
let equation_pass f ast: t_nodelist option =
  let aux (node: t_node): t_node option =
    match Utils.list_map_option f node.n_equations with
    | None -> None
    | Some eqs -> Some {n_name         = node.n_name;
                        n_inputs       = node.n_inputs;
                        n_outputs      = node.n_outputs;
                        n_local_vars   = node.n_local_vars;
                        n_equations    = eqs;
                        n_automata     = node.n_automata;
                        n_inputs_type  = node.n_inputs_type;
                        n_outputs_type = node.n_outputs_type;
                       }
    in
  node_pass aux ast

let expression_pass f: t_nodelist -> t_nodelist option =
  let aux (patt, expr) =
    match f expr with
    | None -> None
    | Some expr -> Some (patt, expr)
  in
  equation_pass aux

let pre2vars =
  let rec all_pre expr =
    match expr with
    | EMonOp (ty, MOp_pre, expr) -> all_pre expr
    | EMonOp _ -> false
    | EVar _ -> true
    | _ -> false
  in
  let rec pre_push expr : t_expression =
    match expr with
    | EVar _ -> EMonOp (Utils.type_exp expr, MOp_pre, expr)
    | EConst _ -> expr (** pre(c) = c for any constant c *)
    | EMonOp (ty, mop, expr) ->
      begin
        match mop with
        | MOp_pre ->
          if all_pre expr
            then EMonOp (ty, mop, EMonOp (ty, mop, expr))
            else pre_push (pre_push expr)
        | _ -> EMonOp (ty, mop, pre_push expr)
      end
    | EBinOp (ty, bop, expr, expr') ->
        let expr = pre_push expr in let expr' = pre_push expr' in
        EBinOp (ty, bop, expr, expr')
    | ETriOp (ty, top, expr, expr', expr'') ->
        let expr = pre_push expr in let expr' = pre_push expr' in
        let expr'' = pre_push expr'' in
        ETriOp (ty, top, expr, expr', expr'')
    | EComp  (ty, cop, expr, expr') ->
        let expr = pre_push expr in let expr' = pre_push expr' in
        EComp (ty, cop, expr, expr')
    | EWhen  (ty, expr, expr') ->
        let expr = pre_push expr in let expr' = pre_push expr' in
        EWhen (ty, expr, expr')
    | EReset (ty, expr, expr') ->
        let expr = pre_push expr in let expr' = pre_push expr' in
        EReset (ty, expr, expr')
    | ETuple (ty, elist) ->
        let elist =
          List.fold_right (fun expr acc -> (pre_push expr) :: acc) elist [] in
        ETuple (ty, elist)
    | EApp   (ty, node, arg) ->
        let arg = pre_push arg in
        EApp (ty, node, arg)
    | EAuto _ -> failwith "toto"
  in
  let rec aux (expr: t_expression) =
    match expr with
    | EVar   _ -> expr
    | EMonOp (ty, mop, expr) ->
      begin
        match mop with
        | MOp_pre -> pre_push expr
        | _ -> let expr = aux expr in EMonOp (ty, mop, expr)
      end
    | EBinOp (ty, bop, expr, expr') ->
        let expr = aux expr in let expr' = aux expr' in
        EBinOp (ty, bop, expr, expr')
    | ETriOp (ty, top, expr, expr', expr'') ->
        let expr = aux expr in let expr' = aux expr' in
        let expr'' = aux expr'' in
        ETriOp (ty, top, expr, expr', expr'')
    | EComp  (ty, cop, expr, expr') ->
        let expr = aux expr in let expr' = aux expr' in
        EComp (ty, cop, expr, expr')
    | EWhen  (ty, expr, expr') ->
        let expr = aux expr in let expr' = aux expr' in
        EWhen (ty, expr, expr')
    | EReset (ty, expr, expr') ->
        let expr = aux expr in let expr' = aux expr' in
        EReset (ty, expr, expr')
    | EConst (ty, c) -> EConst (ty, c)
    | ETuple (ty, elist) ->
        let elist =
          List.fold_right (fun expr acc -> (aux expr) :: acc) elist [] in
        ETuple (ty, elist)
    | EApp   (ty, node, arg) ->
        let arg = aux arg in
        EApp (ty, node, arg)
    | EAuto _ -> failwith "todo"
  in
  expression_pass (Utils.somify aux)

