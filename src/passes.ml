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

let pre2vars verbose debug =
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
  in
  expression_pass (Utils.somify aux)

let chkvar_init_unicity verbose debug : t_nodelist -> t_nodelist option =
  let aux (node: t_node) : t_node option =
    let incr_aux h n =
      match Hashtbl.find_opt h n with
      | None -> failwith "todo, should not happend."
      | Some num -> Hashtbl.replace h n (num + 1)
      in
    let incr_eq h (((_, patt), _): t_equation) =
      List.iter (fun v -> incr_aux h (Utils.name_of_var v)) patt
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
                | None -> failwith "non!"
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
    List.iter add_var_in (snd node.n_inputs);
    List.iter add_var_loc (snd node.n_outputs);
    List.iter add_var_loc (snd node.n_local_vars);


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

