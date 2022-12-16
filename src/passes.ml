(** This file contains simplification passes for our Lustre-like AST *)

open Ast
open Passes_utils
open Utils

let pre2vars verbose debug main_fn =
  let rec all_pre expr =
    match expr with
    | EMonOp (ty, MOp_pre, expr) -> all_pre expr
    | EMonOp _ -> false
    | EVar _ -> true
    | _ -> false
  in
  let rec pre_push expr : t_expression =
    match expr with
    | EVar _ -> EMonOp (type_exp expr, MOp_pre, expr)
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
  expression_pass (somify aux)

let chkvar_init_unicity verbose debug main_fn : t_nodelist -> t_nodelist option =
  let aux (node: t_node) : t_node option =
    let incr_aux h n =
      match Hashtbl.find_opt h n with
      | None -> failwith "todo, should not happened."
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

let pass_linearization verbose debug main_fn =
  let node_lin (node: t_node): t_node option =
    let new_equations = List.flatten
      begin
      List.map
        (tpl debug)
        node.n_equations
      end in
    Some
      {
        n_name = node.n_name;
        n_inputs = node.n_inputs;
        n_outputs = node.n_outputs;
        n_local_vars = node.n_local_vars;
        n_equations = new_equations;
        n_automata = node.n_automata;
      }
  in
  node_pass node_lin

let pass_eq_reordering verbose debug main_fn ast =
  let rec pick_equations init_vars eqs remaining_equations =
    match remaining_equations with
    | [] -> Some eqs
    | _ ->
      begin
        match List.filter
                (fun (patt, expr) ->
                  List.for_all
                    (fun v -> List.mem v init_vars)
                    (vars_of_expr expr))
                remaining_equations with
        | [] -> raise (PassExn "[equation ordering] The equations cannot be ordered.")
        | h :: t ->
            let init_vars =
              List.fold_left
                (fun acc vs ->
                  acc @ (vars_of_patt (fst vs))) init_vars (h :: t) in
            pick_equations init_vars (eqs@(h :: t))
              (List.filter (fun eq -> List.for_all (fun e -> eq <> e) (h :: t)) remaining_equations)
      end
    in
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
  node_pass node_eq_reorganising ast

let pass_typing verbose debug main_fn ast =
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

let check_automata_validity verbos debug main_fn = 
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
      failwith "Automaton branch has different variables assignment in different branches"
    end
  in
  let aux node = 
    List.iter check_automaton_branch_vars node.n_automata;
    Some node
  in
  node_pass aux

let automaton_translation debug automaton = 
  let gathered = Hashtbl.create 10 in
  let state_to_int = Hashtbl.create 10 in
  let add_to_table var exp state = 
    if Hashtbl.mem gathered var then
      let res = Hashtbl.find gathered var in
      Hashtbl.replace gathered var ((state, exp)::res);
    else
      Hashtbl.replace gathered var ([(state, exp)])
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

  let rec equation_pass state : t_eqlist -> unit = function
    | [] -> ()
    | (vars, exp)::q -> begin
      add_to_table vars exp state;
      equation_pass state q
    end
  in

  let flatten_state state = match state with
  | State(name, eq, cond, next) -> 
    (* Flattening is not possible
       for example a branch where x,y = 1, 2 will be unpacked
       when in another branch x, y = f(z) will not be unpacked
    *)
    (*
    let new_equations = List.flatten
      begin
      List.map
        (tpl debug)
        eq
      end in
    *)
    equation_pass name eq;
    State(name, eq, cond, next)
  in

  let rec transition_eq states s = 
    match states with
    | [] -> EVar([TInt], IVar(s))
    | State(name, eqs, cond, next)::q ->
        let name = find_state name
        and next = find_state next in
        ETriOp([TInt], TOp_if, 
          EBinOp([TBool], BOp_and, 
            EComp([TBool], COp_eq,
              EVar([TInt], IVar(s)),
              EConst([TInt], CInt(name))
            ),
            cond
          ),
          EConst([TInt], CInt(next)),
          transition_eq q s
        )
    in

  let rec translate_var s v explist = match explist with
  | [] -> EConst([TInt], CInt(0)) (* TODO *)
  | (state, exp)::q -> 
      ETriOp(Utils.type_exp exp, TOp_if,
        EComp([TBool], COp_eq, 
          EVar([TInt], IVar(s)),
          EConst([TInt], CInt(Hashtbl.find state_to_int state))
        ),
        exp,
        translate_var s v q
      )
  in

  let flatten_automaton automaton = 
    let (init, states) = automaton in
    (flatten_state init, List.map flatten_state states)
  in
  let (init, states) = flatten_automaton automaton in
  let s = create_automaton_name () in
  init_state_translation states 1;
  let exp_transition = EBinOp([TInt], BOp_arrow, EConst([TInt], CInt(1)), EMonOp([TInt], MOp_pre, transition_eq states s)) in
  let new_equations = [(([TInt], [IVar(s)]), exp_transition)] in
  Hashtbl.fold (fun var explist acc -> (var, translate_var s var explist)::acc) gathered new_equations, IVar(s)


let automata_trans_pass debug (node:t_node) : t_node option=

  let rec aux automaton = match automaton with
  | [] -> [], [], []
  | a::q -> 
      let eq, var = automaton_translation debug a
      and tail_eq, tail_var, tail_type = aux q in
      eq@tail_eq, var::tail_var, TInt::tail_type
  in

  let eqs, vars, new_ty = aux node.n_automata in
  let ty, loc_vars = node.n_local_vars in
  Some
    {
      n_name = node.n_name;
      n_inputs = node.n_inputs;
      n_outputs = node.n_outputs;
      n_local_vars = (new_ty@ty, vars@loc_vars);
      n_equations = eqs@node.n_equations;
      n_automata = []; (* not needed anymore *)
    }

let automata_translation_pass verbose debug main_fn = 
  node_pass (automata_trans_pass debug)


