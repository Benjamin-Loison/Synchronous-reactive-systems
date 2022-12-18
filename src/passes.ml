(** This file contains simplification passes for our Lustre-like AST *)

open Ast
open Passes_utils
open Utils

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

let pass_linearization_tuples verbose debug =
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
          | _ -> [eq])
        node.n_equations) in
    Some { node with n_equations = new_equations }
  in
  node_pass aux_linearization_tuples

let pass_linearization_app verbose debug =
  let applin_count = ref 0 in
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
                           | _ -> failwith "[passes.ml] One should not provide
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
    | EApp _ -> failwith "[passes.ml] Should not happened (parser)"
  in
  let aux vars eq =
    let eqs, vars, expr = aux_expr vars (snd eq) in
    (fst eq, expr) :: eqs, vars
  in
  let aux_linearization_app node =
    let new_equations, new_locvars =
      List.fold_left
        (fun (eqs, vars) eq ->
          let es, vs = aux vars eq in
          es @ eqs, vs)
        ([], node.n_local_vars)
        node.n_equations
      in
    Some { node with n_local_vars = new_locvars; n_equations = new_equations }
  in
  node_pass aux_linearization_app

let chkvar_init_unicity verbose debug : t_nodelist -> t_nodelist option =
  let aux (node: t_node) : t_node option =
    let incr_aux h n =
      match Hashtbl.find_opt h n with
      | None -> raise (PassExn "todo, should not happened.")
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

let pass_linearization_pre verbose debug =
  let node_lin (node: t_node): t_node option =
    let rec pre_aux_expression vars expr: t_eqlist * t_varlist * t_expression =
      match expr with
      | EVar _ -> [], vars, expr
      | EMonOp (t, op, e) ->
          begin
          match op with
          | MOp_pre ->
              let eqs, vars, e = pre_aux_expression vars e in
              let nvar: string = fresh_var_name vars 6 in
              let nvar = match t with
                          | [TInt]  -> IVar nvar
                          | [TBool] -> BVar nvar
                          | [TReal] -> RVar nvar
                          | _ -> failwith "Should not happened." in
              let neq_patt: t_varlist = (t, [nvar]) in
              let neq_expr: t_expression = e in
              let vars = varlist_concat (t, [nvar]) vars in
              (neq_patt, neq_expr) :: eqs, vars, EMonOp (t, MOp_pre, EVar (t, nvar))
          | _ ->
              let eqs, vars, e = pre_aux_expression vars e in
              eqs, vars, EMonOp (t, op, e)
          end
      | EBinOp (t, op, e, e') ->
          let eqs, vars, e = pre_aux_expression vars e in
          let eqs', vars, e' = pre_aux_expression vars e' in
          eqs @ eqs', vars, EBinOp (t, op, e, e')
      | ETriOp (t, op, e, e', e'') -> (** Do we always want a new var here ? *)
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
    let rec pre_aux_equation (vars: t_varlist) ((patt, expr): t_equation) =
      let eqs, vars, expr = pre_aux_expression vars expr in
      (patt, expr)::eqs, vars
      in
    let new_equations, new_locvars =
      List.fold_left
        (fun (eqs, vars) eq ->
          let es, vs = pre_aux_equation vars eq in
          es @ eqs, vs)
        ([], node.n_local_vars)
        node.n_equations
      in
    Some
      {
        n_name = node.n_name;
        n_inputs = node.n_inputs;
        n_outputs = node.n_outputs;
        n_local_vars = new_locvars;
        n_equations = new_equations;
        n_automata = node.n_automata;
      }
  in
  node_pass node_lin

let pass_eq_reordering verbose debug ast =
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

let check_automata_validity verbos debug = 
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

  let rec translate_var s v explist ty = match explist with
  | [] -> default_constant ty (* TODO *)
  | (state, exp)::q -> 
      ETriOp(Utils.type_exp exp, TOp_if,
        EComp([TBool], COp_eq, 
          EVar([TInt], IVar(s)),
          EConst([TInt], CInt(Hashtbl.find state_to_int state))
        ),
        exp,
        translate_var s v q ty
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
  Hashtbl.fold (fun var explist acc -> (var, translate_var s var explist (fst var))::acc) gathered new_equations, IVar(s)


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

let automata_translation_pass verbose debug = 
  node_pass (automata_trans_pass debug)

let clock_unification_pass verbose debug ast = 

  let failure str = raise (PassExn ("Failed to unify clocks: "^str)) in
    
  let known_clocks = Hashtbl.create 100 in

  let find_clock_var var = 
      match Hashtbl.find_opt known_clocks var with
      | None -> 
        begin
          match var with
          | BVar(name)
          | IVar(name)
          | RVar(name) -> raise (PassExn ("Cannot find clock of variable "^name) )
        end
      | Some c -> c
  in

  let rec compute_clock_exp exp = match exp with
  | EConst(_, _) -> [Base]
  | EVar(_, var) -> find_clock_var var
  | EMonOp(_, MOp_pre, _) -> [Base]
  | EMonOp(_, _, e) -> compute_clock_exp e

  | EComp(_, _, e1, e2)
  | EReset(_, e1, e2)
  | EBinOp(_, _, e1, e2) -> 
    begin
      let c1 = compute_clock_exp e1
      and c2 = compute_clock_exp e2 in
      if c1 <> c2 then
        failure "Binop"
      else
        c1
    end
  | EWhen(_, e1, e2) -> 
      begin
        match compute_clock_exp e1 with
        | [c1] -> [On (c1, e2)]
        | _ -> failure "When"
      end
  | ETriOp(_, TOp_merge, e1, e2, e3) ->
    begin
      let c1 = compute_clock_exp e1
      and c2 = compute_clock_exp e2
      and c3 = compute_clock_exp e3 in
      match c1, c2, c3 with
      | [c1], [On(cl2, e2)], [On(cl3, e3)] ->
          begin
            if cl2 <> c1 || cl3 <> c1 then
              failure "Triop clocks"
            else match e2, e3 with
            | EMonOp(_, MOp_not, e), _ when e = e3 -> [c1]
            | _, EMonOp(_, MOp_not, e) when e = e2 -> [c1]
            | _ -> failure "Triop condition"
          end
      | _ -> failure ("Merge format")
    end
  | ETriOp(_, TOp_if, e1, e2, e3) ->
      let (* Unused: c1 = compute_clock_exp e1
      and*) c2 = compute_clock_exp e2
      and c3 = compute_clock_exp e3 in
      if c2 <> c3 then
        failure "If clocks"
      else c2

  | ETuple(_, explist) -> List.concat_map compute_clock_exp explist
  | EApp(_, node, e) -> 
      let rec aux_app clk_list = match clk_list with
      | [] -> raise (PassExn "Node called with no argument provided")
      | [cl] -> cl
      | t::q -> if t = (aux_app q) then t else failure "App diff clocks"
      and mult_clk cl out_list = match out_list with
      | [] -> []
      | t::q -> cl::(mult_clk cl q)
      in
      mult_clk (aux_app (compute_clock_exp e)) (snd node.n_outputs)
      in

  let rec compute_eq_clock eq = 
    let rec step vars clks = match vars, clks with
    | [], [] -> ()
    | [], c::q -> raise (PassExn "Mismatch between clock size")
    | v::t, c::q -> Hashtbl.replace known_clocks v [c]; step t q
    | l, [] -> raise (PassExn "Mismatch between clock size")
    in
    let (_, vars), exp = eq in
    let clk = compute_clock_exp exp in
    step vars clk
  in

  let compute_clock_node n = 
    begin
      Hashtbl.clear known_clocks;
      List.iter (fun v -> Hashtbl.replace known_clocks v [Base]) (
        snd n.n_inputs); (* Initializing inputs to base clock *)
      List.iter compute_eq_clock n.n_equations;
      if not (List.for_all (fun v -> (Hashtbl.find known_clocks v) = [Base]) (
        snd n.n_outputs)) then failure "Outputs" (*Checking that the node's output are on base clock *)
      else
        Some n
    end
  in node_pass compute_clock_node ast
