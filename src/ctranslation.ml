open Ast
open Intermediate_ast
open Cast

let rec iexpression_to_cvalue e =
  match e with
  | IEVar   v -> CVariable v
  | IEMonOp (op, e) -> CMonOp (op, iexpression_to_cvalue e)
  | IEBinOp (op, e, e') ->
      CBinOp (op, iexpression_to_cvalue e, iexpression_to_cvalue e')
  | IEComp  (op, e, e') ->
      CComp (op, iexpression_to_cvalue e, iexpression_to_cvalue e')
  | IEConst c -> CConst c
  | IEWhen  _
  | IEReset _
  | IETuple _
  | IEApp   _
  | IETriOp _ -> failwith "[ctranslation.ml] Should not happened."

let rec equation_to_expression (node_st, node_sts, (vl, expr)) =
  let hloc = node_st.nt_map in
  let fetch_unique_var () =
    match vl with
    | [v] ->
      begin
        match Hashtbl.find_opt hloc (Utils.name_of_var v, false) with
        | None -> CVInput (Utils.name_of_var v)
        | Some (arr, idx) -> CVStored (arr, idx)
      end
    | _ -> failwith "[ctranslation.ml] This should not happened."
  in
  match expr with
  | IEVar   vsrc ->
      CAssign (fetch_unique_var (), CVariable vsrc)
  | IEMonOp (MOp_pre, IEVar v) ->
      CAssign (fetch_unique_var (), CVariable v)
  | IEConst c ->
      CAssign (fetch_unique_var (), CConst c)
  | IEMonOp (op, e) ->
      CAssign (fetch_unique_var (),
                CMonOp (op, iexpression_to_cvalue e))
  | IEBinOp (op, e, e') ->
      CAssign (fetch_unique_var (),
                CBinOp (op, iexpression_to_cvalue e, iexpression_to_cvalue e'))
  | IEComp  (op, e, e') ->
      CAssign (fetch_unique_var (),
                CComp (op, iexpression_to_cvalue e, iexpression_to_cvalue e'))
      (** [CApp] below represents the i-th call to an aux node *)
  | IEApp   (i, node, e) ->
      (** e is a tuple of variables due to the linearization pass *)
      let al: c_var list =
        match e with
        | IETuple l ->
            List.map
              (function
                | IEVar v -> v
                | _ -> failwith "[ctranslation.ml] should not happened due to the linearization pass."
                ) l
        | _ -> failwith "[ctranslation.ml] should not happened due to the linearization pass."
        in
      let vl =
        List.map
          (fun v ->
            match Hashtbl.find_opt hloc (Utils.name_of_var v, false) with
            | Some (arr, idx) -> CVStored (arr, idx)
            | None -> CVInput (Utils.name_of_var v))
          vl
        in
      CApplication (node.n_name,i , al, vl, node_sts)
  | IETuple _ -> failwith "[ctranslation.ml] linearisatiosn should have transformed you."
  | IEWhen  (expr, cond) ->
    begin
      CIf (iexpression_to_cvalue cond,
            [equation_to_expression (node_st, node_sts, (vl, expr))],
            [])
    end
  (*TODO!
  | IETriOp of triop * i_expression * i_expression * i_expression
  | IEReset of i_expression * i_expression*)
  | _ -> failwith "[ctranslation.ml] TODO!"

