open Ast
open Intermediate_ast
open Cast

let iexpression_to_cvalue e = ()

let equation_to_expression (hloc, ((vl, expr): i_equation)) : c_expression =
  let fetch_unique_var () =
    match vl with
    | [v] ->
      begin
        match Hashtbl.find_opt hloc (v, false) with
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
  (*| IEMonOp (op, e) ->
      CMonOp (op, iexpression_to_cvalue e)
  | IEBinOp (op, e, e') ->
      CBinOp (op, iexpression_to_cvalue e, iexpression_to_cvalue e')
  | IEComp  (op, e, e') ->
      CComp (op, iexpression_to_cvalue e, iexpression_to_cvalue e')
  | IEConst c -> CConst c
  TODO!
  | IETriOp of triop * i_expression * i_expression * i_expression
  | IEWhen  of i_expression * i_expression
  | IEReset of i_expression * i_expression
  | IETuple of (i_expression list)
      (** [CApp] below represents the n-th call to an aux node *)
  | IEApp   of int * t_node * i_expression*)
  | _ -> failwith "[ctranslation.ml] TODO!"

