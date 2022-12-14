open Intermediate_ast

let rec find_app_opt eqs i =
  let rec find_app_expr_opt i = function
    | IEVar _ | IEConst _ -> None
    | IEMonOp (_, e) -> find_app_expr_opt i e
    | IEReset (e, e') | IEWhen (e, e') | IEComp (_, e, e') | IEBinOp (_, e, e') ->
        begin
        match find_app_expr_opt i e with
        | None -> find_app_expr_opt i e'
        | Some n -> Some n
        end
    | IETriOp (_, e, e', e'') ->
        begin
        match find_app_expr_opt i e with
        | None ->
          begin
          match find_app_expr_opt i e' with
          | None -> find_app_expr_opt i e''
          | Some n -> Some n
          end
        | Some n -> Some n
        end
    | IETuple l ->
        List.fold_left
          (fun acc e ->
            match acc, find_app_expr_opt i e with
            | Some n, _ -> Some n
            | None, v -> v)
          None l
        (** [IEApp] below represents the n-th call to an aux node *)
    | IEApp (j, n, e) ->
        if i = j
          then Some n
          else find_app_expr_opt i e
  in
  match eqs with
  | [] -> None
  | (_, expr) :: eqs ->
    match find_app_expr_opt i expr with
    | None -> find_app_opt eqs i
    | Some n -> Some n

let find_varname h v =
  Hashtbl.fold
    (fun s e acc ->
      match acc with
      | None -> if e = v then Some s else None
      | Some _ -> acc)
    h None
