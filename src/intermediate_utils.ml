open Intermediate_ast

let rec find_app_opt eqs i =
  let rec find_app_expr_opt i = function
    | IVar _ | IConst _ -> None
    | IMonOp (_, e) -> find_app_expr_opt i e
    | IReset (e, e') | IWhen (e, e') | IComp (_, e, e') | IBinOp (_, e, e') ->
        begin
        match find_app_expr_opt i e with
        | None -> find_app_expr_opt i e'
        | Some n -> Some n
        end
    | ITriOp (_, e, e', e'') ->
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
    | ITuple l ->
        List.fold_left
          (fun acc e ->
            match acc, find_app_expr_opt i e with
            | Some n, _ -> Some n
            | None, v -> v)
          None l
        (** [IApp] below represents the n-th call to an aux node *)
    | IApp (j, n, e) ->
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
