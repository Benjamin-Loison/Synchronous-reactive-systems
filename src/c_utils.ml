open Cast

let rec find_app_opt eqs i =
  let rec find_app_expr_opt i = function
    | CVar _ | CConst _ -> None
    | CMonOp (_, e) -> find_app_expr_opt i e
    | CReset (e, e') | CWhen (e, e') | CComp (_, e, e') | CBinOp (_, e, e') ->
        begin
        match find_app_expr_opt i e with
        | None -> find_app_expr_opt i e'
        | Some n -> Some n
        end
    | CTriOp (_, e, e', e'') ->
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
    | CTuple l ->
        List.fold_left
          (fun acc e ->
            match acc, find_app_expr_opt i e with
            | Some n, _ -> Some n
            | None, v -> v)
          None l
        (** [CApp] below represents the n-th call to an aux node *)
    | CApp (j, n, e) ->
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
