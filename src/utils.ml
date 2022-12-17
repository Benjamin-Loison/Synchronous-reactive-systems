open Ast

let rec list_select n = function
  | [] -> [], []
  | h :: t ->
      if n = 0
        then ([], h :: t)
        else
          let p1, p2 = list_select (n-1) t in
          h :: p1, p2

let rec list_remove_duplicates l =
  match l with
  | [] -> []
  | h :: t ->
      let t = list_remove_duplicates t in
      if List.mem h t then t else h :: t

let rec list_map_option (f: 'a -> 'b option) (l: 'a list) : 'b list option =
  List.fold_right (fun elt acc ->
    match acc, f elt with
    | None, _ | _, None -> None
    | Some acc, Some elt -> Some (elt :: acc)) l (Some [])

let rec list_repeat n elt =
  if n = 0 then [] else elt :: (list_repeat (n-1) elt)

let rec list_chk v = function
  | [] -> false
  | h :: t -> if h = v then true else list_chk v t

let rec vars_distinct lv lv' lv'' =
  match lv, lv', lv'' with
  | [], [], _ -> true
  | [], h :: t , l'' ->
      if List.mem h l''
        then false
        else vars_distinct [] t l''
  | h :: t, l', l'' ->
      if List.mem h l' || List.mem h l''
        then false
        else vars_distinct t l' l''

exception MyParsingError of (string * location)

let type_const = function
  | CReal _ -> [TReal]
  | CInt  _ -> [TInt ]
  | CBool _ -> [TBool]

let type_var (v: t_var) =
    match v with
    | IVar _ -> [TInt]
    | BVar _ -> [TBool]
    | RVar _ -> [TReal]

let type_exp : t_expression -> full_ty = function
  | EVar   (full_ty , _) -> full_ty
  | EMonOp (full_ty , _ , _) -> full_ty
  | EBinOp (full_ty , _ , _ , _) -> full_ty
  | ETriOp (full_ty , _ , _ , _ , _) -> full_ty
  | EComp  (full_ty , _ , _ , _) -> full_ty
  | EWhen  (full_ty , _ , _) -> full_ty
  | EReset (full_ty , _ , _) -> full_ty
  | EConst (full_ty , _) -> full_ty
  | ETuple (full_ty , _) -> full_ty
  | EApp   (full_ty , _ , _) -> full_ty

let somify f = fun e -> Some (f e)

let name_of_var: t_var -> ident = function
  | IVar s -> s
  | BVar s -> s
  | RVar s -> s

let rec fresh_var_name (l: t_varlist) n : ident =
  let rec aux acc n =
    let r = Random.int 26 in
    Format.asprintf "%c%s"
      (char_of_int (r + (if Random.bool () then 65 else 97)))
      (if n = 0 then acc else aux acc (n-1))
  in
  let name = aux "" n in
  if List.filter (fun v -> name_of_var v = name) (snd l) = []
    then name
    else fresh_var_name l n

let vars_of_patt patt = List.map name_of_var (snd patt)

let rec vars_of_expr (expr: t_expression) : ident list =
  match expr with
  | EConst _ -> []
  | EVar   (_, v) -> [name_of_var v]
    (** pre (e) does not rely on anything in this round *)
  | EMonOp (_, MOp_pre, _) -> []
  | EApp (_, _, e) | EMonOp (_, _, e) -> vars_of_expr e
  | EComp  (_, _, e, e') | EReset (_, e, e') | EBinOp (_, _, e, e')
  | EWhen  (_, e, e') ->
      (vars_of_expr e) @ (vars_of_expr e')
  | ETriOp (_, _, e, e', e'') ->
      (vars_of_expr e) @ (vars_of_expr e') @ (vars_of_expr e'')
  | ETuple (_, l) -> List.flatten (List.map vars_of_expr l)

let rec varlist_concat (l1: t_varlist) (l2: t_varlist): t_varlist =
  (fst l1 @ fst l2, snd l1 @ snd l2)

