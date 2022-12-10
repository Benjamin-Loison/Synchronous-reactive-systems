open Ast

let rec list_repeat n elt =
  if n = 0 then [] else elt :: (list_repeat (n-1) elt)

let rec list_chk v = function
  | [] -> false
  | h :: t -> if h = v then true else list_chk v t

exception MyParsingError of (string * Ast.location)

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

