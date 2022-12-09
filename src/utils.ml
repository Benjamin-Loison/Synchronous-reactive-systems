let rec list_repeat n elt =
  if n = 0 then [] else elt :: (list_repeat (n-1) elt)

exception MyParsingError of (string * Ast.location)
