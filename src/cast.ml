open Intermediate_ast
open Ast

(** This file contains a small subset of the syntax of C required for the
  * translation. *)

(** A [c_block] represents a block in C. *)
type c_block = c_expression list

(** A [c_expresion] represents a C expression, which can need sequences and
  * function calls. *)
and c_expression =
  | CAssign of c_var * c_value
  | CSeq of c_expression * c_expression
  | CIf of c_value * c_block * c_block
  | CApplication of ident * c_var list

(** A value here is anything that can be inlined into a single C expression
  * containing no function call, condition, ... *)
and c_value =
  | CVariable of c_var
  | CMonOp of monop * c_value
  | CBinOp of binop * c_value * c_value
  | CComp of compop * c_value * c_value
  | CConst of const

