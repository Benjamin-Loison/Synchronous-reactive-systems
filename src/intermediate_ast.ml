open Ast

(** A node state is translated into a struct. This struct has:
  *   1. A name (t_state_<name of the node>)
  *   2. A number of local and output variables of each type (int, real, bool)
  *   3-5. mappings that maps
  *     [(variable, is_pre)] to an index of the corresponding array (see below)
  *     where [variable] is of type [t_var], and [is_pre] indicated whether we
  *     deal with pre (x) or x.
  *   6. A mapping mapping any variable to the name of the C table containing it
  *      and the index at which it is stored (= union of the tables [nt_map_*])
  *   7. A mapping mapping the output number i to its location (name of the
  *     table that contains it and index.
  *
  * Important Note: if a variable x appears behind a pre, it will count as two
  * variables in the point 2. above..
  *
  * It should be translated as follow in C:
      typedef struct {
          int ivars[nt_nb_int];  (or nothing if nt_nb_int = 0)
          int bvars[nt_nb_bool]; (or nothing if nt_nb_bool = 0)
          int rvars[nt_nb_real]; (or nothing if nt_nb_real = 0)
          bool is_init;
      } t_state_<node name>;
  *)
type node_state =
  {
    nt_name: string;
    nt_nb_int : int;
    nt_nb_real: int;
    nt_nb_bool: int;
    nt_map: (ident * bool, string * int) Hashtbl.t;
    nt_output_map: (int, string * int) Hashtbl.t;
    nt_prevars: t_var list;
    nt_count_app: int;
  }



type c_var =
  | CVStored of string * int
  | CVInput of ident

type i_expression =
  | IEVar   of c_var
  | IEMonOp of monop * i_expression
  | IEBinOp of binop * i_expression * i_expression
  | IETriOp of triop * i_expression * i_expression * i_expression
  | IEComp  of compop * i_expression * i_expression
  | IEWhen  of i_expression * i_expression
  | IEReset of i_expression * i_expression
  | IEConst of const
  | IETuple of (i_expression list)
      (** [CApp] below represents the n-th call to an aux node *)
  | IEApp   of int * t_node * i_expression

and i_varlist = t_var list

and i_equation = i_varlist * i_expression

and i_eqlist = i_equation list

and i_node =
  {
    in_name : ident;
    in_inputs: i_varlist;
    in_outputs: i_varlist;
    in_local_vars: i_varlist;
    in_equations: i_eqlist;
  }

type i_nodelist = i_node list

type node_states = (ident, node_state) Hashtbl.t

