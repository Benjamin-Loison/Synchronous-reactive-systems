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
    nt_map_int: (t_var * bool, int) Hashtbl.t;
    nt_map_bool: (t_var * bool, int) Hashtbl.t;
    nt_map_real: (t_var * bool, int) Hashtbl.t;
    nt_map: (t_var * bool, string * int) Hashtbl.t;
    nt_output_map: (int, string * int) Hashtbl.t;
    nt_prevars: t_var list;
    nt_count_app: int;
  }



type c_var =
  | CVStored of string * int
  | CVInput of ident

type c_expression =
  | CVar   of c_var
  | CMonOp of monop * c_expression
  | CBinOp of binop * c_expression * c_expression
  | CTriOp of triop * c_expression * c_expression * c_expression
  | CComp  of compop * c_expression * c_expression
  | CWhen  of c_expression * c_expression
  | CReset of c_expression * c_expression
  | CConst of const
  | CTuple of (c_expression list)
      (** [CApp] below represents the n-th call to an aux node *)
  | CApp   of int * t_node * c_expression

and c_varlist = t_var list

and c_equation = c_varlist * c_expression 

and c_eqlist = c_equation list

and c_node =
  {
    cn_name : ident;
    cn_inputs: c_varlist;
    cn_outputs: c_varlist;
    cn_local_vars: c_varlist;
    cn_equations: c_eqlist;
  }

type c_nodelist = c_node list

type node_states = (ident, node_state) Hashtbl.t

