open Ast

let exit_error (s: string) : unit =
  Format.printf "\n\tCritical error: %s\n\n" s

let print_debug d s =
  if d then Format.printf "\x1b[31;01;04mDebug :\x1b[0m %s\n" s else ()

let print_verbose v s =
  if v then Format.printf "\x1b[33;01;04mStatus:\x1b[0m %s\n" s else ()

(** The following function should check whether the program is well-formed, by
  * induction:
  *  - for any applications of the form (n, arg1, ..., argn)
  *    + n exists
  *    + n waits n arguments
  *    + arg1, ..., argn are well-typed
  *  - The expressions are well-typed
  *  - The equations are well typed
  *  - The output is set
  *)
let check_well_formedness (a: t_nodelist) = Some a
let check_dependencies (a: t_nodelist) = Some a
let simplify_prog (a: t_nodelist) = Some a

let run verbose debug (passes: (t_nodelist -> t_nodelist option) list) ast
  = verbose "RUN_PLACEHOLDER";
    Format.printf "%a" Ast_to_c.ast_to_c ast

let _ =
  (** Usage and argument parsing. *)
  let default_passes = ["check_form"; "check_dependencies"; "simplify_prog"] in
  let usage_msg = "Usage: main [-passes p1,...,pn] [-ast] [-verbose] [-debug] [-o output_file] source_file" in
  let verbose = ref false in
  let debug = ref false in
  let ppast = ref false in
  let passes = ref [] in
  let source_file = ref "" in
  let output_file = ref "out.c" in
  let anon_fun filename = source_file := filename in
  let speclist =
    [
      ("-ast", Arg.Set ppast, "Only print the AST of the input file");
      ("-verbose", Arg.Set verbose, "Output some debug information");
      ("-debug", Arg.Set debug, "Output a lot of debug information");
      ("-p", Arg.String (fun s -> passes := s :: !passes),
            "Add a pass to the compilation process");
      ("-o", Arg.Set_string output_file, "Output file (defaults to [out.c])");
    ] in
  Arg.parse speclist anon_fun usage_msg ;
  if !source_file = "" then exit_error "No source file specified" else
  if !passes = [] then passes := default_passes;
  let print_verbose = print_verbose !verbose in
  let print_debug = print_debug !verbose in

  (** Definition of the passes table *)
  let passes_table : (string,  t_nodelist -> t_nodelist option) Hashtbl.t = Hashtbl.create 100 in
  List.iter (fun (s, k) -> Hashtbl.add passes_table s k)
    [
      ("check_form", check_well_formedness);
      ("check_dependencies", check_dependencies);
      ("simplify_prog", simplify_prog);
    ];

  (** Main functionality below *)
  print_verbose "Parsing the source file...";
  let ast =
    let inchan = open_in !source_file in
    try
      begin
      let res = Parser.main Lexer.token (Lexing.from_channel inchan) in
      close_in inchan; res
      end
    with
    | Lexer.Lexing_error s ->
        (close_in_noerr inchan;
          exit_error (Format.sprintf "Error code:\n\t%s\n\n" s); exit 0)
    | Utils.MyParsingError (s, l) ->
      begin
        close_in_noerr inchan;
        Format.printf "Syntax error at %a: %s\n\n"
          Pp.pp_loc (l, !source_file) s;
        exit 0
      end in

  if !ppast then Format.printf "%a" Pp.pp_ast ast
  else
    let passes = List.map (fun (pass: string) ->
      match Hashtbl.find_opt passes_table pass with
      | None ->
        (exit_error (Format.sprintf "The pass %s does not exist." pass); exit 0)
      | Some f ->
        (print_debug ("The pass "^pass^" has been selected."); f)) !passes in
    run print_verbose print_debug passes ast;
    print_verbose "End of the program, exiting gracefully."

