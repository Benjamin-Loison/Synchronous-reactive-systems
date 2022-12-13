open Ast

let exit_error (s: string) : unit =
  Format.printf "\n\tCritical error: %s\n\n" s

let print_debug d s =
  if d then Format.printf "\x1b[31;01;04mDebug :\x1b[0m %s\n" s else ()

let print_verbose v s =
  if v then Format.printf "\x1b[33;01;04mStatus:\x1b[0m %s\n" s else ()

let exec_passes ast verbose debug passes f =
  let rec aux ast = function
    | [] ->  f ast
    | (n, p) :: passes ->
        verbose (Format.asprintf "Executing pass %s:\n" n);
        match p ast with
        | None -> (exit_error ("Error while in the pass "^n^".\n"); exit 0)
        | Some ast -> (
        debug (Format.asprintf "Current AST (after %s):\n%a\n" n Pp.pp_ast ast);
        aux ast passes)
  in
  aux ast passes


let _ =
  (** Usage and argument parsing. *)
  let default_passes = ["pre2vars"] in
  let usage_msg =
    "Usage: main [-passes p1,...,pn] [-ast] [-verbose] [-debug] \
      [-o output_file] source_file\n" in
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
  let print_debug = print_debug !debug in

  (** Definition of the passes table *)
  let passes_table : (string,  t_nodelist -> t_nodelist option) Hashtbl.t = Hashtbl.create 100 in
  List.iter (fun (s, k) -> Hashtbl.add passes_table s k)
    [
      ("pre2vars", Passes.pre2vars);
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
      end
    | Parsing.Parse_error ->
      begin
        close_in_noerr inchan;
        Parsing.(
        Format.printf "Syntax error at %a\n\n"
          Pp.pp_loc ((symbol_start_pos (), symbol_end_pos()), !source_file));
        exit 0
      end
    in

  let passes = List.map (fun (pass: string) -> (pass,
    match Hashtbl.find_opt passes_table pass with
    | None ->
      (exit_error (Format.sprintf "The pass %s does not exist.\n" pass); exit 0)
    | Some f ->
      (print_debug ("The pass "^pass^" has been selected.\n"); f))) !passes in

  print_debug (Format.asprintf "Initial AST (before executing any passes):\n%a"
                Pp.pp_ast ast) ;
  exec_passes ast print_verbose print_debug passes
    begin
    if !ppast
      then (Format.printf "%a" Pp.pp_ast)
      else (Format.printf "%a" Ast_to_c.ast_to_c)
    end

