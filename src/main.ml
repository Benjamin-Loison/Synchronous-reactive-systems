open Ast

let exit_error (s: string) : unit =
  Format.printf "\n\tCritical error: %s\n\n" s

let print_debug d s =
  if d then Format.printf "\x1b[31;01;04mDebug :\x1b[0m %s\n" s else ()

let print_verbose v s =
  if v then Format.printf "\x1b[33;01;04mStatus:\x1b[0m %s\n" s else ()



(** [exec_passes] executes the passes on the parsed typed-AST.
  * A pass should return [Some program] in case of a success, and [None]
  * otherwise.
  *
  * The function [exec_passes] returns the optionnal program returned by the
  * last pass.
  *
  * A pass should never be interrupted by an exception. Nevertheless, we make
  * sure that no pass raise one. *)
let exec_passes ast verbose debug passes f =
  let rec aux ast = function
    | [] ->  f ast
    | (n, p) :: passes ->
        verbose (Format.asprintf "Executing pass %s:\n" n);
        try
        begin
          match p verbose debug ast with
          | None -> (exit_error ("Error while in the pass "^n^".\n"); exit 0)
          | Some ast -> (
            debug
              (Format.asprintf
                "Current AST (after %s):\n%a\n" n Lustre_pp.pp_ast ast);
            aux ast passes)
        end with
        | _ -> failwith ("The pass "^n^" should have caught me!")
  in
  aux ast passes



let _ =
  (** Usage and argument parsing. *)
  let default_passes =
    ["linearization_reset"; "remove_if";
      "linearization_pre"; "linearization_tuples"; "linearization_app";
      "ensure_assign_val";
      "equations_ordering"] in
  let sanity_passes = ["sanity_pass_assignment_unicity"; "check_typing"] in
  let usage_msg =
    "Usage: main [-passes p1,...,pn] [-ast] [-verbose] [-debug] \
      [-o output_file] [-m main_function] source_file\n" in
  let verbose = ref false in
  let debug = ref false in
  let ppast = ref false in
  let nopopt = ref false in
  let passes = ref [] in
  let source_file = ref "" in
  let testopt = ref false in
  let output_file = ref "out.c" in
  let anon_fun filename = source_file := filename in
  let speclist =
    [
      ("-test", Arg.Set testopt, "Runs the sanity passes not only at the \
                                begining of the compilation, but also after \
                                each pass altering the AST.");
      ("-ast", Arg.Set ppast, "Only print the AST of the input file");
      ("-nop", Arg.Set nopopt, "Only computes the AST and execute the passes");
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
  let passes_table  = Hashtbl.create 100 in
  List.iter (fun (s, k) -> Hashtbl.add passes_table s k)
    [
      ("remove_if", Passes.pass_if_removal);
      ("linearization_tuples", Passes.pass_linearization_tuples);
      ("linearization_app", Passes.pass_linearization_app);
      ("linearization_pre", Passes.pass_linearization_pre);
      ("ensure_assign_val", Passes.pass_ensure_assignment_valuh);
      ("linearization_reset", Passes.pass_linearization_reset);
      ("sanity_pass_assignment_unicity", Passes.sanity_pass_assignment_unicity);
      ("automata_translation", Passes.automata_translation_pass);
      ("automata_validity", Passes.check_automata_validity);
      ("equations_ordering", Passes.pass_eq_reordering);
      ("check_typing", Passes.pass_typing);
      ("clock_unification", Passes.clock_unification_pass);
    ];

  (** Main functionality below *)
  print_verbose "Parsing the source file...";
  let ast =
    let inchan = open_in !source_file in
    try
      begin
        (**let _ = Parsing.set_trace true in*)
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
          Lustre_pp.pp_loc (l, !source_file) s;
        exit 0
      end
    | Parsing.Parse_error ->
      begin
        close_in_noerr inchan;
        Parsing.(
        Format.printf "Syntax error at %a\n\n"
          Lustre_pp.pp_loc ((symbol_start_pos (), symbol_end_pos()), !source_file));
        exit 0
      end
    in

  (** Computes the list of passes to execute. If the [-test] flag is set, all
    * sanity passes (ie. passes which do not modify the AST, but ensure its
    * validity) are re-run after any other pass.
    *
    * Note: the sanity passes are always executed before any other. *)
  let passes =
    List.map
      (fun (pass: string) -> (pass,
        match Hashtbl.find_opt passes_table pass with
        | None ->
          (exit_error (Format.sprintf "The pass %s does not exist.\n" pass); exit 0)
        | Some f ->
          (print_debug ("The pass "^pass^" has been selected.\n"); f)))
      (sanity_passes @
        if !testopt
          then List.flatten (List.map (fun p -> p :: sanity_passes) !passes)
          else !passes)
    in

  print_debug (Format.asprintf "Initial AST (before executing any passes):\n%a"
                Lustre_pp.pp_ast ast) ;
  exec_passes ast print_verbose print_debug passes
  begin
  if !ppast
    then (Format.printf "%a" Lustre_pp.pp_ast)
    else (
      if !nopopt
        then (fun _ -> ())
        else Ast_to_c.ast_to_c print_verbose print_debug)
  end

