open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_test_generation;;

let logger = Logger_utils.make_logger "Test_generator";;
let lazy_logger = Logger_utils.make_lazy_logger "Test_generator";;

exception CommandLineParseFailure of string;;
exception GenerationComplete;;

let () =
  (* Parse CLI args *)
  let args = Generator_configuration_parser.parse_args () in
  (* Read the AST *)
  let ast =
    let is_natodefa =
      Filename.extension args.ga_filename = ".natodefa"
    in
    if is_natodefa then begin
      try
        let natast =
          File.with_file_in args.ga_filename
            Odefa_natural.On_parse.parse_program
        in
        Odefa_natural.On_to_odefa.translate natast
      with
      | Sys_error err ->
        prerr_endline err;
        exit 1
    end else begin
      try
        File.with_file_in args.ga_filename Odefa_parser.Parser.parse_program
      with
      | Sys_error err ->
        prerr_endline err;
        exit 1
    end
  in
  (* Check well-formedness of AST *)
  begin
    try
      Ast_wellformedness.check_wellformed_expr ast;
    with
    | Ast_wellformedness.Illformedness_found ills ->
      begin
        print_endline "Program is ill-formed.";
        ills
        |> List.iter
          (fun ill ->
             print_string "* ";
             print_endline @@ Ast_wellformedness.show_illformedness ill;
          );
        ignore @@ Stdlib.exit 1
      end;
  end;
  (* Generate tests *)
  try
    let results_remaining = ref args.ga_maximum_results in
    let generator =
      Generator.create
        ~exploration_policy:args.ga_exploration_policy
        args.ga_generator_configuration
        ast
        args.ga_target_point
    in
    let generation_callback (inputs : int list) (steps : int) : unit =
      if args.ga_compact_output then (
        Printf.printf "[%s]\n%d\n"
          (String.join "," @@ List.map string_of_int inputs) steps
      ) else (
        Printf.printf "Input sequence: [%s]\nGenerated in %d steps.\n"
          (String.join ", " @@ List.map string_of_int inputs) steps
      );
      flush stdout;
      results_remaining := (Option.map (fun n -> n - 1) !results_remaining);
      if !results_remaining = Some 0 then begin
        raise GenerationComplete
      end;
    in
    begin
      try
        let answers, generator_opt =
          Generator.generate_inputs
            ~generation_callback:generation_callback
            args.ga_maximum_steps
            generator
        in
        let answer_count = List.length answers in
        if args.ga_compact_output then (
          Printf.printf "%d\n" answer_count;
          if Option.is_none generator_opt then
            print_endline "no"
          else
            print_endline "yes"
        ) else (
          Printf.printf "%d answer%s generated\n"
            answer_count (if answer_count = 1 then "" else "s");
          if Option.is_none generator_opt then
            print_endline "No further control flows exist."
          else
            print_endline "Further control flows may exist."
        )
      with
      | GenerationComplete ->
        print_endline "Requested input sequences found; terminating.";
    end
  with
  | Odefa_symbolic_interpreter.Interpreter.Invalid_query msg ->
    prerr_endline msg
;;
