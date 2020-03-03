open Batteries;;

open Odefa_ast;;
open Odefa_ddpa;;
open Odefa_test_generation;;

open Ast;;
open Ddpa_context_stack;;
open Generator_configuration;;

open Odefa_symbolic_interpreter.Interpreter;;

type generator_args = {
  ga_generator_configuration : Generator_configuration.configuration;
  ga_filename : string;
  ga_target_point : Ident.t;
  ga_maximum_steps : int option;
  ga_maximum_results : int option;
  ga_exploration_policy : exploration_policy;
  ga_compact_output : bool;
};;

let named_exploration_policies =
  [ (Explore_breadth_first, "bfs");
    (Explore_smallest_relative_stack_length, "relstack-len");
    (Explore_least_relative_stack_repetition, "relstack-rep");
  ]
;;

let single_value_parser
    (type a)
    (arg_name : string)
    (help : string option)
    (default : a option)
    (parse : string -> a option)
  : a BatOptParse.Opt.t =
  let cell : a option ref = ref None in
  { option_set =
      (fun option_name args ->
         let fail s = raise @@ BatOptParse.Opt.Option_error(option_name, s) in
         match args with
         | [] ->
           fail @@ Printf.sprintf "Argument required for option %s" option_name
         | [str] ->
           begin
             match parse str with
             | None ->
               fail @@ Printf.sprintf "Unrecognized %s value: %s" arg_name str
             | Some result ->
               begin
                 match !cell with
                 | None -> cell := Some result
                 | Some _ ->
                   fail @@ Printf.sprintf "Multiple %s values provided" arg_name
               end
           end
         | _ ->
           fail @@ Printf.sprintf "Invalid number of arguments to option %s: %d"
             option_name (List.length args)
      );
    option_set_value = (fun value -> cell := Some value);
    option_get =(fun () -> if Option.is_some !cell then !cell else default);
    option_metavars = [arg_name];
    option_defhelp = help;
  }
;;

let logging_option_parser : unit BatOptParse.Opt.t =
  {
    (* Called whenever e.g. "--log debug" appears in the argument list *)
    option_set =
      (let open Jhupllib.Logger_utils in
       fun option_name args ->
         let match_string_with_level level_str =
           match level_of_string level_str with
           | Some level -> level
           | None -> failwith ("Invalid log level \"" ^ level_str ^ "\".")
         in
         (match args with
          |[arg] ->
            (let (module_name_option,module_level) =
               if BatString.exists arg "=" then
                 let (module_name,module_level) =
                   String.split ~by:"=" arg
                 in (Some module_name,module_level)
               else
                 (None,arg)
             in
             let level' = match_string_with_level module_level in
             match module_name_option with
             |Some(module_name) ->
               set_logging_level_for module_name level'
             |None ->
               set_default_logging_level level'
            )
          | _ -> raise @@ BatOptParse.Opt.Option_error
              (option_name,"Invalid argument")
         )
      )
    ;
    option_set_value = (fun _ -> ())
    ;
    option_get = (fun () -> Some())
    ;
    option_metavars = ["LOG_INSTR"]
    ;
    option_defhelp = Some("Sets the logging level.")
    ;
  }
;;

type parsers =
  { parse_context_stack : (module Context_stack) BatOptParse.Opt.t;
    parse_target_point : string BatOptParse.Opt.t;
    parse_max_steps : int BatOptParse.Opt.t;
    parse_max_results : int BatOptParse.Opt.t;
    parse_exploration_policy : exploration_policy BatOptParse.Opt.t;
    parse_logging : unit BatOptParse.Opt.t;
    parse_compact_output : bool BatOptParse.Opt.t;
  }
;;

exception Argument_parse_failure;;

let make_parsers () : parsers =
  { parse_context_stack =
      single_value_parser
        "CONTEXT_STACK"
        (Some "Specifies the context stack used in CFG construction.")
        (Some (module Ddpa_single_element_stack.Stack : Context_stack))
        (fun stack_name ->
           if stack_name = "0ddpa" then
             Some (module Ddpa_unit_stack.Stack : Context_stack)
           else if stack_name = "1ddpa" then
             Some (module Ddpa_single_element_stack.Stack : Context_stack)
           else if stack_name = "2ddpa" then
             Some (module Ddpa_two_element_stack.Stack : Context_stack)
           else if String.ends_with stack_name "ddpa" then
             try
               let num_str =
                 String.sub stack_name 0 (String.length stack_name - 4)
               in
               let module Stack = Ddpa_n_element_stack.Make(
                 struct let size = int_of_string num_str end)
               in
               Some (module Stack : Context_stack)
             with
             | Failure _ -> None
           else
             None
        );
    parse_target_point =
      single_value_parser
        "VARIABLE"
        (Some "Specifies the variable to reach with generated input.")
        None
        Option.some;
    parse_max_steps =
      single_value_parser
        "MAX_STEPS"
        (Some ("Specifies the maximum number of steps to take during " ^
               "computation."))
        None
        (fun x -> try Some(int_of_string x) with | Failure _ -> None);
    parse_max_results =
      single_value_parser
        "MAX_RESULTS"
        (Some ("Specifies the maximum number of results to find during " ^
               "computation."))
        None
        (fun x -> try Some(int_of_string x) with | Failure _ -> None);
    parse_exploration_policy =
      BatOptParse.Opt.value_option
        "POLICY" (Some(Explore_breadth_first))
        (fun s ->
           try
             List.assoc_inv s named_exploration_policies
           with
           | Not_found -> raise Argument_parse_failure
        )
        (fun _ arg ->
           "Could not understand exploration policy: " ^ arg ^ "\n" ^
           "Valid policies are:\n  " ^
           ( named_exploration_policies
             |> List.map snd
             |> List.map (fun s -> "* " ^ s)
             |> String.concat "\n  "
           )
        );
    parse_compact_output =
      single_value_parser
        "COMPACT_OUTPUT"
        (Some ("Specifies whether the output is compact of descriptive\n"))
        None
        (fun x -> try Some (bool_of_string x) with | Failure _ -> None);
    parse_logging = logging_option_parser;
  }
;;

exception ParseFailure of string;;

let insist name parser =
  match parser.BatOptParse.Opt.option_get () with
  | None ->
    raise @@ ParseFailure(Printf.sprintf "%s is required." name)
  | Some x -> x
;;

let parse_args () : generator_args =
  let cli_parser =
    BatOptParse.OptParser.make ~version:Generator_constants.version ()
  in
  let parsers = make_parsers () in
  (* **** Add options **** *)
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'c'
    ~long_name:"context-stack"
    parsers.parse_context_stack;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'t'
    ~long_name:"target-point"
    parsers.parse_target_point;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'m'
    ~long_name:"maximum-steps"
    parsers.parse_max_steps;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'r'
    ~long_name:"maximum-results"
    parsers.parse_max_results;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'l'
    ~long_name:"log"
    parsers.parse_logging;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'e'
    ~long_name:"exploration-policy"
    parsers.parse_exploration_policy;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'b'
    ~long_name:"compact-output"
    parsers.parse_compact_output;
  (* **** Perform parse **** *)
  let positional_args = BatOptParse.OptParser.parse_argv cli_parser in
  try
    match positional_args with
    | [] ->
      raise @@ ParseFailure("You must specify a source file.")
    | [filename] ->
      let conf =
        { conf_context_model =
            insist "Context model" parsers.parse_context_stack;
        }
      in
      { ga_generator_configuration = conf;
        ga_filename = filename;
        ga_target_point =
          Ident(insist "Target point" parsers.parse_target_point);
        ga_maximum_steps =
          parsers.parse_max_steps.BatOptParse.Opt.option_get ();
        ga_maximum_results =
          parsers.parse_max_results.BatOptParse.Opt.option_get ();
        ga_exploration_policy =
          insist "Exploration policy" parsers.parse_exploration_policy;
        ga_compact_output =
          match (parsers.parse_compact_output.BatOptParse.Opt.option_get ()) with
          | Some b -> b
          | None -> false
      }
    | _::extras ->
      raise @@ ParseFailure(
        Printf.sprintf "Spurious arguments: %s" (String.join " " extras))
  with
  | ParseFailure msg ->
    BatOptParse.OptParser.error cli_parser @@ msg;
    raise @@ Jhupllib.Utils.Invariant_failure
      "BatOptParse.OptParser.error was supposed to terminate the program!"
;;
