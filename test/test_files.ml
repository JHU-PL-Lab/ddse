(**
   This test module will load a series of test files from the test sources
   directory and execute them one by one.

   Each file is expected to contain a comment describing the expected test
   result.  The comment should be of one of the following forms:

   - [EXPECT-EVALUATE] (which requires that the code evaluates to completion)
   - [EXPECT-STUCK] (which requires that the code gets stuck)
     FIXME: update this documentation
*)

(* FIXME: purge the term "inconsistency" *)

open Batteries;;
open Jhupllib;;
open OUnit2;;

open Odefa_ast;;
open Odefa_ddpa;;
open Odefa_parser;;
open Odefa_test_generation;;
open Odefa_toploop;;

open Odefa_natural;;

open Ast;;
open Ast_pp;;
open Ast_wellformedness;;
open Generator_configuration;;
open Toploop_options;;
open Toploop_types;;
open Ddpa_abstract_ast;;
open String_utils;;

let lazy_logger = Logger_utils.make_lazy_logger "Test_files";;

exception File_test_creation_failure of string;;

(** Thrown internally when an input generation test can halt generation as all
    sequences have been generated. *)
exception Input_generation_complete of Generator_types.test_generator;;

let string_of_input_sequence input_sequence =
  "[" ^ (String.join "," @@ List.map string_of_int input_sequence) ^ "]"
;;

let string_of_input_sequences input_sequences =
  String.join ", " @@ List.map string_of_input_sequence input_sequences
;;

type test_expectation =
  | Expect_evaluate
  | Expect_stuck
  | Expect_well_formed
  | Expect_ill_formed
  | Expect_analysis_stack_is of (module Ddpa_context_stack.Context_stack) option
  | Expect_input_is of int list
  | Expect_analysis_variable_lookup_from_end of ident * string
  | Expect_analysis_inconsistency_at of ident
  | Expect_analysis_no_inconsistencies
  | Expect_input_sequences_reach of
      string * (* the variable *)
      int list list * (* the expected input sequences *)
      bool (* true if we should be certain that generation is complete *)
  | Expect_required_input_sequence_generation_steps of int
;;

let pp_test_expectation formatter expectation =
  match expectation with
  | Expect_evaluate -> Format.pp_print_string formatter "Expect_evaluate"
  | Expect_stuck -> Format.pp_print_string formatter "Expect_stuck"
  | Expect_well_formed -> Format.pp_print_string formatter "Expect_well_formed"
  | Expect_ill_formed -> Format.pp_print_string formatter "Expect_ill_formed"
  | Expect_analysis_stack_is _ ->
    Format.pp_print_string formatter "Expect_analysis_stack_is(...)"
  | Expect_input_is inputs ->
    Format.fprintf formatter "Expect_int_is [%s]"
      (String.join ", " @@ List.map string_of_int inputs)
  | Expect_analysis_variable_lookup_from_end(x,expected) ->
    Format.fprintf formatter
      "Expect_analysis_variable_lookup_from_end(%a,\"%s\")"
      pp_ident x expected
  | Expect_analysis_inconsistency_at(x) ->
    Format.fprintf formatter
      "Expect_analysis_inconsistency_at(%a)"
      pp_ident x
  | Expect_analysis_no_inconsistencies ->
    Format.pp_print_string formatter "Expect_analysis_no_inconsistencies"
  | Expect_input_sequences_reach(x,inputs,complete) ->
    Format.fprintf formatter "Expect input sequences reach %s: %s%s"
      x
      (string_of_input_sequences inputs)
      (if complete then " (and no others)" else "")
  | Expect_required_input_sequence_generation_steps(n) ->
    Format.fprintf formatter "Expect input sequence generation steps = %d" n
;;

type expectation_parse =
  | Success of test_expectation
  | Failure of string
;;

exception Expectation_parse_failure of string;;

exception Expectation_not_found;;

type expectation_stack_decision =
  | Default_stack
  | Chosen_stack of (module Ddpa_context_stack.Context_stack) option
;;

let parse_expectation str =
  let assert_no_args lst =
    if List.is_empty lst
    then ()
    else raise @@ Expectation_parse_failure "expected no arguments"
  in
  let assert_one_arg lst =
    match lst with
    | [x] -> x
    | _ ->
      raise @@
      Expectation_parse_failure ("expected one argument; got " ^
                                 string_of_int (List.length lst))
  in
  let assert_two_args lst =
    match lst with
    | [x;y] -> (x,y)
    | _ ->
      raise @@
      Expectation_parse_failure ("expected two arguments; got " ^
                                 string_of_int (List.length lst))
  in
  try
    let expectation =
      match String_utils.whitespace_split ~max:2 str with
      | "EXPECT-EVALUATE"::args_part ->
        assert_no_args args_part;
        Expect_evaluate
      | "EXPECT-STUCK"::args_part ->
        assert_no_args args_part;
        Expect_stuck
      | "EXPECT-WELL-FORMED"::args_part ->
        assert_no_args args_part;
        Expect_well_formed
      | "EXPECT-ILL-FORMED"::args_part ->
        assert_no_args args_part;
        Expect_ill_formed
      | "EXPECT-ANALYSIS-STACK-IS"::args_part ->
        let args_str = String.join "" args_part in
        let args = whitespace_split args_str in
        let name = assert_one_arg args in
        begin
          try
            let stack_module = Toploop_utils.stack_from_name name in
            Expect_analysis_stack_is stack_module
          with
          | Not_found ->
            raise @@ Expectation_parse_failure "invalid stack name"
        end
      | "EXPECT-INPUT-IS"::args_part ->
        let args_str = String.join "" args_part in
        let args = whitespace_split args_str in
        let inputs =
          args
          |> List.map
            (fun s ->
               try
                 int_of_string s
               with
               | Failure _ ->
                 raise @@ Expectation_parse_failure
                   ("Could not parse input: " ^ s)
            )
        in
        Expect_input_is inputs
      | "EXPECT-ANALYSIS-LOOKUP-FROM-END"::args_part ->
        let args_str = String.join "" args_part in
        let args = whitespace_split ~max:2 args_str in
        let (ident_str, pp_expectation) = assert_two_args args in
        let ident = Ident(ident_str) in
        Expect_analysis_variable_lookup_from_end(ident,pp_expectation)
      | "EXPECT-ANALYSIS-INCONSISTENCY-AT"::args_part ->
        let args_str = String.join "" args_part in
        let args = whitespace_split args_str in
        let call_site = assert_one_arg args in
        Expect_analysis_inconsistency_at (Ident(call_site))
      | "EXPECT-ANALYSIS-NO-INCONSISTENCIES"::args_part ->
        assert_no_args args_part;
        Expect_analysis_no_inconsistencies
      | "EXPECT-INPUT-SEQUENCES-REACH"::args_part ->
        begin
          match String_utils.whitespace_split ~max:2
                  (String.join "" args_part) with
          | [] ->
            raise @@ Expectation_parse_failure
              "Missing input sequence variable name"
          | variable_name :: rest_args ->
            let parse_rest_args chs =
              let parse_int chs : int * char list =
                let is_digit_char c = (Char.is_digit c) || c == '-' in
                let ns = List.take_while is_digit_char chs in
                let parse_exception = Expectation_parse_failure(
                    "In input sequence expectation, expected integer at: " ^
                    (String.of_list chs)) in
                if List.is_empty ns then begin
                  raise parse_exception
                end else begin
                  let chs' = List.drop_while is_digit_char chs in
                  let to_int_result = int_of_string_opt @@ String.of_list ns in
                  match to_int_result with
                  | Some i -> (i, chs')
                  | None -> raise parse_exception
                end
              in
              let parse_input_sequence chs : int list option * char list =
                match chs with
                | '[' :: chs' ->
                  let first, chs'' = parse_int chs' in
                  let rec loop loop_chs : int list * char list =
                    match loop_chs with
                    | ',' :: loop_chs' ->
                      let num, loop_chs'' = parse_int loop_chs' in
                      let nums, loop_chs''' = loop loop_chs'' in
                      (num :: nums, loop_chs''')
                    | ']' :: loop_chs' ->
                      ([], loop_chs')
                    | _ ->
                      raise @@ Expectation_parse_failure(
                        "In input sequence expectation, expected comma at: " ^
                        (String.of_list chs))
                  in
                  let rest, chs''' = loop chs'' in
                  (Some (first :: rest), chs''')
                | _ ->
                  (None, chs)
              in
              let rec parse_input_sequences chs : int list list * char list =
                let (seq_opt, chs') = parse_input_sequence chs in
                match seq_opt with
                | Some seq ->
                  let (rest, chs'') = parse_input_sequences chs' in
                  (seq :: rest, chs'')
                | None ->
                  ([], chs')
              in
              let nums, chs' = parse_input_sequences chs in
              match chs' with
              | [] -> (nums, false)
              | ['!'] -> (nums, true)
              | _ ->
                raise @@ Expectation_parse_failure(
                  "In input sequence expectation, unexpected trailing characters: " ^
                  (String.of_list chs'))
            in
            let (input_sequences, complete) =
              parse_rest_args @@ List.filter (not % Char.is_whitespace) @@
              String.to_list @@ String.join "" rest_args
            in
            Expect_input_sequences_reach(
              variable_name, input_sequences, complete)
        end
      | "EXPECT-REQUIRED-INPUT-SEQUENCE-GENERATION-STEPS"::args ->
        let nstr = assert_one_arg args in
        begin
          try
            Expect_required_input_sequence_generation_steps(int_of_string nstr)
          with
          | Failure _ ->
            raise @@ Expectation_parse_failure
              (Printf.sprintf
                 "Could not parse number of expected input generation steps: %s"
                 nstr)
        end
      | _ ->
        raise @@ Expectation_not_found
    in
    Some (Success expectation)
  with
  | Expectation_parse_failure s -> Some (Failure s)
  | Expectation_not_found -> None
;;

let observe_evaluated expectation =
  match expectation with
  | Expect_evaluate -> None
  | Expect_stuck ->
    assert_failure @@ "Evaluation completed but was expected to become stuck."
  | _ -> Some expectation
;;

let observe_stuck failure expectation =
  match expectation with
  | Expect_evaluate ->
    assert_failure @@ "Evaluation became stuck: " ^ failure
  | Expect_stuck -> None
  | _ -> Some expectation
;;

let observe_well_formed expectation =
  match expectation with
  | Expect_well_formed -> None
  | Expect_ill_formed ->
    assert_failure @@ "Well-formedness check passed but was expect to fail."
  | _ -> Some expectation
;;

let observe_ill_formed illformednesses expectation =
  match expectation with
  | Expect_well_formed ->
    assert_failure @@ "Expression was unexpectedly ill-formed.  Causes:" ^
                      "\n    * " ^ concat_sep "\n    *"
                        (List.enum @@
                         List.map show_illformedness illformednesses)
  | Expect_ill_formed -> None
  | _ -> Some expectation
;;

let observe_analysis_stack_selection chosen_stack_ref expectation =
  match expectation with
  | Expect_analysis_stack_is module_option ->
    begin
      chosen_stack_ref :=
        begin
          match !chosen_stack_ref with
          | Default_stack -> Chosen_stack module_option
          | Chosen_stack _ ->
            assert_failure @@ "multiple expectations of analysis stack"
        end;
      None
    end
  | _ -> Some expectation
;;

let observe_input_selection input_ref expectation =
  match expectation with
  | Expect_input_is inputs ->
    begin
      input_ref :=
        begin
          match !input_ref with
          | None -> Some inputs
          | Some _ ->
            assert_failure @@ "multiple expectations of input"
        end;
      None
    end
  | _ -> Some expectation
;;

let observe_input_generation_steps input_ref expectation =
  match expectation with
  | Expect_required_input_sequence_generation_steps inputs ->
    begin
      input_ref :=
        begin
          match !input_ref with
          | None -> Some inputs
          | Some _ ->
            assert_failure @@
            "multiple expectations of input generation step count"
        end;
      None
    end
  | _ -> Some expectation
;;

let observe_analysis_variable_lookup_from_end ident repr expectation =
  match expectation with
  | Expect_analysis_variable_lookup_from_end(ident',repr') ->
    if ident = ident'
    then
      begin
        if repr = repr'
        then None
        else assert_failure @@
          Printf.sprintf "for variable %s, expected %s but got %s"
            (show_ident ident) repr' repr
      end
    else Some expectation
  | _ -> Some expectation
;;

let observe_inconsistency inconsistency expectation =
  let site_of_inconsistency =
    let open Toploop_analysis_types in
    match inconsistency with
    | Application_of_non_function (Abs_var ident,_,_,_) -> ident
    | Invalid_binary_operation (Abs_var ident,_,_,_,_,_) -> ident
    | Projection_of_non_record (Abs_var ident,_,_) -> ident
    | Projection_of_absent_label (Abs_var ident,_,_,_) -> ident
  in
  match expectation with
  | Expect_analysis_inconsistency_at expected_site ->
    if site_of_inconsistency = expected_site
    then None
    else Some expectation
  | _ -> Some expectation
;;

let observe_no_inconsistency expectation =
  match expectation with
  | Expect_analysis_no_inconsistencies -> None
  | _ -> Some expectation
;;

let make_test filename expectations =
  let name_of_expectation expectation = match expectation with
    | Expect_evaluate -> "should evaluate"
    | Expect_stuck -> "should get stuck"
    | Expect_well_formed -> "should be well-formed"
    | Expect_ill_formed -> "should be ill-formed"
    | Expect_analysis_stack_is stack_option ->
      let name =
        match stack_option with
        | Some stack ->
          let module Stack =
            (val stack : Ddpa_context_stack.Context_stack)
          in
          Stack.name
        | None -> "none"
      in
      "should use analysis stack " ^ name
    | Expect_input_is inputs ->
      "should have input " ^ (string_of_input_sequence inputs)
    | Expect_analysis_variable_lookup_from_end(ident,_) ->
      "should have particular values for variable " ^ (show_ident ident)
    | Expect_analysis_inconsistency_at ident ->
      "should be inconsistent at " ^ show_ident ident
    | Expect_analysis_no_inconsistencies ->
      "should be consistent"
    | Expect_input_sequences_reach(var,sequences,complete) ->
      Printf.sprintf "should reach variable %s with inputs %s%s"
        var
        (string_of_input_sequences sequences)
        (if complete then " (and no others)" else "")
    | Expect_required_input_sequence_generation_steps(n) ->
      Printf.sprintf "should only require %d steps to discover inputs" n
  in
  let test_name = filename ^ ": (" ^
                  string_of_list name_of_expectation expectations ^ ")"
  in
  (* Create the test in a thunk. *)
  test_name >::
  function _ ->
    lazy_logger `trace (fun () ->
        Printf.sprintf "Performing test for %s with expectations: %s"
          filename
          (Pp_utils.pp_to_string (Pp_utils.pp_list pp_test_expectation)
             expectations)
      );
    (* Using a mutable list of not-yet-handled expectations. *)
    let expectations_left = ref expectations in
    (* This routine takes an observation function and applies it to all of the
       not-yet-handled expectations. *)
    let observation f =
      expectations_left := List.filter_map f @@ !expectations_left;
      lazy_logger `trace (fun () ->
          Printf.sprintf "In test for %s, expectations remaining after an observation: %s"
            filename
            (Pp_utils.pp_to_string (Pp_utils.pp_list pp_test_expectation)
               !expectations_left)
        );
    in
    (* This routine detects expectations of a particular form. *)
    let have_expectation pred = List.exists pred (!expectations_left) in
    (* We're going to execute the following block.  If it completes without
       error, we're also going to require that all of its expectations were
       satisfied.  This addresses nonsense cases such as expecting an ill-formed
       expression to evaluate. *)
    begin
      let is_nato = String.ends_with filename "natodefa" in
      let expr =
        if is_nato then
          let on_expr = File.with_file_in filename On_parse.parse_program in
          On_to_odefa.translate on_expr
        else
          File.with_file_in filename Parser.parse_program in
      (* Decide what kind of analysis to perform. *)
      let module_choice = ref Default_stack in
      observation (observe_analysis_stack_selection module_choice);
      let chosen_module_option =
        match !module_choice with
        | Default_stack ->
          Some (module Ddpa_single_element_stack.Stack :
                 Ddpa_context_stack.Context_stack)
        | Chosen_stack value -> value
      in
      (* Configure the toploop *)
      let variables_to_analyze =
        !expectations_left
        |> List.enum
        |> Enum.filter_map
          (function
            | Expect_analysis_variable_lookup_from_end(ident,expected) ->
              Some(ident,expected)
            | _ -> None)
        |> List.of_enum
      in
      let configuration =
        { topconf_context_stack = chosen_module_option
        ; topconf_log_prefix = filename ^ "_"
        ; topconf_ddpa_log_level = None
        ; topconf_pdr_log_level = None
        ; topconf_pdr_log_deltas = false
        ; topconf_graph_log_file_name = "ddpa_test.log.yojson"
        ; topconf_analyze_vars =
            if variables_to_analyze = []
            then Toploop_option_parsers.Analyze_no_variables
            else
              Toploop_option_parsers.Analyze_specific_variables
                (variables_to_analyze
                 |> List.map (fun (Ident s, _) -> (s, None, None)))
        ; topconf_disable_evaluation =
            not @@ have_expectation
              (function
                | Expect_evaluate -> true
                | Expect_stuck -> true
                | _ -> false)
        ; topconf_disable_inconsistency_check =
            not @@ have_expectation
              (function
                | Expect_analysis_no_inconsistencies -> true
                | Expect_analysis_inconsistency_at _ -> true
                | _ -> false)
        ; topconf_disable_analysis = false
        ; topconf_report_sizes = false
        ; topconf_report_source_statistics = false
        }
      in
      let input_ref = ref None in
      observation (observe_input_selection input_ref);
      let input_callback =
        match !input_ref with
        | Some inputs ->
          (let buffer = ref inputs in
           fun () ->
             match !buffer with
             | [] -> failwith "Out of input"
             | h::t -> buffer := t; h
          )
        | None -> Toploop.default_callbacks.cb_input
      in
      let callbacks =
        { Toploop.default_callbacks with
          cb_input = input_callback
        }
      in
      lazy_logger `trace (fun () ->
          Printf.sprintf "Test for %s: executing toploop handler"
            filename
        );
      (* Run the toploop *)
      let result =
        Toploop.handle_expression
          ~callbacks:callbacks
          configuration
          expr
      in
      lazy_logger `trace (fun () ->
          Printf.sprintf "Test for %s: toploop result was %s"
            filename (Pp_utils.pp_to_string pp_result result)
        );
      (* Report well-formedness or ill-formedness as appropriate. *)
      if result.illformednesses = []
      then observation @@ observe_well_formed
      else observation @@ observe_ill_formed result.illformednesses;
      (* Report each discovered error *)
      result.errors
      |> List.iter
        (fun error -> observation @@ observe_inconsistency error);
      (* If there are no errors, report that. *)
      if result.errors = [] then observation observe_no_inconsistency;
      (* Report each resulting variable analysis. *)
      result.analyses
      |> List.iter
        (fun ((varname,_,_),values) ->
           let repr =
             Pp_utils.pp_to_string Ddpa_abstract_ast.Abs_value_set.pp values
           in
           observation @@ observe_analysis_variable_lookup_from_end
             (Ident varname) repr
        );
      (* Now report the result of evaluation. *)
      begin
        match result.evaluation_result with
        | Evaluation_completed _ -> observation observe_evaluated
        | Evaluation_failure failure -> observation (observe_stuck failure)
        | Evaluation_invalidated -> ()
        | Evaluation_disabled -> ()
      end;
      (* Next, we'll handle input sequence generation.  This requires a
         different approach because we have no guarantee of termination.  We'll
         remove all of the expectations of this form from the list and process
         them individually.  (This is kind of gross and indicates that we're
         bolting onto an abstraction which is no longer suitable for what we're
         doing here, but we can live with this for now.) *)
      let input_generation_steps_ref = ref None in
      observation @@ observe_input_generation_steps input_generation_steps_ref;
      let input_generation_steps =
        Option.default 10000 !input_generation_steps_ref
      in
      let input_generation_expectations =
        let (a,b) =
          !expectations_left
          |> List.fold_left (fun (iges,niges) expectation ->
              match expectation with
              | Expect_input_sequences_reach(x,inputs,complete) ->
                ((x, inputs, complete) :: iges, niges)
              | _ -> (iges, expectation :: niges)
            )
            ([],[])
        in
        expectations_left := List.rev b;
        List.rev a
      in
      let input_generation_complaints =
        input_generation_expectations
        |> List.map
          (fun (x, inputs, complete) ->
             let configuration =
               match chosen_module_option with
               | Some context_model ->
                 { conf_context_model = context_model; }
               | None ->
                 assert_failure
                   "Test specified input sequence requirement without context model."
             in
             let generator = Generator.create
                 ?exploration_policy:(Some (Odefa_symbolic_interpreter.Interpreter.Explore_least_relative_stack_repetition))
                 configuration expr (Ident x) in
             let remaining_input_sequences = ref inputs in
             let callback sequence _steps =
               if List.mem sequence !remaining_input_sequences then begin
                 remaining_input_sequences :=
                   List.remove !remaining_input_sequences sequence;
                 if List.is_empty !remaining_input_sequences && not complete then
                   (* We're not looking for a complete input generation and we've
                      found everything we wanted to find.  We're finished! *)
                   raise @@ Input_generation_complete(generator);
               end else begin
                 (* An input sequence was generated which we didn't expect. *)
                 if complete then
                   (* If the input sequences in the test are expected to be
                      complete, this one represents a problem. *)
                   assert_failure
                     (Printf.sprintf
                        "Unexpected input sequence generated: %s"
                        (string_of_input_sequence sequence)
                     )
                 else
                   (* If the input sequences in the test are not expected to be
                      complete, maybe this is just one which we didn't explicitly
                      call out. *)
                   ()
               end
             in
             (* Setting an arbitrary generation limit for unit tests. *)
             let (_, generator') =
               try
                 Generator.generate_inputs
                   ~generation_callback:callback
                   (Some input_generation_steps) generator
               with
               | Input_generation_complete generator ->
                 ([], Some generator)
             in
             let complaints =
               (
                 (* First, verify that all input sequences were discovered. *)
                 !remaining_input_sequences
                 |> List.map
                   (fun input_sequence ->
                      Printf.sprintf
                        "Did not generate input sequence %s for variable %s."
                        (string_of_input_sequence input_sequence) x
                   )
               ) @
               (
                 (* If we expected a complete input sequence and didn't get that
                    guarantee, complain. *)
                 if complete && Option.is_some generator' then
                   [Printf.sprintf
                      "Test generation did not complete in %d steps."
                      input_generation_steps
                   ]
                 else
                   []
               )
             in
             complaints
          )
        |> List.concat
      in
      (* If there are any expectations of errors left, they're a problem. *)
      !expectations_left
      |> List.iter
        (function
          | Expect_analysis_inconsistency_at ident ->
            assert_failure @@ "Expected error at " ^
                              show_ident ident ^ " which did not occur"
          | _ -> ()
        );
      (* If there are any complaints about input generation, announce them
         now. *)
      if not @@ List.is_empty input_generation_complaints then begin
        assert_failure (
          input_generation_complaints
          |> List.map (fun s -> "* " ^ s)
          |> String.join "\n"
          |> (fun s ->
              "Input generation test failed to meet expectations:\n" ^ s)
        )
      end;
    end;
    (* Now assert that every expectation has been addressed. *)
    match !expectations_left with
    | [] -> ()
    | expectations' ->
      assert_failure @@ "The following expectations could not be met:" ^
                        "\n    * " ^ concat_sep "\n    * "
                          (List.enum @@
                           List.map name_of_expectation expectations')
;;

let make_test_from filename =
  let expectations =
    filename
    |> File.lines_of
    |> Enum.filter_map
      (fun str ->
         let str' = String.trim str in
         if String.starts_with str' "#"
         then
           let str'' = String.trim @@ String.tail str' 1 in
           match parse_expectation str'' with
           | Some (Success expectation) -> Some(Success expectation)
           | Some (Failure s) -> Some(Failure(
               Printf.sprintf
                 "Error parsing expectation:\n        Error: %s\n        Text:  %s"
                 s str''))
           | None -> None
         else None
      )
    |> List.of_enum
  in
  let failures =
    expectations
    |> List.filter_map
      (function
        | Success _ -> None
        | Failure s -> Some s
      )
  in
  match failures with
  | [] ->
    let successes =
      expectations
      |> List.filter_map
        (function
          | Success expectation -> Some expectation
          | Failure _ -> None
        )
    in
    begin
      match successes with
      | [] -> raise (File_test_creation_failure(
          "Could not create test from file " ^ filename ^
          ": no expectations found"))
      | _ ->
        make_test filename successes
    end
  | _ ->
    let message = "Could not create test from file " ^ filename ^ ":" in
    let message' =
      failures
      |> List.fold_left
        (fun msg err -> msg ^ "\n    " ^ err) message
    in
    raise (File_test_creation_failure message')
;;

let wrap_make_test_from filename =
  try
    make_test_from filename
  with
  | File_test_creation_failure s ->
    filename >:: function _ -> assert_failure s
;;

let make_all_tests pathname =
  let legal_exts = [".odefa"; ".natodefa"] in
  if Sys.file_exists pathname && Sys.is_directory pathname
  then
    Sys.files_of pathname
    |> Enum.map (fun f -> pathname ^ Filename.dir_sep ^ f)
    |> Enum.filter (fun f -> not @@ Sys.is_directory f)
    |> Enum.filter (fun f ->
        (List.fold_left
           (fun acc -> fun legal_ext -> acc || (String.ends_with f legal_ext))
           false legal_exts))
    |> Enum.map wrap_make_test_from
    |> List.of_enum
  else
    raise (File_test_creation_failure(
        "Test file directory " ^ pathname ^ " is missing"))
;;

let tests = "Test_source_files" >::: make_all_tests "test-sources";;
