open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_ddpa;;

open Ast;;
open Ast_pp;;

open Generator_configuration;;
open Generator_types;;
open Odefa_symbolic_interpreter.Interpreter_types;;

module Symbolic_interpreter = Odefa_symbolic_interpreter;;
module Relative_stack = Symbolic_interpreter.Relative_stack;;
module Solver = Symbolic_interpreter.Solver;;

let lazy_logger = Logger_utils.make_lazy_logger "Generator";;

(** Calculates the difference between two stacks.  Given a reference point at
    which to start, this function computes the relative stack which will produce
    the goal.
*)
let relativize_stack
    (reference_point : Ident.t list)
    (goal : Ident.t list)
  : Relative_stack.t =
  let insist f x s =
    match f x s with
    | None -> raise @@ Jhupllib.Utils.Invariant_failure "insist got None stack"
    | Some s' -> s'
  in
  (* Start by throwing away everything they have in common. *)
  let rec discard_common start finish =
    match start, finish with
    | x :: start', y :: finish' when equal_ident x y ->
      discard_common start' finish'
    | _ -> start, finish
  in
  let start, finish = discard_common reference_point goal in
  (* To get from the start stack to the finish stack, we'll first have to pop
     everything from the start stack and then push everything from the finish
     stack. *)
  let relstack =
    Relative_stack.empty
    |> List.fold_right (flip @@ insist Relative_stack.pop) (List.rev start)
    |> (flip @@ List.fold_left (insist Relative_stack.push)) (List.rev finish)
  in
  relstack
;;

exception Halt_interpretation_as_input_sequence_is_complete;;

let input_sequence_from_solution
    (solution : Solver.solution)
    (e : expr)
    (stop_var : Var.t)
  : int list =
  let _, stop_stack =
    match stop_var with
    | Var(_,None) ->
      raise @@ Jhupllib.Utils.Invariant_failure
        "Non-freshened stop variable!"
    | Var(x,Some(Freshening_stack(stop_stack))) -> x,stop_stack
  in
  let input_record = ref [] in
  let read_from_formulae (Var(x,stack_opt)) =
    let stack =
      match stack_opt with
      | None ->
        raise @@ Jhupllib.Utils.Invariant_failure
          "Interpreter performed input on non-freshened variable!"
      | Some(Freshening_stack(stack)) ->
        stack
    in
    let relstack = relativize_stack stop_stack stack in
    let symbol = Symbol(x, relstack) in
    let value =
      match solution symbol with
      | None ->
        (* The solver had no value for us.  That means that this variable is
           unconstrained and we are free to pick as we please. *)
        Value_int 0
      | Some value ->
        value
    in
    input_record := value :: !input_record;
    value
  in
  let stop_at_stop_var (Clause(x,_)) =
    if equal_var x stop_var then
      raise Halt_interpretation_as_input_sequence_is_complete
    else
      ()
  in
  begin
    try
      let _ =
        Odefa_interpreter.Interpreter.eval
          ~input_source:read_from_formulae
          ~clause_callback:stop_at_stop_var
          e
      in
      raise @@ Jhupllib.Utils.Invariant_failure
        "evaluation completed without triggering halt exception!"
    with
    | Halt_interpretation_as_input_sequence_is_complete -> ()
  end;
  let input_sequence = List.rev !input_record in
  input_sequence
  |> List.map
    (fun value ->
       match value with
       | Value_int n -> n
       | _ ->
         raise @@ Jhupllib.Utils.Not_yet_implemented
           "cannot presently handle non-integer input!"
    )
;;

let rec take_steps
    (e : expr)
    (x : Ident.t)
    (max_steps : int)
    (evaluation : Symbolic_interpreter.Interpreter.evaluation)
  : test_generation_result =
  let rec loop
      (step_count : int)
      (ev : Symbolic_interpreter.Interpreter.evaluation)
    : test_generation_result =
    lazy_logger `trace (fun () -> Printf.sprintf
                           "%d/%d completed in this pass" step_count max_steps);
    if step_count = max_steps then begin
      lazy_logger `trace (fun () ->
          "Pass reached max step count; returning suspended generator.");
      { tgr_input_sequences = [];
        tgr_steps = step_count;
        tgr_generator =
          { tg_program = e;
            tg_target = x;
            tg_generator_fn = Some(fun n -> take_steps e x n ev)
          };
      }
    end else begin
      let results, ev'_opt = Odefa_symbolic_interpreter.Interpreter.step ev in
      if List.is_empty results then begin
        lazy_logger `trace (fun () ->
            "No new results found in this step.");
        match ev'_opt with
        | Some ev' ->
          (* No result and no termination.  Keep running. *)
          lazy_logger `trace (fun () ->
              "Interpreter evaluation not yet complete; continuing.");
          loop (step_count + 1) ev'
        | None ->
          (* No result and no remaining computation; we terminated!  Give back a
             result indicating as much. *)
          lazy_logger `trace (fun () ->
              "Interpreter evaluation complete; stopping.");
          { tgr_input_sequences = [];
            tgr_steps = step_count + 1;
            tgr_generator =
              { tg_program = e;
                tg_target = x;
                tg_generator_fn = None;
              };
          }
      end else begin
        (* We have results! *)
        lazy_logger `trace (fun () -> "Found input sequences!");
        let input_sequence_from_result result =
          let formulae =
            result.Symbolic_interpreter.Interpreter.er_solver
          in
          match Solver.solve formulae with
          | None ->
            raise @@ Jhupllib_utils.Invariant_failure
              "input_sequence_from_result (no solution)"
          | Some solution ->
            let Concrete_stack stack =
              result.Symbolic_interpreter.Interpreter.er_stack
            in
            let stop_var = Var(x,Some(Freshening_stack(stack))) in
            let input_sequence =
              input_sequence_from_solution solution e stop_var
            in
            lazy_logger `trace (fun () ->
                Printf.sprintf "Yielding input sequence: %s"
                  (String.join "," @@ List.map string_of_int input_sequence)
              );
            input_sequence
        in
        let input_sequences = List.map input_sequence_from_result results in
        let generator_fn =
          match ev'_opt with
          | None -> None
          | Some ev' -> Some(fun n -> take_steps e x n ev')
        in
        { tgr_input_sequences = input_sequences;
          tgr_steps = step_count + 1;
          tgr_generator =
            { tg_program = e;
              tg_target = x;
              tg_generator_fn = generator_fn;
            };
        }
      end
    end
  in
  loop 0 evaluation
;;

let create
    ?exploration_policy:(exploration_policy=
                         Symbolic_interpreter.Interpreter.Explore_breadth_first)
    (conf : configuration)
    (e : expr)
    (x : Ident.t)
  : test_generator =
  let module Stack = (val conf.conf_context_model) in
  let module Analysis = Ddpa_analysis.Make(Stack) in
  let cfg =
    e
    |> Analysis.create_initial_analysis
    |> Analysis.perform_full_closure
    |> Analysis.cfg_of_analysis
  in
  let evaluation =
    Odefa_symbolic_interpreter.Interpreter.start
      ~exploration_policy:exploration_policy
      cfg e x
  in
  { tg_program = e;
    tg_target = x;
    tg_generator_fn = Some(fun n -> take_steps e x n evaluation)
  }
;;

let generate_inputs
    ?generation_callback:(generation_callback=fun _ _ -> ())
    (max_steps_opt : int option)
    (original_generator : test_generator)
  : (int list * int) list * test_generator option =
  lazy_logger `trace
    (fun () -> "Generating inputs for expression:\n" ^
               Pp_utils.pp_to_string pp_expr original_generator.tg_program
    );
  let max_steps_per_loop = 100 in
  let rec loop
      (generator : test_generator)
      (steps_left_opt : int option)
      (steps_taken : int)
      (results : (int list * int) list)
    : (int list * int) list * test_generator option =
    let steps_to_take =
      match steps_left_opt with
      | None -> max_steps_per_loop
      | Some n -> min n max_steps_per_loop
    in
    if steps_to_take = 0 then begin
      (* We're quitting now! *)
      lazy_logger `trace
        (fun () -> "Out of generation steps; stopping with waiting generator.");
      (results, Some generator)
    end else begin
      lazy_logger `trace
        (fun () -> Printf.sprintf
            "Taking up to %d step%s of generation in this loop" steps_to_take
            (if steps_to_take = 1 then "" else "s"));
      match generator.tg_generator_fn with
      | None ->
        (* No further generation is possible. *)
        lazy_logger `trace
          (fun () -> "Generation terminated with no further results.");
        (results, None)
      | Some fn ->
        let result = fn steps_to_take in
        let steps_taken' = steps_taken + result.tgr_steps in
        lazy_logger `trace
          (fun () -> Printf.sprintf "Took %d step%s (%d so far)"
              result.tgr_steps
              (if result.tgr_steps = 1 then "" else "s")
              steps_taken');
        begin
          match result.tgr_input_sequences with
          | _ :: _ ->
            result.tgr_input_sequences
            |> List.iter
              (fun input_sequence ->
                 lazy_logger `trace
                   (fun () -> Printf.sprintf "Found an input sequence: [%s]"
                       (String.join ", " @@
                        List.map string_of_int input_sequence));
                 generation_callback input_sequence steps_taken';
              );
          | [] ->
            lazy_logger `trace
              (fun () ->
                 "No further input sequence discovered in this iteration.");
        end;
        let results' =
          List.map (fun seq -> (seq, steps_taken')) result.tgr_input_sequences @
          results
        in
        let steps_left_opt' =
          Option.map (fun n -> max 0 @@ n - result.tgr_steps) steps_left_opt
        in
        loop result.tgr_generator steps_left_opt' steps_taken' results'
    end
  in
  loop original_generator max_steps_opt 0 []
;;
