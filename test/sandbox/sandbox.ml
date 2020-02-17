open Batteries;;
open Jhupllib;;

open Odefa_symbolic_interpreter;;

open Interpreter_types;;

module Test_cache_key = struct
  type 'a t = KInt : int -> int t;;
  type some_key = Some_key : 'a t -> some_key;;
  let compare (type a b) (x : a t) (y : b t) : (a,b) Gmap.Order.t =
    let KInt(x) = x in
    let KInt(y) = y in
    if x < y then Gmap.Order.Lt else
    if x > y then Gmap.Order.Gt else
      Gmap.Order.Eq
  ;;
  let pp (type a) formatter (x : a t) : unit =
    let KInt(n) = x in
    Format.pp_print_int formatter n
  ;;
  let show x = Jhupllib.Pp_utils.pp_to_string pp x;;
end;;

module Spec = struct
  module Cache_key = Test_cache_key;;
  module Work_collection = Symbolic_monad.QueueWorkCollection(Test_cache_key);;
end;;

module M = Symbolic_monad.Make(Spec);;

open M;;

let symb x = Symbol(Ident(x), Relative_stack.empty);;
let set_int s n = Constraint.Constraint_value(symb s, Constraint.Int n);;
let alias s s' = Constraint.Constraint_alias(symb s, symb s');;

type 'a test_result =
  { tr_value : 'a;
    tr_solver : Solver.t;
    tr_total_steps : int;
    tr_evaluation_steps : int;
    tr_result_steps : int;
  }
  (* NOTE: total steps (computed by test framework) and evaluation steps
     (computed by monadic evaluation engine) should always match. *)
;;

let complete (x : 'a m) : 'a test_result Enum.t =
  let rec loop evaluation steps_so_far : 'a test_result Enum.t =
    let results, evaluation' = step evaluation in
    let new_steps_so_far = steps_so_far + 1 in
    let tagged_results =
      results
      |> Enum.map
        (fun er ->
           { tr_value = er.er_value;
             tr_solver = er.er_solver;
             tr_total_steps = new_steps_so_far;
             tr_evaluation_steps = er.er_evaluation_steps;
             tr_result_steps = er.er_result_steps;
           }
        )
    in
    Enum.append tagged_results @@
    if is_complete evaluation' then Enum.empty () else
      loop evaluation' new_steps_so_far
  in
  loop (start x) 0
;;

let computation =
  check_constraints @@
  let%bind () = record_constraint @@ set_int "x" 2 in
  let%bind () = record_constraint @@ alias "x" "y" in
  let%bind n = pick @@ List.enum [1;2;3] in
  let%bind () = record_constraint @@ set_int "y" n in
  return n
in

let results : int test_result Enum.t = complete computation in
let actual : int list =
  List.of_enum @@ Enum.map (fun tr -> tr.tr_value) results
in
print_endline
  (Pp_utils.pp_to_string (Pp_utils.pp_list Format.pp_print_int) actual);
