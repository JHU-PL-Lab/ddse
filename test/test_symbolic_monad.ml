(** This module contains tests for the solver interface in the symbolic
    interpreter. *)

open Batteries;;
open Jhupllib;;
open OUnit2;;

open Odefa_symbolic_interpreter;;

module F = Formula_test_utils;;

(* **** Scaffolding ***** *)

let _tests_acc = ref [];;
let _add_test name testfn = _tests_acc := (name >:: testfn) :: !_tests_acc;;

(* Experimental monad *)

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
open Test_cache_key;;

(* **** Utils **** *)

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

let test_complete_values
    (type a)
    (printer : a Pp_utils.pretty_printer)
    (equal : a -> a -> bool)
    (computation : a m)
    (expected : a list) : unit =
  let results : a test_result Enum.t = complete computation in
  let actual : a list =
    List.of_enum @@ Enum.map (fun tr -> tr.tr_value) results
  in
  assert_equal
    ~printer:(Pp_utils.pp_to_string @@ Pp_utils.pp_list printer)
    ~cmp:(List.eq equal)
    expected
    actual
;;

let test_complete_values_with_result_steps
    (type a)
    (printer : a Pp_utils.pretty_printer)
    (equal : a -> a -> bool)
    (computation : a m)
    (expected : (a * int) list) : unit =
  let results : a test_result Enum.t = complete computation in
  let actual : (a * int) list =
    List.of_enum @@
    Enum.map (fun tr -> (tr.tr_value,tr.tr_result_steps)) results
  in
  assert_equal
    ~printer:(Pp_utils.pp_to_string @@
              Pp_utils.pp_list @@ Pp_utils.pp_tuple printer Format.pp_print_int)
    ~cmp:(List.eq (fun (x,y) (x',y') -> equal x x' && y = y'))
    expected
    actual
;;

let test_complete_values_with_all_steps
    (type a)
    (printer : a Pp_utils.pretty_printer)
    (equal : a -> a -> bool)
    (computation : a m)
    (expected : (a * int * int) list) : unit =
  let results : a test_result Enum.t = complete computation in
  let actual : (a * int * int) list =
    List.of_enum @@
    Enum.map
      (fun tr ->
         (tr.tr_value, tr.tr_result_steps, tr.tr_evaluation_steps)
      )
      results
  in
  assert_equal
    ~printer:(Pp_utils.pp_to_string @@
              Pp_utils.pp_list @@
              Pp_utils.pp_triple
                printer
                Format.pp_print_int
                Format.pp_print_int)
    ~cmp:(List.eq (fun (x,y,z) (x',y',z') -> equal x x' && y = y' && z = z'))
    expected
    actual
;;

(* **** Tests **** *)

_add_test "pure 4" @@ fun _ ->
let computation =
  return 4
in
test_complete_values_with_result_steps Format.pp_print_int (=) computation
  [(4,1)]
;;

_add_test "nondeterminism" @@ fun _ ->
let computation =
  let%bind z = pick @@ List.enum [1;2;3;4] in
  return z
in
test_complete_values_with_result_steps Format.pp_print_int (=) computation
  [(1,1); (2,1); (3,1); (4,1)]
;;

_add_test "nondeterminism and state" @@ fun _ ->
let computation =
  check_constraints @@
  let%bind () = record_constraint @@ F.set_int F.x 2 in
  let%bind () = record_constraint @@ F.alias F.x F.y in
  let%bind n = pick @@ List.enum [1;2;3] in
  let%bind () = record_constraint @@ F.set_int F.y n in
  return n
in
test_complete_values_with_result_steps Format.pp_print_int (=) computation
  [(2,1)]
;;

_add_test "single pause" @@ fun _ ->
let computation =
  let%bind () = pause () in
  return 5
in
test_complete_values_with_result_steps Format.pp_print_int (=) computation
  [(5,2)]
;;

_add_test "pause in nondeterminism" @@ fun _ ->
let computation =
  let%bind n = pick @@ List.enum [1;2;3] in
  let%bind () = pause () in
  return n
in
test_complete_values_with_result_steps Format.pp_print_int (=) computation
  [(1,2); (2,2); (3,2)]
;;

_add_test "nondeterministic pause" @@ fun _ ->
let computation =
  let%bind n = pick @@ List.enum [1;2;3;4;5] in
  let%bind () = if n mod 2 = 0 then pause () else return () in
  return n
in
test_complete_values_with_result_steps Format.pp_print_int (=) computation
  [(1,1); (3,1); (5,1); (2,2); (4,2)]
;;

_add_test "caching" @@ fun _ ->
let computation =
  let computation_to_cache =
    let%bind () = pause () in
    let%bind () = pause () in
    let%bind () = pause () in
    let%bind () = pause () in
    let%bind () = pause () in
    let%bind () = pause () in
    let%bind () = pause () in
    let%bind () = pause () in
    let%bind () = pause () in
    let%bind () = pause () in
    return 5
  in
  let%bind x = cache (KInt 1) computation_to_cache in
  let%bind y = cache (KInt 1) computation_to_cache in
  return @@ x + y
in
test_complete_values_with_all_steps Format.pp_print_int (=) computation
  [(10,21,14)]
;;

(* **** Packaging up tests for main test module ***** *)

let tests = "symbolic monad tests" >::: List.rev !_tests_acc;;
