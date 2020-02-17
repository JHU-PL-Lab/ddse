(**
   This module contains a number of utilty functions used to create formulae.
*)

open Batteries;;
open OUnit2;;

open Odefa_ast;;
open Odefa_symbolic_interpreter;;

open Ast;;
open Ast_pp;;
open Interpreter_types;;

let empty_stack = Relative_stack.empty;;
let empty_stack_symbol x = Symbol(Ident(x), empty_stack);;
let symbol_with_stack x s =
  Symbol(Ident(x),
         s
         |> List.map
           (fun name -> Ident(name))
         |> List.fold_left
           (fun a e -> Option.get @@ Relative_stack.push a e)
           Relative_stack.empty
        )
;;

let x = empty_stack_symbol "x";;
let y = empty_stack_symbol "y";;
let z = empty_stack_symbol "z";;
let xa = symbol_with_stack "x" ["a"];;

let alias s1 s2 = Constraint.Constraint_alias(s1, s2);;
let set_int s n = Constraint.Constraint_value(s, Constraint.Int n);;
let set_bool s n = Constraint.Constraint_value(s, Constraint.Bool n);;

let string_of_constraint_list constraint_list =
  String.join "\n" @@ List.map Constraint.show constraint_list
;;

let indent str =
  String.nreplace ~str:str ~sub:"\n" ~by:"\n  "
;;

let assert_solvable constraint_list =
  let formulae = Solver.of_enum @@ List.enum constraint_list in
  if not @@ Solver.solvable formulae then
    assert_failure @@
    let msg = indent @@ string_of_constraint_list constraint_list in
    Printf.sprintf "Should be able to solve formula set:\n%s" msg
;;

let assert_unsolvable constraint_list =
  let formulae = Solver.of_enum @@ List.enum constraint_list in
  if Solver.solvable formulae then
    assert_failure @@
    let msg = indent @@ string_of_constraint_list constraint_list in
    Printf.sprintf "Should NOT be able to solve formula set:\n%s" msg
;;

let assert_solutions constraint_list solutions =
  let formulae = Solver.of_enum @@ List.enum constraint_list in
  match Solver.solve formulae with
  | None ->
    assert_failure @@
    let msg = indent @@ string_of_constraint_list constraint_list in
    Printf.sprintf "Should NOT be able to solve formula set:\n%s" msg
  | Some model ->
    solutions
    |> List.iter
      (fun (symbol, expected_answer) ->
         let actual_answer = model symbol in
         if not @@ Option.eq ~eq:equal_value expected_answer actual_answer then
           assert_failure @@
           let set_msg = indent @@ string_of_constraint_list constraint_list in
           Printf.sprintf
             "Expected %s but got %s for symbol %s in formula set:\n%s"
             (Option.default "<none>" @@ Option.map show_value expected_answer)
             (Option.default "<none>" @@ Option.map show_value actual_answer)
             (show_symbol symbol)
             set_msg;
      )
;;

let assert_symbol_type_error constraint_list =
  try
    let _ = Solver.of_enum @@ List.enum constraint_list in
    assert_failure @@
    let msg = indent @@ string_of_constraint_list constraint_list in
    Printf.sprintf "Should receive symbol type error from formula set:\n%s" msg
  with
  | Solver.TypeContradiction _ ->
    ()
;;
