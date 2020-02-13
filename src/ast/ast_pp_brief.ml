(** This module contains a collection of pretty-printing functions which print
    an abbreviated form of the Odefa AST.  Most notably, function bodies are
    entirely elided in favor of ellipses.  This abbreviated form is useful for
    printing clauses or values as part of an AST without cluttering output. *)

open Batteries;;
open Jhupllib;;

open Ast;;
open Pp_utils;;

let pp_ident formatter (Ident(s)) = Format.pp_print_string formatter s;;
let show_ident = pp_to_string pp_ident;;

let pp_ident_map pp_value formatter map =
  let open Format in
  pp_concat_sep_delim "{" "}" ","
    (fun formatter (k,v) ->
       pp_ident formatter k;
       pp_print_string formatter " => ";
       pp_value formatter v)
    formatter
  @@
  Ident_map.enum map
;;

let pp_freshening_stack formatter (Freshening_stack ids) =
  ids
  |> List.iter
    (fun i -> Format.pp_print_string formatter "__"; pp_ident formatter i)
;;
let show_freshening_stack = pp_to_string pp_freshening_stack;;

let pp_var formatter (Var(i, mfs)) =
  pp_ident formatter i;
  match mfs with
  | None -> Format.pp_print_char formatter '$'
  | Some fs -> pp_freshening_stack formatter fs
;;
let show_var = pp_to_string pp_var;;

let pp_binary_operator formatter binop =
  let s =
    match binop with
    | Binary_operator_plus -> "+"
    | Binary_operator_minus -> "-"
    | Binary_operator_times -> "*"
    | Binary_operator_divide -> "/"
    | Binary_operator_modulus -> "%"
    | Binary_operator_less_than -> "<"
    | Binary_operator_less_than_or_equal_to -> "<="
    | Binary_operator_equal_to -> "=="
    | Binary_operator_and -> "and"
    | Binary_operator_or -> "or"
    | Binary_operator_xor -> "xor"
  in
  Format.pp_print_string formatter s
;;
let show_binary_operator = pp_to_string pp_binary_operator;;

let pp_record_value formatter (Record_value(els)) =
  let pp_element formatter (k,v) =
    Format.fprintf formatter "%a=%a" pp_ident k pp_var v
  in
  pp_concat_sep_delim "{" "}" "," pp_element formatter @@ Ident_map.enum els
;;
let show_record_value = pp_to_string pp_record_value;;

let rec pp_function_value formatter (Function_value(x,_)) =
  Format.fprintf formatter "fun %a -> ..." pp_var x

and pp_value formatter v =
  match v with
  | Value_record(r) -> pp_record_value formatter r
  | Value_function(f) -> pp_function_value formatter f
  | Value_int(n) -> Format.pp_print_int formatter n
  | Value_bool(b) -> Format.pp_print_bool formatter b

and pp_clause_body formatter b =
  match b with
  | Var_body(x) -> pp_var formatter x
  | Value_body(v) -> pp_value formatter v
  | Input_body -> Format.pp_print_string formatter "input"
  | Appl_body(x1,x2) -> Format.fprintf formatter "%a %a" pp_var x1 pp_var x2
  | Conditional_body(x,_,_) ->
    Format.fprintf formatter
      "%a @[<4>? ...@]"
      pp_var x
  | Match_body(x,_) ->
    Format.fprintf formatter
      "%a ~ ..." pp_var x
  | Projection_body(x,l) ->
    Format.fprintf formatter "%a.%a" pp_var x pp_ident l
  | Binary_operation_body(x1,op,x2) ->
    Format.fprintf formatter "%a %a %a"
      pp_var x1 pp_binary_operator op pp_var x2

and pp_clause formatter c =
  match c with
  | Clause(x,b) -> Format.fprintf formatter "%a = %a" pp_var x pp_clause_body b

and pp_expr formatter (Expr(cls)) =
  pp_concat_sep ";" pp_clause formatter @@ List.enum cls
;;

let show_value = pp_to_string pp_value;;
let show_clause = pp_to_string pp_clause;;
