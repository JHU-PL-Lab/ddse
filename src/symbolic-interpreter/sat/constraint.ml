open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast;;
open Ast_pp;;
open Interpreter_types;;

type symbol_type =
  | IntSymbol
  | BoolSymbol
  | RecordSymbol
  | FunctionSymbol of function_value
[@@deriving eq, ord, to_yojson]
;;

let pp_symbol_type formatter t =
  match t with
  | IntSymbol -> Format.pp_print_string formatter "int"
  | BoolSymbol -> Format.pp_print_string formatter "bool"
  | RecordSymbol -> Format.pp_print_string formatter "record"
  | FunctionSymbol(Function_value(p,_)) ->
    Format.pp_print_string formatter "fun ";
    pp_var formatter p;
    Format.pp_print_string formatter " -> ...";
;;

let show_symbol_type = Pp_utils.pp_to_string pp_symbol_type;;

(** A representation of runtime values in terms of symbols. *)
type value =
  | Int of int
  | Bool of bool
  | Function of function_value
  | Record of symbol Ident_map.t
[@@deriving eq, ord, to_yojson]
;;

let pp_value formatter v =
  match v with
  | Int n -> Format.pp_print_int formatter n
  | Bool b -> Format.pp_print_bool formatter b
  | Function(Function_value(x,_)) ->
    Format.fprintf formatter "fun %a -> ..." pp_var x
  | Record(m) ->
    Pp_utils.pp_map pp_ident pp_symbol Ident_map.enum formatter m
;;

let show_value = Pp_utils.pp_to_string pp_value;;

type t =
  | Constraint_value of symbol * value (* x = v *)
  | Constraint_alias of symbol * symbol (* x = x *)
  | Constraint_binop of symbol * symbol * binary_operator * symbol (* x = x+x *)
  | Constraint_projection of symbol * symbol * ident (* x = x.l *)
  | Constraint_type of symbol * symbol_type (* x : t *)
  | Constraint_stack of Relative_stack.concrete_stack (* stack = C *)
[@@deriving eq, ord, to_yojson]
;;

let pp formatter sc =
  match sc with
  | Constraint_value(x,v) ->
    Format.fprintf formatter "%a = %a" pp_symbol x pp_value v
  | Constraint_alias(x,x') ->
    Format.fprintf formatter "%a = %a" pp_symbol x pp_symbol x'
  | Constraint_binop(x,x',op,x'') ->
    Format.fprintf formatter "%a = %a %a %a"
      pp_symbol x pp_symbol x' pp_binary_operator op pp_symbol x''
  | Constraint_projection(x,x',lbl) ->
    Format.fprintf formatter "%a = %a.%a"
      pp_symbol x pp_symbol x' pp_ident lbl
  | Constraint_type(x,t) ->
    Format.fprintf formatter "%a = %a" pp_symbol x pp_symbol_type t
  | Constraint_stack(s) ->
    Format.fprintf formatter "stack = %a" Relative_stack.pp_concrete_stack s
;;

let show = Pp_utils.pp_to_string pp;;

(* Need to create an equivalent internal type for namespacing reasons. *)
type _t = t [@@deriving ord, show, to_yojson];;
module Symbolic_constraint = struct
  type t = _t [@@deriving ord, show, to_yojson];;
end;;

module Set = struct
  module S = BatSet.Make(Symbolic_constraint);;
  include S;;
  include Pp_utils.Set_pp(S)(Symbolic_constraint);;
  include Yojson_utils.Set_to_yojson(S)(Symbolic_constraint);;
end;;

module Map = struct
  module M = BatMap.Make(Symbolic_constraint);;
  include M;;
  include Pp_utils.Map_pp(M)(Symbolic_constraint);;
  include Yojson_utils.Map_to_yojson(M)(Symbolic_constraint);;
end;;
