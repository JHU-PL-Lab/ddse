(** This module contains definitions related to the formulae on symbols
    generated by the symbolic interpreter. *)

open Odefa_ast;;

open Ast;;
open Interpreter_types;;

(** A high-level grouping of the types of symbols.  These types are not precise;
    they are only designed to detect obvious contradictions in our formulae.
    The only types for which these symbols are entirely precise are those which
    we reason about using Z3 (as Z3 requires explicit symbol types). *)
type symbol_type =
  | IntSymbol
  | BoolSymbol
  | RecordSymbol
  | FunctionSymbol of function_value
[@@deriving eq, ord, show, to_yojson]
;;

(** A representation of runtime values in terms of symbols. *)
type value =
  | Int of int
  | Bool of bool
  | Function of function_value
  | Record of symbol Ident_map.t
[@@deriving eq, ord, show, to_yojson]
;;

(** Represents the constraints on symbols generated by the symbolic
    interpreter and/or used within constraint checking. *)
type t =
  | Constraint_value of symbol * value (* x = v *)
  | Constraint_alias of symbol * symbol (* x = x *)
  | Constraint_binop of symbol * symbol * binary_operator * symbol (* x = x+x *)
  | Constraint_projection of symbol * symbol * ident (* x = x.l *)
  | Constraint_type of symbol * symbol_type (* x : t *)
  | Constraint_stack of Relative_stack.concrete_stack (* stack = C *)
[@@deriving eq, ord, show, to_yojson]
;;

module Set : sig
  module S : BatSet.S with type elt = t;;
  include module type of S;;
  val pp : t Jhupllib_pp_utils.pretty_printer;;
  val show : t -> string;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

module Map : sig
  module M : BatMap.S with type key = t;;
  include module type of M;;
  val pp :
    'a Jhupllib_pp_utils.pretty_printer ->
    'a t Jhupllib_pp_utils.pretty_printer;;
  val show : ('a Jhupllib_pp_utils.pretty_printer) -> 'a t -> string;;
  val to_yojson : ('a -> Yojson.Safe.t) -> 'a t -> Yojson.Safe.t;;
end;;
