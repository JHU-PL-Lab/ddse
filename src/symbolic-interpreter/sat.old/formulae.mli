(**
   This module defines a data structure for storing and analyzing logical
   formulae regarding a symbolically interpreted program.
*)

open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Pp_utils;;

open Ast;;
open Interpreter_types;;
open Sat_types;;

(** A type representing the kind of information a formula symbol contains. *)
type symbol_type =
  | IntSymbol
  | BoolSymbol
  | RecordSymbol
  | FunctionSymbol of function_value
;;

val pp_symbol_type : symbol_type pretty_printer;;

(** An exception which is raised if an inconsistent formula is added to a
    collection.  This is not guaranteed to be thrown in all contradictory
    circumstances; it is thrown when the intersection of types assigned to a
    symbol produces the empty set. *)
exception SymbolTypeContradiction of string * symbol * symbol_type list;;

(** An exception which is raised if an inconsistent pair if immediate
    assignments is added to a collection.  This is not guaranteed to be thrown
    in all contradictory circumstances; it is only thrown when two immediately
    contradictory value assignments (e.g. x = 4 and x = 6) attempt to
    coexist. *)
exception SymbolValueContradiction of string * symbol * value * value;;

(** A type representing a collection of formulae. *)
type t;;

(** An empty collection of formulae. *)
val empty : t;;

(** Adds an element to a collection.  May raise a SymbolTypeContradiction if the
    formula eliminates all possible values for a symbol. *)
val add : formula -> t -> t;;

(** Creates a singleton collection. *)
val singleton : formula -> t;;

(** Unions two collections.  May raise a SymbolTypeContradiction as in the add
    function. *)
val union : t -> t -> t

(** Enumerates the formulae in a collection. *)
val enum : t -> formula Enum.t;;

(** Creates a formulae collection from an enumeration of formulae. *)
val of_enum : formula Enum.t -> t;;

(** Processes each formula in a collection. *)
val iter : (formula -> unit) -> t -> unit;;

(** Retrieves the inferred type of a symbol in a collection.  If None is
    returned, the symbol has no fixed type; this may occur if a symbol has been
    introduced via a formula but has never been constrained.  Raises Not_found
    if the symbol has never been introduced. *)
val type_of : symbol -> t -> symbol_type option;;

(** Pretty-prints a set of formulae. *)
val pp : t pretty_printer;;

(** Shows a set of formulae. *)
val show : t -> string;;

(** Briefly pretty-prints a set of formulae. *)
val pp_brief : t pretty_printer;;

(** Briefly shows a set of formulae. *)
val show_brief : t -> string;;
