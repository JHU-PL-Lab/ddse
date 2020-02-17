(** This module defines a solver for the constraints emitted by the symbolic
    interpreter.  This solver performs two types of checks.  As constraints are
    added, they are checked for immediate or relatively obvious contradictions
    (e.g. x = 4 and x = 6).  Later, a user may call the solve routine to check
    for all forms of contradiction (e.g. x < 2 and x > 4).  Solvers are provided
    via a persistent (immutable) interface. *)

open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Interpreter_types;;
open Pp_utils;;

(** An exception which is raised if a constraint is added to a solver which
    causes a symbol to be assigned inconsistent types. *)
exception TypeContradiction of
    symbol * Constraint.symbol_type * Constraint.symbol_type;;

(** An exception which is raised if a constraint is added to a solver which
    causes a symbol to be directly assigned contradictory values.  This is only
    raised when the contradiction is immediate (and not e.g. when binary
    operators eliminate the range of possible values for a symbol). *)
exception ValueContradiction of symbol * Constraint.value * Constraint.value;;

(** The type of solvers. *)
type t;;

(** The type of solutions. *)
type solution = symbol -> Ast.value option;;

(** The empty solver. *)
val empty : t;;

(** Adds a constraint to this solver.  May raise a contradiction. *)
val add : Constraint.t -> t -> t;;

(** Creates a solver with a single constraint. *)
val singleton : Constraint.t -> t;;

(** Unions the constraints for two solvers.  May raise a contradiction. *)
val union : t -> t -> t;;

(** Checks the constraints in a solver.  Returns a solution if one exists;
    returns None if no solution exists. *)
val solve : t -> solution option;;

(** Determines whether a solution exists for a given solver. *)
val solvable : t -> bool;;

(** Enumerates the constraints in a solver. *)
val enum : t -> Constraint.t Enum.t;;

(** Creates a solver from an enumeration of constraints.  May raise a
    contradiction. *)
val of_enum : Constraint.t Enum.t -> t;;

(** Processses each constraint in a solver. *)
val iter : (Constraint.t -> unit) -> t -> unit;;

(** Pretty-prints the constraints in a solver. *)
val pp : t pretty_printer;;

(** Converts the constraints in a solver to a human-readable string. *)
val show : t -> string;;
