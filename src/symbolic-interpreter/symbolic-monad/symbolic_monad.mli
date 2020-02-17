(**
   This module defines a monad used by the symbolic interpreter.  This monad
   provides the following computational properties:

   * Non-determinism (for choices on e.g. wiring nodes)
   * State within (rather than across) non-determinism (to track decisions and
     constraints)
   * SAT checks on collected constraints
   * Stepping incrementally through computation

   To support incremental stepping, this monad's data type is essentially a free
   monad: binds and returns both produce suspended structures with sufficient
   metadata to support the other features.  This monad also provides an
   evaluation stepping routine to allow it to be incrementally evaluated.
*)

open Batteries;;

open Odefa_ast;;

open Ast;;

(** The information pertinent to a single element of work in a symbolic monad
    computation. *)
type ('cache_key, 'work) work_info = {
  work_item : 'work;
  work_cache_key : 'cache_key option;
};;

(** The signature of a type used for caching operations in this monad. *)
module type Cache_key = sig
  include Gmap.KEY;;
  type some_key = Some_key : 'a t -> some_key;;
  val pp : 'a t Jhupllib.Pp_utils.pretty_printer;;
  val show : 'a t -> string;;
end;;

(** The signature of a work collection module used to order how a symbolic monad
    takes computational steps. *)
module type WorkCollection = sig
  module Work_cache_key : Cache_key;;
  type 'a t;;
  val empty : 'a t;;
  val is_empty : 'a t -> bool;;
  val size : 'a t -> int;;
  val offer : (Work_cache_key.some_key, 'a) work_info -> 'a t -> 'a t;;
  val take : 'a t -> ((Work_cache_key.some_key, 'a) work_info * 'a t) option;;
  val enum : 'a t -> 'a Enum.t
end;;

module QueueWorkCollection(Cache_key : Cache_key)
  : WorkCollection with module Work_cache_key = Cache_key;;

module CacheKeyPriorityQueueWorkCollection
    (Cache_key : Cache_key)
    (Priority : Interfaces.OrderedType with type t = Cache_key.some_key option)
  : WorkCollection with module Work_cache_key = Cache_key;;

(** The specification of a symbolic monad. *)
module type Spec = sig
  (** A definition of the type used as a caching key. *)
  module Cache_key : Cache_key;;
  (** The work collection to use during computation. *)
  module Work_collection
    : WorkCollection with module Work_cache_key = Cache_key;;
end;;

(** The interface of a symbolic monad. *)
module type S = sig
  (** The specification for this symbolic monad. *)
  module Spec : Spec;;

  (** The type describing a computation in this monad.  This type does not include
      a state; it is waiting to be run. *)
  type 'a m;;

  (** The return operation. *)
  val return : 'a -> 'a m;;

  (** The bind operation. *)
  val bind : 'a m -> ('a -> 'b m) -> 'b m;;

  (** A zero operation.  Produces an empty value containing no computations. *)
  val zero : unit -> 'a m;;

  (** Non-deterministic selection. *)
  val pick : 'a Enum.t -> 'a m;;

  (** Computational suspension.  When stepping the evaluation of a monadic value,
      invocations of this function will mark the completion of a step. *)
  val pause : unit -> unit m;;

  (** Caches the value produced by the provided monadic computation using a
      particular key.  The first call to this routine will register the
      evaluation of the provided monadic computation in the work queue and, once
      it has been stepped to completion, will store the resulting value in a
      cache and resume this computation with that value.  Further calls to this
      routine with the same cache key will ignore the provided monadic
      computation and simply use any previously computed value.  If a cached
      value is being computed, all computations which depend upon it will block.
      This cache is shared among all threads of non-deterministic computation in
      this monad. *)
  val cache : 'a Spec.Cache_key.t -> 'a m -> 'a m;;

  (** Records a path decision for the provided variable.  If the provided search
      path is valid in this environment, unit is returned in the environment.
      If the provided search path conflicts with a previous selection, the
      environment is destroyed.  The first symbol is the variable which is being
      mapped; the remaining arguments are the components of the wiring node. *)
  val record_decision :
    Relative_stack.t -> Ident.t -> clause -> Ident.t -> unit m;;

  (** Stores a constraint in this environment's constraint set. *)
  val record_constraint : Constraint.t -> unit m;;

  (** Checks that a monadic value's constraints are solvable.  For each
      non-deterministic path in the provided monadic value, a solution is
      attempted for the constraints.  Any paths with unsolvable constraints are
      zeroed out; the remaining paths exist in the returned monadic value (if
      any). *)
  val check_constraints : 'a m -> 'a m;;

  (* **** Evaluation interface **** *)

  (** The type describing a running evaluation of a computation in this monad.
      This value represents all non-deterministic outcomes of a monadic value.
      As an evaluation is stepped, it produces completed values and may or may
      not terminate. *)
  type 'a evaluation;;

  (** A type describing a single evaluation result. *)
  type 'a evaluation_result =
    { er_value : 'a;
      er_solver : Solver.t;
      er_evaluation_steps : int;
      er_result_steps : int;
    };;

  (** Initializes a computation in this monad.  This is similar to the "run"
      routines of standard monads except that it does not run to completion; it
      runs to the first pause. *)
  val start : 'a m -> 'a evaluation;;

  (** Performs one step of evaluation.  Evaluation continues until all
      non-deterministic outcomes are paused; these paused outcomes are
      represented by the returned evaluation.  The returned enumeration contains
      all completed values discovered in this step together with the formulae
      they induced. *)
  val step :
    ?show_value:('a -> string) ->
    'a evaluation ->
    'a evaluation_result Enum.t * 'a evaluation;;

  (** Determines whether a particular evaluation has completed.  If so,
      stepping the evaluation will never produce additional results.  Note that
      false does not guarantee that further values exist to be produced; it
      only indicates that evaluation is not yet finished. *)
  val is_complete : 'a evaluation -> bool;;
end;;

(** The interface of the functor producing symbolic monads. *)
module Make(Spec : Spec) : S with module Spec = Spec;;
