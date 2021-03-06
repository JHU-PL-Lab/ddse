(** This module defines a value-parametric priority queue.  The algorithm was
    derived from v4.08 of The OCaml System
    (http://caml.inria.fr/pub/docs/manual-ocaml/moduleexamples.html). *)
(* In accordance with the license of that document, the license for the original
   priority queue source appears below. *)
(*
The OCaml system is copyright © 1996–2013 Institut National de Recherche en Informatique et en Automatique (INRIA). INRIA holds all ownership rights to the OCaml system.

The OCaml system is open source and can be freely redistributed. See the file LICENSE in the distribution for licensing information.

The present documentation is copyright © 2013 Institut National de Recherche en Informatique et en Automatique (INRIA). The OCaml documentation and user’s manual may be reproduced and distributed in whole or in part, subject to the following conditions:

  * The copyright notice above and this permission notice must be preserved complete on all complete or partial copies.
  * Any translation or derivative work of the OCaml documentation and user’s manual must be approved by the authors in writing before distribution.
  * If you distribute the OCaml documentation and user’s manual in part, instructions for obtaining the complete version of this manual must be included, and a means for obtaining a complete version provided.
  * Small portions may be reproduced as illustrations for reviews or quotes in other works without this permission notice if proper citation is given.
*)

open Batteries;;

(** The signature of a priority queue.  The given priority orders the enqueued
    elements.  Values with a lower priority value are dequeued first. *)
module type PQ = sig
  module Priority : Interfaces.OrderedType;;
  type 'a t;;
  val empty : 'a t;;
  val is_empty : 'a t -> bool;;
  val size : 'a t -> int;;
  val enqueue : Priority.t -> 'a -> 'a t -> 'a t;;
  val dequeue : 'a t -> (Priority.t * 'a * 'a t) option
  val enum : 'a t -> 'a Enum.t
end;;

module Make(Priority : Interfaces.OrderedType)
  : PQ with module Priority = Priority =
struct
  module Priority = Priority;;
  module M = Map.Make(Priority);;
  type 'a t =
    { pq_map : 'a Deque.t M.t;
      pq_size : int
    }
  ;;
  let empty = { pq_map = M.empty; pq_size = 0 };;
  let is_empty pq = M.is_empty pq.pq_map;;
  let size pq = pq.pq_size;;
  let enqueue prio elt pq =
    match M.Exceptionless.find prio pq.pq_map with
    | None ->
      { pq_map = M.add prio (Deque.of_list [elt]) pq.pq_map;
        pq_size = pq.pq_size + 1
      }
    | Some dq ->
      { pq_map = M.add prio (Deque.cons elt dq) pq.pq_map;
        pq_size = pq.pq_size + 1
      }
  ;;
  let dequeue (pq : 'a t) : (Priority.t * 'a * 'a t) option =
    if is_empty pq then None else
      let (smallest_key, smallest_value) = M.min_binding pq.pq_map in
      match Deque.rear smallest_value with
      | None ->
        raise @@ Jhupllib.Utils.Invariant_failure
          "priority entry in PQ with no values"
      | Some(dq', result) ->
        let pq_map' =
          if Deque.is_empty dq' then
            M.remove smallest_key pq.pq_map
          else
            M.add smallest_key dq' pq.pq_map
        in
        Some(smallest_key, result,
             { pq_map = pq_map'; pq_size = pq.pq_size - 1 }
            )
  ;;
  let enum (pq : 'a t) : 'a Enum.t =
    pq.pq_map
    |> M.enum
    |> Enum.map snd
    |> Enum.map Deque.enum
    |> Enum.concat
  ;;
end;;
