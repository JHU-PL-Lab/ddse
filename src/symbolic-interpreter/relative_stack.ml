open Batteries;;
open Jhupllib;;
open Odefa_ast;;

open Ast;;
open Ast_pp;;
open Pp_utils;;

(** The type of concrete stacks in the symbolic interpreter. *)
type concrete_stack =
    Concrete_stack of Ident.t list
[@@ocaml.unboxed]
[@@deriving eq, ord, show, to_yojson]
;;

(** The type of relative stacks in the symbolic interpreter. *)
type t =
  | Relative_stack of Ident.t list * Ident.t list
[@@deriving eq, ord, to_yojson]
;;

let pp : t pretty_printer =
  fun formatter (Relative_stack(costk,stk)) ->
  Format.pp_print_char formatter '[';
  costk |> List.iter
    (fun i -> Format.pp_print_char formatter '-'; pp_ident formatter i);
  stk |> List.iter
    (fun i -> Format.pp_print_char formatter '+'; pp_ident formatter i);
  Format.pp_print_char formatter ']';
;;
let show = pp_to_string pp;;

let empty = Relative_stack([],[]);;

(* NOTE: this implementation canonicalizes the stack in a way that the
   specification does not: push(pop(C,x),x) = C.  This should be fine, as this
   should never actually happen during the reverse evaluation of a program.  The
   specification picks its form to ease its proof burden.  Here, we select the
   canonicalizing version as it makes it easier to derive relative stacks from
   two absolute stacks. *)
let push (Relative_stack(costk,stk)) (x : Ident.t) : t option =
  match costk with
  | [] ->
    Some(Relative_stack(costk, x :: stk))
  | x' :: costk' ->
    if equal_ident x x' then
      Some(Relative_stack(costk', stk))
    else
      Some(Relative_stack(costk, x :: stk))
;;

let pop (Relative_stack(costk,stk)) (x : Ident.t) : t option =
  match stk with
  | [] ->
    Some(Relative_stack(x :: costk, stk))
  | x' :: stk' ->
    if equal_ident x x' then Some(Relative_stack(costk, stk')) else None
;;

(** This is an implementation of the Stackize function from the paper.  It
    assumes that the stack is relative to a point within the program *and* that
    the relative stack describes a top-level context.  It produces a concrete
    stack from those assumptions. *)
let stackize (Relative_stack(costk,stk)) : concrete_stack =
  if not @@ List.is_empty stk then begin
    raise @@ Jhupllib.Utils.Invariant_failure
      "Non-empty positive stack in Stackize!";
  end;
  Concrete_stack(List.rev costk)
;;

let length (Relative_stack(costk, stk)) : int =
  List.length costk + List.length stk
;;

let to_lists (Relative_stack(costk, stk)) : Ident.t list * Ident.t list =
  costk, stk
;;

(** Dictionaries with relative stacks as keys. *)
module Map = struct
  module RS = struct
    type _t = t;;
    type t = _t;;
    let compare = compare;;
    let pp = pp;;
  end;;
  module M = Map.Make(RS);;
  include M;;
  include Pp_utils.Map_pp(M)(RS);;
end;;
