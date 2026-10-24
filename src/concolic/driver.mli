
module Test_result :
  sig
    type t =
      | Found_abort of Branch.t * Jil_input.t list (* Found an abort at this branch using these inputs, where the inputs are in the order they're given *)
      | Type_mismatch of Jayil.Ast.Ident_new.t * Jil_input.t list (* Proposed addition for removing instrumentation *)
      | Exhausted               (* Ran all possible tree paths, and no paths were too deep *)
      | Exhausted_pruned_tree   (* Ran all possible tree paths up to the given max depth *)
      | Timeout                 (* total evaluation timeout *)

    val to_string : t -> string
    (** [to_string t] is a capitalized string for [t], with an underscore *)

    val merge : t -> t -> t
    (** [merge a b] is the more information of the two [a] and [b]. *)
  end

val test_expr : ?print_result:bool -> (Jayil.Ast.expr -> Test_result.t) Options.Fun.t
(** [test expr] is the result where [expr] is the JIL AST. *)

val test : (string -> Test_result.t) Options.Fun.t
(** [test filename] is the result where [filename] is a jil or bjy file name. *)