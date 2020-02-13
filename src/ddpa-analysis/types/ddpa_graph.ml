(**
   A module defining data structures and basic operations to form a DDPA graph.
*)

open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast;;
open Ddpa_abstract_ast;;
open Pp_utils;;

type ddpa_edge =
  | Ddpa_edge of annotated_clause * annotated_clause
  [@@deriving ord, show, to_yojson]
;;

module Ddpa_edge =
struct
  type t = ddpa_edge
  let compare = compare_ddpa_edge
  let pp = pp_ddpa_edge
  let to_yojson = ddpa_edge_to_yojson
end;;

(*
  Creating the graph data type inside of a module.  This allows us to keep the
  graph data type intentionally abstract, thus permitting safe indexing and
  other helpful features.
*)
module type Graph_sig =
sig
  type ddpa_graph

  val empty : ddpa_graph

  val add_edge : ddpa_edge -> ddpa_graph -> ddpa_graph

  val edges_of : ddpa_graph -> ddpa_edge Enum.t

  val has_edge : ddpa_edge -> ddpa_graph -> bool

  val edges_from : annotated_clause -> ddpa_graph -> ddpa_edge Enum.t

  val edges_to : annotated_clause -> ddpa_graph -> ddpa_edge Enum.t

  val preds : annotated_clause -> ddpa_graph -> annotated_clause Enum.t

  val succs : annotated_clause -> ddpa_graph -> annotated_clause Enum.t

  val to_yojson : ddpa_graph -> Yojson.Safe.t
end;;

(* TODO: improve the performance of this implementation! *)
module Graph_impl : Graph_sig =
struct
  module Ddpa_edge_set =
  struct
    module Impl = Set.Make(Ddpa_edge);;
    include Impl;;
    include Pp_utils.Set_pp(Impl)(Ddpa_edge);;
    include Yojson_utils.Set_to_yojson(Impl)(Ddpa_edge);;
  end;;

  type ddpa_graph = Graph of Ddpa_edge_set.t [@@deriving to_yojson];;

  let empty = Graph(Ddpa_edge_set.empty);;

  let add_edge edge (Graph(s)) = Graph(Ddpa_edge_set.add edge s);;

  let edges_of (Graph(s)) = Ddpa_edge_set.enum s;;

  let has_edge edge (Graph(s)) = Ddpa_edge_set.mem edge s;;

  let edges_from acl (Graph(s)) =
    Ddpa_edge_set.enum s
    |> Enum.filter (fun (Ddpa_edge(acl',_)) -> equal_annotated_clause acl acl')
  ;;

  let succs acl g =
    edges_from acl g |> Enum.map (fun (Ddpa_edge(_,acl)) -> acl)
  ;;

  let edges_to acl (Graph(s)) =
    Ddpa_edge_set.enum s
    |> Enum.filter (fun (Ddpa_edge(_,acl')) -> equal_annotated_clause acl acl')
  ;;

  let preds acl g =
    edges_to acl g |> Enum.map (fun (Ddpa_edge(acl,_)) -> acl)
  ;;

  let to_yojson = ddpa_graph_to_yojson;;
end;;

include Graph_impl;;

let pp_ddpa_graph formatter g =
  pp_concat_sep_delim "{" "}" ", " pp_ddpa_edge formatter @@ edges_of g
;;

let rec lift_expr (Expr(cls)) =
  Abs_expr(List.map lift_clause cls)

and lift_clause (Clause(x,b)) =
  Abs_clause(lift_var x, lift_clause_body b)

and lift_clause_body b =
  match b with
  | Value_body v -> Abs_value_body(lift_value v)
  | Var_body x -> Abs_var_body(lift_var x)
  | Input_body -> Abs_input_body
  | Appl_body(x,x') -> Abs_appl_body(lift_var x, lift_var x')
  | Conditional_body(x,e1,e2) ->
    Abs_conditional_body(lift_var x,lift_expr e1,lift_expr e2)
  | Match_body(x,p) ->
    Abs_match_body(lift_var x,p)
  | Projection_body(x,l) ->
    Abs_projection_body(lift_var x,l)
  | Binary_operation_body(x1,op,x2) ->
    Abs_binary_operation_body(lift_var x1, op, lift_var x2)

and lift_value v =
  match v with
  | Value_record r -> Abs_value_record(lift_record_value r)
  | Value_function f -> Abs_value_function(lift_function_value f)
  | Value_int _ -> Abs_value_int
  | Value_bool b -> Abs_value_bool b

and lift_var (Var(i,_)) =
  Abs_var i

and lift_function_value (Function_value(x,e)) =
  Abs_function_value(lift_var x, lift_expr e)

and lift_record_value (Record_value m) =
  Abs_record_value(Ident_map.map lift_var m)
;;
