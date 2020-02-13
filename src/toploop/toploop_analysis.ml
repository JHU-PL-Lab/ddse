open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_ddpa;;

open Ast;;
open Toploop_analysis_types;;
open Toploop_ddpa_wrapper_types;;
open Toploop_utils;;
open Ddpa_abstract_ast;;
open Ddpa_graph;;
open Ddpa_utils;;

module Make(DDPA_wrapper : DDPA_wrapper) =
struct
  module DDPA_wrapper = DDPA_wrapper;;

  let find_errors analysis =
    let open Nondeterminism.Nondeterminism_monad in
    enum @@
    let%bind acl =
      analysis
      |> DDPA_wrapper.expression_of
      |> lift_expr
      |> iterate_abstract_clauses
      |> pick_enum
    in
    let Abs_clause(x_clause,b) = acl in
    let lookup x =
      analysis
      |> DDPA_wrapper.values_of_variable_from x (Unannotated_clause(acl))
      |> Abs_value_set.enum
      |> pick_enum
    in
    match b with
    | Abs_value_body _
    | Abs_var_body _
    | Abs_input_body
    | Abs_conditional_body _
    | Abs_match_body _ ->
      (* There's nothing this body that can be inconsistent. *)
      zero ()
    | Abs_projection_body(x,i) ->
      let%bind v = lookup x in
      begin
        match v with
        | Abs_value_record(Abs_record_value(m)) ->
          if Ident_map.mem i m
          then zero ()
          else return @@ Projection_of_absent_label(x_clause,x,v,i)
        | _ -> return @@ Projection_of_non_record(x_clause,x,v)
      end
    | Abs_appl_body(xf,xa) ->
      let%bind v = lookup xf in
      begin
        match v with
        | Abs_value_function _ -> zero ()
        | _ ->
          let filtvs =
            lookup xa
            |> Nondeterminism.Nondeterminism_monad.enum
            |> Ddpa_abstract_ast.Abs_value_set.of_enum
          in
          return @@ Application_of_non_function(x_clause,xf,v,filtvs)
      end
    | Abs_binary_operation_body(x1,op,x2) ->
      let%bind v1 = lookup x1 in
      let%bind v2 = lookup x2 in
      let is_valid = Option.is_some (abstract_binary_operation op v1 v2) in
      if is_valid
      then zero ()
      else return @@
        Invalid_binary_operation(x_clause, op, x1, v1, x2, v2)
end;;
