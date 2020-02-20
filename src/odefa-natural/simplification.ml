(** This module defines a routine which simplifies an Odefa ANF AST by removing
    unnecessary variable aliases. *)

open Batteries;;

open Odefa_ast;;

open Ast;;
open Ast_tools;;

let eliminate_alias_pass (e : expr) : expr =
  e |> transform_exprs_in_expr
    (fun expr ->
       let Expr(cls) = expr in
       (* Identify all immediate aliases except the return value.  (We might
          need to preserve its name.) *)
       let aliases =
         cls
         |> List.take (List.length cls - 1)
         |> List.filter_map
           (function
             | Clause(x,Var_body(x')) -> Some(x,x')
             | _ -> None
           )
       in
       (* The aliases list contains a series of alias clauses to eliminate from
          this expression.  To do so, we must substitute all uses of those
          variables in the expression. *)
       let replacement_map = Var_map.of_enum @@ List.enum aliases in
       let expr' =
         map_expr_vars (fun x -> Var_map.find_default x x replacement_map) expr
       in
       (* Now that we've done this, we need to get rid of the old aliases. *)
       let Expr cls' = expr' in
       let cls'' =
         cls'
         |> List.filter
           (function
             | (Clause(x,Var_body(x'))) -> not @@ equal_var x x'
             | _ -> true)
       in
       let e'' = Expr cls'' in
       e''
    )
;;

let rec eliminate_aliases (e : expr) : expr =
  let e' = eliminate_alias_pass e in
  if equal_expr e e' then e' else eliminate_aliases e'
;;
