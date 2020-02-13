open Batteries;;

open Odefa_ast;;
open Odefa_ddpa;;

open Ast;;
open Ddpa_abstract_ast;;

module type Stack = Ddpa_context_stack.Context_stack;;

let name_parsing_functions =
  [
    (* A function for the literally-named modules. *)
    (fun name ->
       match name with
       | "0ddpa" ->
         Some (module Ddpa_unit_stack.Stack : Stack)
       | "1ddpa" ->
         Some (module Ddpa_single_element_stack.Stack : Stack)
       | "2ddpa" ->
         Some (module Ddpa_two_element_stack.Stack : Stack)
       | "ddpaNR" ->
         Some (module Ddpa_nonrepeating_stack.Stack : Stack)
       | "none" -> None
       | _ -> raise Not_found
    )
    ;
    (* A function for parsing kddpa *)
    (fun name ->
       if not @@ String.ends_with name "ddpa" then raise Not_found;
       let num_str = String.sub name 0 @@ String.length name - 4 in
       try
         let num = int_of_string num_str in
         let module Spec : Ddpa_n_element_stack.Spec =
         struct
           let size = num
         end
         in
         let module NStack = Ddpa_n_element_stack.Make(Spec) in
         Some (module NStack : Stack)
       with
       | Failure _ -> raise Not_found
    )
  ];;

let stack_from_name name =
  let rec loop fns =
    match fns with
    | [] -> raise Not_found
    | fn::fns' ->
      begin
        try
          fn name
        with
        | Not_found -> loop fns'
      end
  in
  loop name_parsing_functions
;;

(** Iterate recursively over all clauses in an expression. *)
let rec iterate_abstract_clauses (Abs_expr(acls)) =
  let top_level = List.enum acls in
  let nested = Enum.delay
      (fun () -> Enum.concat @@
        Enum.map (fun e -> Enum.delay (fun () -> iterate_abstract_clauses e)) @@
        Enum.concat @@ List.enum @@ List.map _abs_exprs_of_clause acls)
  in
  Enum.append top_level nested

and _abs_exprs_of_clause (Abs_clause(_,b)) =
  match b with
  | Abs_conditional_body(_,e1,e2)
    -> Enum.append (Enum.singleton e1) (Enum.singleton e2)
  | Abs_value_body(v) ->
    _abs_exprs_of_value v
  | Abs_var_body _
  | Abs_appl_body _
  | Abs_input_body
  | Abs_match_body _
  | Abs_projection_body _
  | Abs_binary_operation_body _ -> Enum.empty ()

and _abs_exprs_of_value v =
  match v with
  | Abs_value_record _ -> Enum.empty ()
  | Abs_value_function(Abs_function_value(_,e)) -> Enum.singleton e
  | Abs_value_int
  | Abs_value_bool _ -> Enum.empty ()
;;

let last_var_of (Expr(cls)) =
  let Clause(x,_) = List.last cls in x
;;
