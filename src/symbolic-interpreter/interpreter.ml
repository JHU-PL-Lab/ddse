open Batteries;;
open Jhupllib;;
open Odefa_ast;;
open Odefa_ddpa;;

open Ast;;
open Ast_pp;;
open Ddpa_abstract_ast;;
open Ddpa_graph;;
open Ddpa_utils;;
open Interpreter_types;;
open Logger_utils;;

let lazy_logger = make_lazy_logger "Symbolic_interpreter.Interpreter";;

type exploration_policy =
  | Explore_breadth_first
  | Explore_smallest_relative_stack_length
  | Explore_least_relative_stack_repetition
;;

(** This type describes the information which must be in context during lookup. *)
type lookup_environment = {
  le_cfg : ddpa_graph;
  (** The DDPA CFG to use during lookup. *)

  le_clause_mapping : clause Ident_map.t;
  (** A mapping from identifiers to the concrete clauses which define them. *)

  le_clause_predecessor_mapping : clause Ident_map.t;
  (** A mapping from clauses (represented by the identifier they define) to the
      concrete clauses which appear immediately *before* them.  The first clause
      in each expression does not appear in this map. *)

  le_function_parameter_mapping : function_value Ident_map.t;
  (** A mapping from function parameter variables to the functions which declare
      them. *)

  le_function_return_mapping : function_value Ident_map.t;
  (** A mapping from function return variables to the functions which declare
      them. *)

  le_first_var : Ident.t;
  (** The identifier which represents the first defined variable in the
      program. *)
};;

(**
   Given a program and its corresponding CFG, constructs an appropriate lookup
   environment.
*)
let prepare_environment (e : expr) (cfg : ddpa_graph)
  : lookup_environment =
  let rec enum_all_functions_in_expr expr : function_value Enum.t =
    let Expr(clauses) = expr in
    Enum.concat @@ Enum.map enum_all_functions_in_clause @@ List.enum clauses
  and enum_all_functions_in_clause clause : function_value Enum.t =
    let Clause(_,body) = clause in
    enum_all_functions_in_body body
  and enum_all_functions_in_body body : function_value Enum.t =
    match body with
    | Value_body v ->
      enum_all_functions_in_value v
    | Var_body _
    | Input_body
    | Appl_body _
    | Binary_operation_body (_, _, _) ->
      Enum.empty ()
    | Conditional_body (_, e1, e2) ->
      Enum.append
        (enum_all_functions_in_expr e1) (enum_all_functions_in_expr e2)
    | Match_body (_, _)
    | Projection_body (_, _) ->
      Enum.empty ()
  and enum_all_functions_in_value value : function_value Enum.t =
    match value with
    | Value_record _ -> Enum.empty ()
    | Value_function(Function_value(_,e) as f) ->
      Enum.append (Enum.singleton f) @@ enum_all_functions_in_expr e
    | Value_int _
    | Value_bool _ -> Enum.empty ()
  in
  let function_parameter_mapping, function_return_mapping =
    enum_all_functions_in_expr e
    |> Enum.fold
      (fun (pm,rm) (Function_value(Var(p,_),Expr(clss)) as f) ->
         let pm' = Ident_map.add p f pm in
         let retvar =
           clss
           |> List.last
           |> (fun (Clause(Var(r,_),_)) -> r)
         in
         let rm' = Ident_map.add retvar f rm in
         (pm', rm')
      )
      (Ident_map.empty, Ident_map.empty)
  in
  let clause_mapping =
    Ast_tools.flatten e
    |> List.enum
    |> Enum.fold
      (fun map (Clause(Var(x,_),_) as c) ->
         Ident_map.add x c map
      )
      Ident_map.empty
  in
  let rec expr_flatten ((Expr clauses) as expr) : expr list =
    expr ::
    (clauses
     |>
     List.map
       (fun (Clause(_,b)) ->
          match b with
          | Value_body (Value_function(Function_value(_,e))) -> expr_flatten e
          | Value_body _
          | Var_body _
          | Input_body
          | Appl_body (_, _)
          | Match_body (_, _)
          | Projection_body (_, _)
          | Binary_operation_body (_, _, _) -> []
          | Conditional_body (_, e1, e2) ->
            e1 :: e2 :: expr_flatten e1 @ expr_flatten e2
       )
     |> List.concat
    )
  in
  let clause_predecessor_mapping =
    expr_flatten e
    |> List.enum
    |> Enum.map
      (fun (Expr clauses) ->
         let c1 = List.enum clauses in
         let c2 = List.enum clauses in
         Enum.drop 1 c1;
         Enum.combine (c1,c2)
         |> Enum.map
           (fun (Clause(Var(x,_),_),clause) -> (x,clause))
      )
    |> Enum.concat
    |> Ident_map.of_enum
  in
  let first_var =
    e
    |> (fun (Expr cls) -> cls)
    |> List.first
    |> (fun (Clause(Var(x,_),_)) -> x)
  in
  { le_cfg = cfg;
    le_clause_mapping = clause_mapping;
    le_clause_predecessor_mapping = clause_predecessor_mapping;
    le_function_parameter_mapping = function_parameter_mapping;
    le_function_return_mapping = function_return_mapping;
    le_first_var = first_var;
  }
;;

(* The type of the symbolic interpreter's cache key.  The arguments are the
   lookup stack, the clause identifying the program point at which lookup is
   proceeding, and the relative call stack at this point.
*)
type 'a interpreter_cache_key =
  | Cache_lookup :
      Ident.t list * annotated_clause * Relative_stack.t ->
      (symbol * Relative_stack.concrete_stack) interpreter_cache_key
;;

module Interpreter_cache_key
  : Symbolic_monad.Cache_key with type 'a t = 'a interpreter_cache_key =
struct
  type 'a t = 'a interpreter_cache_key;;
  type some_key = Some_key : 'a t -> some_key;;

  let compare : type a b. a t -> b t -> (a, b) Gmap.Order.t = fun k1 k2 ->
    match k1, k2 with
    | Cache_lookup(lookup_stack_1, acl1, relative_stack_1),
      Cache_lookup(lookup_stack_2, acl2, relative_stack_2) ->
      let c = List.compare Ident.compare lookup_stack_1 lookup_stack_2 in
      if c < 0 then Lt else
      if c > 0 then Gt else
        let c = Annotated_clause.compare acl1 acl2 in
        if c < 0 then Lt else
        if c > 0 then Gt else
          let c =
            Relative_stack.compare relative_stack_1 relative_stack_2
          in
          if c < 0 then Lt else
          if c > 0 then Gt else
            Eq
  ;;

  let pp (type a) formatter (key : a t) =
    match key with
    | Cache_lookup(lookup_stack, acl, relative_stack) ->
      Format.fprintf formatter "lookup(%s,%s,%s)"
        (Jhupllib.Pp_utils.pp_to_string
           (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack)
        (show_brief_annotated_clause acl)
        (Relative_stack.show relative_stack)
  ;;

  let show key = Jhupllib.Pp_utils.pp_to_string pp key;;
end;;

module Interpreter_cache_key_smallest_relative_stack_length_ordering = struct
  open Interpreter_cache_key;;
  type t = some_key option;;
  let compare (a : t) (b : t) : int =
    match a, b with
    | None, None -> 0
    | Some _, None -> 1
    | None, Some _ -> -1
    | Some(Some_key(Cache_lookup(_, _, relative_stack_1))),
      Some(Some_key(Cache_lookup(_, _, relative_stack_2))) ->
      Stdlib.compare
        (Relative_stack.length relative_stack_1)
        (Relative_stack.length relative_stack_2)
  ;;
end;;

module Interpreter_cache_key_least_relative_stack_repetition_ordering = struct
  open Interpreter_cache_key;;
  type t = some_key option;;
  let reps (a : t) =
    match a with
    | None -> -1
    | Some(Some_key(Cache_lookup(_, _, relstack))) ->
      let (costk, stk) = Relative_stack.to_lists relstack in
      let occurrences =
        (costk @ stk)
        |> List.fold_left
          (fun a e -> Ident_map.modify_def 0 e (fun n -> n + 1) a)
          Ident_map.empty
      in
      let repetitions =
        occurrences
        |> Ident_map.enum
        |> Enum.map (fun (_,v) -> if v < 2 then 0 else v - 1)
        |> Enum.sum
      in
      repetitions
  ;;
  let compare (a : t) (b : t) : int =
    Stdlib.compare (reps a) (reps b)
  ;;
end;;

type evaluation_result = {
  er_solver : Solver.t;
  er_stack : Relative_stack.concrete_stack;
  er_solution : (symbol -> value option);
};;

exception Invalid_query of string;;

module type Interpreter =
sig
  type evaluation;;
  val start : ddpa_graph -> expr -> ident -> evaluation;;
  val step : evaluation -> evaluation_result list * evaluation option;;
end;;

module Make
    (C : Symbolic_monad.WorkCollection
     with module Work_cache_key = Interpreter_cache_key)
  : Interpreter =
struct
  module M = Symbolic_monad.Make(
    struct
      module Cache_key = Interpreter_cache_key;;
      module Work_collection = C;;
    end);;

  (* NOTE 1: rather than introducing a "stack=" SAT formula, we instead have
     lookup return a pair.  The "stack=" formula in the spec is a hack to avoid
     dealing with pairs in the lookup definition since the mathematical notation
     is... unpleasant.

     This incurs an obligation: we technically need to show that all of the
     stacks are the same.  In the "stack=" variation, two distinct stacks would
     lead to unsatisfiable formulae; here, if two different stacks are returned,
     we must zero the computation.  Conveniently, however, this never occurs:
     all lookups respect the stack discipline and the function call decision set
     is shared between them.  Therefore, all stacks *will* be the same; we
     needn't verify, which is good because it'd make the code quite a lot
     sloppier.
  *)
  let rec lookup
      (env : lookup_environment)
      (lookup_stack : Ident.t list)
      (acl0 : annotated_clause)
      (relstack : Relative_stack.t)
    : (symbol * Relative_stack.concrete_stack) M.m =
    let open M in
    let%bind acl1 = pick @@ preds acl0 env.le_cfg in
    let zeromsg msg () =
      lazy_logger `trace
        (fun () ->
           Printf.sprintf "ZERO (%s) for lookup of\n  %s\n  with stack %s\n  at %s\n  after %s\n"
             msg
             (Jhupllib.Pp_utils.pp_to_string
                (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack)
             (Jhupllib.Pp_utils.pp_to_string Relative_stack.pp relstack)
             (Jhupllib.Pp_utils.pp_to_string
                pp_brief_annotated_clause acl0)
             (Jhupllib.Pp_utils.pp_to_string
                pp_brief_annotated_clause acl1)
        );
      zero ()
    in
    let _ = zeromsg in
    let%bind () = pause () in
    let recurse
        (lookup_stack' : Ident.t list)
        (acl0' : annotated_clause)
        (relstack' : Relative_stack.t) =
      lazy_logger `trace
        (fun () ->
           Printf.sprintf
             "From lookup of\n  %s\n  with stack %s\n  at %s\n  after %s\nRecursively looking up\n  %s\n  with stack %s\n  at %s\n"
             (Jhupllib.Pp_utils.pp_to_string
                (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack)
             (Jhupllib.Pp_utils.pp_to_string Relative_stack.pp relstack)
             (Jhupllib.Pp_utils.pp_to_string
                pp_brief_annotated_clause acl0)
             (Jhupllib.Pp_utils.pp_to_string
                pp_brief_annotated_clause acl1)
             (Jhupllib.Pp_utils.pp_to_string
                (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack')
             (Jhupllib.Pp_utils.pp_to_string Relative_stack.pp relstack')
             (Jhupllib.Pp_utils.pp_to_string
                pp_brief_annotated_clause acl0')
        );
      cache (Cache_lookup(lookup_stack', acl0', relstack')) @@
      (* check_formulae @@ *)
      lookup env lookup_stack' acl0' relstack'
    in
    lazy_logger `trace
      (fun () ->
         Printf.sprintf
           "Looking up\n  %s\n  with stack %s\n  at %s\n  after %s\n"
           (Jhupllib.Pp_utils.pp_to_string
              (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack)
           (Jhupllib.Pp_utils.pp_to_string Relative_stack.pp relstack)
           (Jhupllib.Pp_utils.pp_to_string pp_brief_annotated_clause acl0)
           (Jhupllib.Pp_utils.pp_to_string pp_brief_annotated_clause acl1)
      );
    let rule_computations =
      [
        (* ### Value Discovery rule ### *)
        begin
          (* Lookup stack must be a singleton *)
          let%orzero [lookup_var] = lookup_stack in
          (* This must be a value assignment clause defining that variable. *)
          let%orzero Unannotated_clause(
              Abs_clause(Abs_var x,Abs_value_body _)) = acl1
          in
          [%guard equal_ident x lookup_var];
          (* Get the value v assigned here. *)
          let%orzero (Clause(_,Value_body(v))) =
            Ident_map.find x env.le_clause_mapping
          in
          (* Induce the resulting formula *)
          let lookup_symbol = Symbol(lookup_var, relstack) in
          let%bind constraint_value =
            match v with
            | Value_record(Record_value m) ->
              (* The variables in m are unfreshened and local to this context.
                 We can look up each of their corresponding symbols and then
                 put them in a new dictionary for the constraint. *)
              let mappings =
                m
                |> Ident_map.enum
                |> Enum.map
                  (fun (lbl, Var(x,_)) ->
                     (* We ignore the stacks here intentionally; see note 1 above. *)
                     (* TODO: make sure note 1 justifies this case! *)
                     let%bind (symbol, _) = recurse [x] acl1 relstack in
                     return (lbl, symbol)
                  )
                |> List.of_enum
              in
              (* If only we could generalize monadic sequencing... *)
              let rec loop mappings map =
                match mappings with
                | [] -> return map
                | h::t ->
                  let%bind (k,v) = h in
                  loop t (Ident_map.add k v map)
              in
              let%bind record_map = loop mappings Ident_map.empty in
              return @@ Constraint.Record(record_map)
            | Value_function f -> return @@ Constraint.Function f
            | Value_int n -> return @@ Constraint.Int n
            | Value_bool b -> return @@ Constraint.Bool b
          in
          let%bind () = record_constraint @@
            Constraint.Constraint_value(lookup_symbol, constraint_value)
          in
          (* If we're at the top of the program, we're finished.  Otherwise, start
             a search for the first variable. *)
          if equal_ident lookup_var env.le_first_var then begin
            (* Then we've found the start of the program!  Build an
               appropriate concrete stack. *)
            lazy_logger `trace
              (fun () -> "This lookup complete; top of program reached.");
            return (lookup_symbol, Relative_stack.stackize relstack)
          end else begin
            lazy_logger `trace
              (fun () ->
                 "This lookup complete; resuming to top of program.");
            let%bind (_, stack) =
              recurse [env.le_first_var] acl1 relstack
            in
            return (lookup_symbol, stack)
          end
        end;
        (* ### Input rule ### *)
        begin
          (* Lookup stack must be a singleton *)
          let%orzero [lookup_var] = lookup_stack in
          (* This must be an input clause defining that variable. *)
          let%orzero Unannotated_clause(
              Abs_clause(Abs_var x,Abs_input_body)) = acl1
          in
          [%guard equal_ident x lookup_var];
          (* Induce the resulting formula *)
          let lookup_symbol = Symbol(lookup_var, relstack) in
          let%bind () = record_constraint @@
            Constraint.Constraint_binop(
              SpecialSymbol SSymTrue,
              lookup_symbol,
              Binary_operator_equal_to,
              lookup_symbol)
          in
          (* If we're at the top of the program, we're finished.  Otherwise, start
             a search for the first variable. *)
          if equal_ident lookup_var env.le_first_var then begin
            (* Then we've found the start of the program!  Build an
               appropriate concrete stack. *)
            lazy_logger `trace
              (fun () -> "This lookup complete; top of program reached.");
            return (lookup_symbol, Relative_stack.stackize relstack)
          end else begin
            lazy_logger `trace
              (fun () ->
                 "This lookup complete; resuming to top of program.");
            let%bind (_, stack) =
              recurse [env.le_first_var] acl1 relstack
            in
            return (lookup_symbol, stack)
          end
        end;
        (* ### Value Discard rule ### *)
        begin
          (* Lookup stack must NOT be a singleton *)
          (* TODO: verify that this still has the desired intent.  What if
             query_element isn't a variable? *)
          let%orzero lookup_var :: query_element :: lookup_stack' =
            lookup_stack
          in
          (* This must be a value assignment clause defining that variable. *)
          let%orzero Unannotated_clause(
              Abs_clause(Abs_var x,Abs_value_body _)) = acl1
          in
          [%guard equal_ident x lookup_var];
          (* We found the variable, so toss it and keep going. *)
          recurse (query_element :: lookup_stack') acl1 relstack
        end;
        (* ### Alias rule ### *)
        begin
          (* Grab variable from lookup stack *)
          let%orzero lookup_var :: lookup_stack' = lookup_stack in
          (* This must be an alias clause defining that variable. *)
          let%orzero Unannotated_clause(
              Abs_clause(Abs_var x,Abs_var_body(Abs_var x'))) =
            acl1
          in
          [%guard equal_ident x lookup_var];
          (* Look for the alias now. *)
          recurse (x' :: lookup_stack') acl1 relstack
        end;
        (* ### Binop rule ### *)
        begin
          (* Grab variable from lookup stack *)
          let%orzero lookup_var :: lookup_stack' = lookup_stack in
          (* This must be a binary operator clause assigning to that variable. *)
          let%orzero Unannotated_clause(
              Abs_clause(Abs_var x, Abs_binary_operation_body(
                  Abs_var x', op, Abs_var x''))) =
            acl1
          in
          [%guard equal_ident x lookup_var];
          (* We ignore the stacks here intentionally; see note 1 above. *)
          let%bind (symbol1, _) = recurse [x'] acl1 relstack in
          let%bind (symbol2, _) = recurse [x''] acl1 relstack in
          let lookup_symbol = Symbol(lookup_var, relstack) in
          let%bind () = record_constraint @@
            Constraint.Constraint_binop(lookup_symbol, symbol1, op, symbol2)
          in
          (* The "further" clause in the Binop rule says that, if the lookup
             stack is non-empty, we have to look that stuff up too.  That
             should never happen because none of our operators operate on
             functions and functions are the only non-bottom elements in the
             lookup stack.  So instead, we'll just skip the check here and
             play defensively; it saves us a bind. *)
          if not @@ List.is_empty lookup_stack' then begin
            raise @@ Jhupllib.Utils.Not_yet_implemented
              "Non-singleton lookup stack in Binop rule!"
          end;
          let%bind (_, stack) =
            recurse [env.le_first_var] acl1 relstack
          in
          return (lookup_symbol, stack)
        end;
        (* ### Function Enter Parameter rule ### *)
        begin
          (* Grab variable from lookup stack *)
          let%orzero lookup_var :: lookup_stack' = lookup_stack in
          (* This must be a binding enter clause which defines our lookup
             variable. *)
          let%orzero Binding_enter_clause(Abs_var x,Abs_var x',c) = acl1 in
          [%guard equal_ident lookup_var x];
          (* Build the popped relative stack. *)
          let%orzero Abs_clause(Abs_var xr,Abs_appl_body(Abs_var xf,_)) = c in
          let%orzero Some relstack' = Relative_stack.pop relstack xr in
          (* Record this wiring decision. *)
          let cc = Ident_map.find xr env.le_clause_mapping in
          let%bind () = record_decision relstack x cc x' in
          (* Look up the definition of the function. *)
          let%bind (function_symbol, _) = recurse [xf] acl1 relstack' in
          (* Require this function be assigned to that variable. *)
          let fv = Ident_map.find x env.le_function_parameter_mapping in
          let%bind () = record_constraint @@
            Constraint.Constraint_value(function_symbol, Constraint.Function fv)
          in
          (* Proceed to look up the argument in the calling context. *)
          recurse (x' :: lookup_stack') acl1 relstack'
        end;
        (* ### Function Enter Non-Local rule ### *)
        begin
          (* Grab variable from lookup stack *)
          let%orzero x :: lookup_stack' = lookup_stack in
          (* This must be a binding enter clause which DOES NOT define our
             lookup variable. *)
          let%orzero Binding_enter_clause(Abs_var x'',Abs_var x',c) = acl1 in
          [%guard not @@ equal_ident x x''];
          (* Build the popped relative stack. *)
          let%orzero Abs_clause(Abs_var xr,Abs_appl_body(Abs_var xf,_)) = c in
          let%orzero Some relstack' = Relative_stack.pop relstack xr in
          (* Record this wiring decision. *)
          let cc = Ident_map.find xr env.le_clause_mapping in
          let%bind () = record_decision relstack x'' cc x' in
          (* Look up the definition of the function. *)
          let%bind (function_symbol, _) =
            recurse [xf] acl1 relstack'
          in
          (* Require this function be assigned to that variable. *)
          let fv = Ident_map.find x'' env.le_function_parameter_mapping in
          let%bind () = record_constraint @@
            Constraint.Constraint_value(function_symbol, Constraint.Function fv)
          in
          (* Proceed to look up the variable in the context of the function's
             definition. *)
          recurse
            (xf :: x :: lookup_stack')
            acl1
            relstack'
        end;
        (* ### Function Exit rule ### *)
        begin
          (* Grab variable from lookup stack *)
          let%orzero lookup_var :: lookup_stack' = lookup_stack in
          (* This must be a binding exit clause which defines our lookup
             variable. *)
          let%orzero Binding_exit_clause(Abs_var x, Abs_var x', c) = acl1 in
          [%guard equal_ident x lookup_var];
          (* Look up the definition point of the function. *)
          let%orzero Abs_clause(Abs_var xr, Abs_appl_body(Abs_var xf, _)) = c in
          let%bind (function_symbol, _) =
            recurse [xf] (Unannotated_clause(c)) relstack
          in
          (* Require this function be assigned to that variable. *)
          let fv = Ident_map.find x' env.le_function_return_mapping in
          let%bind () = record_constraint @@
            Constraint.Constraint_value(function_symbol, Constraint.Function fv)
          in
          (* Proceed to look up the value returned by the function. *)
          let%orzero Some relstack' = Relative_stack.push relstack xr in
          recurse (x' :: lookup_stack') acl1 relstack'
        end;
        (* ### Skip rule ### *)
        begin
          (* Grab variable from lookup stack *)
          let%orzero lookup_var :: _ = lookup_stack in
          (* This must be a variable we AREN'T looking for. *)
          let%orzero Unannotated_clause(Abs_clause(Abs_var x'', _)) = acl1 in
          [%guard not @@ equal_ident x'' lookup_var ];
          (* Even if we're not looking for it, it has to be defined! *)
          let%bind _ = recurse [x''] acl0 relstack in
          recurse lookup_stack acl1 relstack
        end;
        (* ### Conditional Top rule ### *)
        begin
          (* This must be a non-binding enter wiring node for a conditional. *)
          let%orzero Nonbinding_enter_clause(av,c) = acl1 in
          let%orzero Abs_clause(_, Abs_conditional_body(Abs_var x1, _, _)) = c in
          (* Look up the subject symbol. *)
          let%bind (subject_symbol, _) =
            recurse [x1] (Unannotated_clause c) relstack
          in
          (* Require that it has the same value as the wiring node. *)
          let%orzero Abs_value_bool b = av in
          let%bind () = record_constraint @@
            Constraint.Constraint_value(subject_symbol, Constraint.Bool b)
          in
          (* Proceed by moving through the wiring node. *)
          recurse lookup_stack acl1 relstack
        end;
        (* ### Conditional Bottom - True rule ### *)
        begin
          (* Grab variable from lookup stack *)
          let%orzero lookup_var :: lookup_stack' = lookup_stack in
          (* This must be a binding exit clause which defines our lookup
             variable. *)
          let%orzero Binding_exit_clause(Abs_var x, Abs_var x', c) = acl1 in
          [%guard equal_ident x lookup_var];
          (* Ensure that we're considering the true branch *)
          let%orzero Abs_clause(_, Abs_conditional_body(Abs_var x1, e1, _)) = c in
          let Abs_var e1ret = retv e1 in
          [%guard equal_ident x' e1ret];
          (* Look up the subject symbol. *)
          let%bind (subject_symbol, _) =
            recurse [x1] (Unannotated_clause c) relstack
          in
          (* Require that its value matches this conditional branch. *)
          let%bind () = record_constraint @@
            Constraint.Constraint_value(subject_symbol, Constraint.Bool true)
          in
          (* Proceed to look up the value returned by this branch. *)
          recurse (x' :: lookup_stack') acl1 relstack
        end;
        (* ### Conditional Bottom - False rule ### *)
        begin
          (* Grab variable from lookup stack *)
          let%orzero lookup_var :: lookup_stack' = lookup_stack in
          (* This must be a binding exit clause which defines our lookup
             variable. *)
          let%orzero Binding_exit_clause(Abs_var x, Abs_var x', c) = acl1 in
          [%guard equal_ident x lookup_var];
          (* Ensure that we're considering the false branch *)
          let%orzero Abs_clause(_, Abs_conditional_body(Abs_var x1, _, e2)) = c in
          let Abs_var e2ret = retv e2 in
          [%guard equal_ident x' e2ret];
          (* Look up the subject symbol. *)
          let%bind (subject_symbol, _) =
            recurse [x1] (Unannotated_clause c) relstack
          in
          (* Require that its value matches this conditional branch. *)
          let%bind () = record_constraint @@
            Constraint.Constraint_value(subject_symbol, Constraint.Bool false)
          in
          (* Proceed to look up the value returned by this branch. *)
          recurse (x' :: lookup_stack') acl1 relstack
        end;
        (* Record projection handling (not a written rule) *)
        begin
          (* Don't process the record projection unless we're ready to move
             on: we need a variable on top of the stack. *)
          let%orzero lookup_var :: lookup_stack' = lookup_stack in
          (* This must be a record projection clause which defines our
             variable. *)
          let%orzero Unannotated_clause(
              Abs_clause(Abs_var x, Abs_projection_body(Abs_var x', lbl))) =
            acl1
          in
          [%guard equal_ident x lookup_var];
          (* Look up the record itself and identify the symbol it uses. *)
          (* We ignore the stacks here intentionally; see note 1 above. *)
          let%bind (record_symbol, _) = recurse [x'] acl1 relstack in
          (* Now record the constraint that the lookup variable must be the
             projection of the label from that record. *)
          let lookup_symbol = Symbol(lookup_var, relstack) in
          let%bind () = record_constraint @@
            Constraint_projection(lookup_symbol, record_symbol, lbl)
          in
          (* We should have a "further" clause similar to the Binop rule: if the
             lookup stack is non-empty, we have to look up all that stuff to
             make sure this control flow is valid.  That should never happen
             because our projection only works on non-functions and functions
             are the only non-bottom elements of the lookup stack.  So instead,
             we'll just skip the check here and play defensively; it saves us
             a bind. *)
          if not @@ List.is_empty lookup_stack' then begin
            raise @@ Jhupllib.Utils.Not_yet_implemented
              "Non-singleton lookup stack in Binop rule!"
          end;
          (* Now check to make sure that this control flow exists. *)
          let%bind (_, stack) =
            recurse [env.le_first_var] acl1 relstack
          in
          (* And we're finished. *)
          return (lookup_symbol, stack)
        end;
        (* Start-of-block and end-of-block handling (not actually a rule) *)
        begin
          let%orzero (Start_clause _ | End_clause _) = acl1 in
          recurse lookup_stack acl1 relstack
        end;
      ]
    in
    let%bind m = pick @@ List.enum rule_computations in m
  ;;

  type evaluation = Evaluation of Relative_stack.concrete_stack M.evaluation;;

  let start (cfg : ddpa_graph) (e : expr) (program_point : ident) : evaluation =
    let open M in
    let env = prepare_environment e cfg in
    let initial_lookup_var = env.le_first_var in
    let acl =
      try
        Unannotated_clause(
          lift_clause @@ Ident_map.find program_point env.le_clause_mapping)
      with
      | Not_found ->
        raise @@ Invalid_query(
          Printf.sprintf "Variable %s is not defined" (show_ident program_point))
    in
    let m : Relative_stack.concrete_stack m =
      (* At top level, we don't actually need the returned symbol; we just want
         the concrete stack it produces.  The symbol is only used to generate
         formulae, which we'll get from the completed computations. *)
      let%bind _, stack =
        lookup env [initial_lookup_var] acl Relative_stack.empty
      in
      return stack
    in
    let m_eval = start m in
    Evaluation(m_eval)
  ;;

  let step (x : evaluation) : evaluation_result list * evaluation option =
    let Evaluation(evaluation) = x in
    let results, evaluation' = M.step evaluation in
    let results' =
      results
      |> Enum.filter_map
        (fun evaluation_result ->
           match Solver.solve evaluation_result.M.er_solver with
           | Some f ->
             begin
               lazy_logger `trace (fun () ->
                   Printf.sprintf
                     "Discovered answer of stack %s and formulae:\n%s"
                     (Relative_stack.show_concrete_stack evaluation_result.M.er_value)
                     (Solver.show evaluation_result.M.er_solver)
                 )
             end;
             Some {er_solver = evaluation_result.M.er_solver;
                   er_stack = evaluation_result.M.er_value;
                   er_solution = f
                  }
           | None ->
             begin
               lazy_logger `trace (fun () ->
                   Printf.sprintf
                     "Dismissed answer of stack %s with unsolvable formulae:\n%s"
                     (Relative_stack.show_concrete_stack evaluation_result.M.er_value)
                     (Solver.show evaluation_result.M.er_solver)
                 )
             end;
             None
        )
    in
    (List.of_enum results',
     if M.is_complete evaluation' then None else Some(Evaluation(evaluation'))
    )
  ;;
end;;

type evaluation =
    Evaluation : ('a -> (evaluation_result list * 'a option)) * 'a -> evaluation
;;

module QueueInterpreter =
  Make(Symbolic_monad.QueueWorkCollection(Interpreter_cache_key))
;;

module SmallestRelativeStackLengthInterpreter =
  Make(Symbolic_monad.CacheKeyPriorityQueueWorkCollection
         (Interpreter_cache_key)
         (Interpreter_cache_key_smallest_relative_stack_length_ordering))
;;

module LeastRelativeStackRepetitionInterpreter =
  Make(Symbolic_monad.CacheKeyPriorityQueueWorkCollection
         (Interpreter_cache_key)
         (Interpreter_cache_key_least_relative_stack_repetition_ordering))
;;

let start
    ?exploration_policy:(exploration_policy=Explore_breadth_first)
    (cfg : ddpa_graph) (e : expr) (x : ident) : evaluation =
  match exploration_policy with
  | Explore_breadth_first ->
    let e = QueueInterpreter.start cfg e x in
    Evaluation(QueueInterpreter.step, e)
  | Explore_smallest_relative_stack_length ->
    let e = SmallestRelativeStackLengthInterpreter.start cfg e x in
    Evaluation(SmallestRelativeStackLengthInterpreter.step, e)
  | Explore_least_relative_stack_repetition ->
    let e = LeastRelativeStackRepetitionInterpreter.start cfg e x in
    Evaluation(LeastRelativeStackRepetitionInterpreter.step, e)
;;

let step (x : evaluation) : evaluation_result list * evaluation option =
  let Evaluation(stepper,e) = x in
  let (results, e'opt) = stepper e in
  match e'opt with
  | None -> (results, None)
  | Some e' -> (results, Some(Evaluation(stepper, e')))
;;
