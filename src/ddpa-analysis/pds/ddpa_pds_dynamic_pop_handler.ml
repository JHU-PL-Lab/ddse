open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast;;
open Ddpa_abstract_ast;;
open Ddpa_context_stack;;
open Ddpa_utils;;
open Nondeterminism;;
open Pds_reachability_types_stack;;

let logger = Logger_utils.make_logger "Ddpa_pds_dynamic_pop_handler";;
let lazy_logger = Logger_utils.make_lazy_logger "Ddpa_pds_dynamic_pop_handler";;

module Make
    (C : Context_stack)
    (S : (module type of Ddpa_pds_structure_types.Make(C)) with module C = C)
    (T : (module type of Ddpa_pds_dynamic_pop_types.Make(C)(S))
     with module C = C
      and module S = S)
=
struct
  open S;;
  open T;;

  module Stack_element = Pds_continuation;;
  module State = Pds_state;;
  module Targeted_dynamic_pop_action = Pds_targeted_dynamic_pop_action;;
  module Untargeted_dynamic_pop_action = Pds_untargeted_dynamic_pop_action;;
  module Stack_action =
    Stack_action_constructor(Stack_element)(Targeted_dynamic_pop_action)
  ;;
  module Terminus =
    Terminus_constructor(State)(Untargeted_dynamic_pop_action)
  ;;
  open Stack_action.T;;
  open Terminus.T;;
  let perform_targeted_dynamic_pop element action =
    Logger_utils.lazy_bracket_log (lazy_logger `trace)
      (fun () ->
         Printf.sprintf "perform_targeted_dynamic_pop (%s) (%s)"
           (Pds_continuation.show element)
           (show_pds_targeted_dynamic_pop_action action))
      (fun results ->
         String_utils.concat_sep_delim "[" "]" ", "
           (
             results
             |> Enum.clone
             |> Enum.map (String_utils.string_of_list Stack_action.show)
           )
      )
    @@ fun () ->
    Nondeterminism_monad.enum @@
    let open Nondeterminism_monad in
    match action with
    | Value_lookup(x,v) ->
      let%orzero Lookup_var x' = element in
      [%guard equal_abstract_var x x'];
      return [Push(Continuation_value v)]
    | Value_drop ->
      let%orzero Continuation_value _ = element in
      return []
    | Value_discovery_2_of_2 ->
      let%orzero Bottom_of_stack = element in
      return []
    | Require_value_1_of_2 ->
      let%orzero Require_value v = element in
      return [Pop_dynamic_targeted(Require_value_2_of_2 v)]
    | Require_value_2_of_2(v) ->
      let%orzero Continuation_value(v') = element in
      [%guard equal_abstract_value v v'];
      return []
    | Variable_aliasing(x2,x1) ->
      let%orzero (Lookup_var(x')) = element in
      [%guard equal_abstract_var x' x2];
      (* We're looking for x2 and we've discovered here that it's aliased to
         x1. *)
      return [Push(Lookup_var(x1))]
    | Nonmatching_clause_skip x'' ->
      let%orzero (Lookup_var(x)) = element in
      [%guard (not @@ equal_abstract_var x x'')];
      (* We can skip the clause.  Put the element back on the stack, though. *)
      return [Push(element)]
    | Value_capture_1_of_3 ->
      let%orzero (Continuation_value abs_filtered_value) = element in
      return [ Pop_dynamic_targeted(
          Value_capture_2_of_3(abs_filtered_value)) ]
    | Value_capture_2_of_3 fv ->
      let%orzero Capture(size) = element in
      return [ Pop_dynamic_targeted(Value_capture_3_of_3(fv,[],size)) ]
    | Value_capture_3_of_3(fv,collected_elements,size) ->
      let n = Bounded_capture_size.to_int size in
      if n > 1
      then
        begin
          let size' = Bounded_capture_size.of_int (n-1) in
          return
            [Pop_dynamic_targeted
               (Value_capture_3_of_3(fv,element::collected_elements,size'))]
        end
      else
        begin
          let pushes =
            List.map (fun x -> Push x) (element::collected_elements)
          in
          return @@ (Push (Continuation_value fv))::pushes
        end
    | Function_call_flow_validation(x2'',x3'',acl0,ctx0,c,ctxc,x) ->
      let%orzero (Lookup_var(x')) = element in
      [%guard (equal_abstract_var x x')];
      return [ Push(element)
             ; Push(Real_flow_huh)
             ; Push(Jump(acl0,ctx0))
             ; Push(Capture(Bounded_capture_size.of_int 2))
             ; Push(Lookup_var(x2''))
             ; Push(Jump(c,ctxc))
             ; Push(Lookup_var(x3''))
             ]
    | Function_call_flow_validation_resolution_1_of_2(x,x') ->
      let%orzero Real_flow_huh = element in
      let action = Function_call_flow_validation_resolution_2_of_2(x,x') in
      return [ Pop_dynamic_targeted(action) ]
    | Function_call_flow_validation_resolution_2_of_2(x,x') ->
      let%orzero Continuation_value(v) = element in
      let%orzero
        Abs_value_function(Abs_function_value(_,Abs_expr(acls))) = v
      in
      [%guard (equal_abstract_var x' @@ rv acls)];
      return [ Pop_dynamic_targeted(Variable_aliasing(x,x')) ]
    | Function_closure_lookup(x'',xf) ->
      let%orzero (Lookup_var(x)) = element in
      [%guard (not @@ equal_abstract_var x x'')];
      (* We're looking for a non-local variable.  Push a lookup for the
         function. *)
      return [ Push(element)
             ; Push(Lookup_var(xf))
             ]
    | Conditional_subject_evaluation(x,x',x1,then_branch,acl1,ctx) ->
      let%orzero (Lookup_var(x0)) = element in
      [%guard (equal_abstract_var x0 x)];
      let capture_size_1 = Bounded_capture_size.of_int 1 in
      return [ Push(Lookup_var(x'))
             ; Push(Jump(acl1,ctx))
             ; Push(Require_value (Abs_value_bool then_branch))
             ; Push(Capture capture_size_1)
             ; Push(Lookup_var(x1))
             ]
    | Record_projection_lookup(x,x',l) ->
      let%orzero (Lookup_var x0) = element in
      [%guard (equal_abstract_var x0 x)];
      return [ Push(Project l)
             ; Push(Lookup_var x')
             ]
    | Record_projection_1_of_2 ->
      let%orzero (Continuation_value v) = element in
      let%orzero (Abs_value_record(r)) = v in
      return [ Pop_dynamic_targeted(Record_projection_2_of_2 r) ]
    | Record_projection_2_of_2(Abs_record_value(m)) ->
      let%orzero (Project lbl) = element in
      [%guard (Ident_map.mem lbl m)];
      return @@ [ Push(Lookup_var(Ident_map.find lbl m)) ]
    | Binary_operator_lookup_init(x1,x2,x3,acl1,ctx1,acl0,ctx0) ->
      let%orzero Lookup_var(x1') = element in
      [%guard (equal_abstract_var x1 x1') ];
      (* The lists below are in reverse order of their presentation in the
         formal rules because we are not directly modifying the stack;
         instead, we are pushing stack elements one at a time. *)
      let capture_size_5 = Bounded_capture_size.of_int 5 in
      let capture_size_2 = Bounded_capture_size.of_int 2 in
      let k1'' = [ Capture capture_size_5
                 ; Lookup_var(x2)
                 ] in
      let k2'' = [ Capture capture_size_2
                 ; Lookup_var(x3)
                 ; Jump(acl1, ctx1) ] in
      let k3'' = [ Binary_operation ; Jump(acl0,ctx0) ] in
      let k0 = [ element ] in
      return @@ List.map (fun x -> Push x) @@ k0 @ k3'' @ k2'' @ k1''
    | Binary_operator_resolution_1_of_4(x1,op) ->
      let%orzero Binary_operation = element in
      return [ Pop_dynamic_targeted(
          Binary_operator_resolution_2_of_4(x1,op)) ]
    | Binary_operator_resolution_2_of_4(x1,op) ->
      (* TODO: Filter out invalid operands.  We did this before, but Zach
         removed it because (a) the logic was messy to embed here and (b) this
         all gets much easier to write once we have the assumption that all
         operators are monomorphic.  So for now, we'll just validate once we
         have the second operand.  This optimization isn't significant anyway.
      *)
      let%orzero Continuation_value(v2) = element in
      return [ Pop_dynamic_targeted(
          Binary_operator_resolution_3_of_4(x1,op,v2)) ]
    | Binary_operator_resolution_3_of_4(x1,op,v2) ->
      let%orzero Continuation_value(v1) = element in
      let%orzero Some result_values = abstract_binary_operation op v1 v2 in
      let%bind result_value = pick_enum result_values in
      return [ Pop_dynamic_targeted(
          Binary_operator_resolution_4_of_4(x1, result_value)) ]
    | Binary_operator_resolution_4_of_4(x1, result_value) ->
      let%orzero Lookup_var(x1') = element in
      [%guard (equal_abstract_var x1 x1') ];
      return [ Push (Continuation_value(result_value)) ]
  ;;

  let perform_untargeted_dynamic_pop element action =
    Nondeterminism_monad.enum @@
    let open Nondeterminism_monad in
    match action with
    | Do_jump ->
      let%orzero (Jump(acl1,ctx)) = element in
      return ([], Static_terminus(Program_point_state(acl1,ctx)))
    | Value_discovery_1_of_2 ->
      let%orzero (Continuation_value v) = element in
      return ( [ Pop_dynamic_targeted(Value_discovery_2_of_2) ]
             , Static_terminus(Result_state v)
             )
  ;;
end;;
