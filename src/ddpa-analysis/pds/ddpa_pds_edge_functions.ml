open Batteries;;
open Jhupllib;;

open Ddpa_abstract_ast;;
open Ddpa_context_stack;;
open Ddpa_graph;;
open Ddpa_utils;;

let logger = Logger_utils.make_logger "Ddpa_pds_edge_functions";;
let lazy_logger = Logger_utils.make_lazy_logger "Ddpa_pds_edge_functions";;

module Make
    (C : Context_stack)
    (S : (module type of Ddpa_pds_structure_types.Make(C)) with module C = C)
    (T : (module type of Ddpa_pds_dynamic_pop_types.Make(C)(S))
     with module C = C
      and module S = S)
    (B : Pds_reachability_basis.Basis)
    (R : Pds_reachability_analysis.Analysis
     with type State.t = S.Pds_state.t
      and type Targeted_dynamic_pop_action.t = T.pds_targeted_dynamic_pop_action)
=
struct
  open S;;
  open T;;
  open R.Stack_action.T;;
  open R.Terminus.T;;

  (**
     Creates a PDS edge function for a particular DDPA graph edge.  The
     resulting function produces transitions for PDS states, essentially serving
     as the first step toward implementing each DDPA rule.  The remaining steps
     are addressed by the dynamic pop handler, which performs the closure of the
     dynamic pops generated by this function.
  *)
  let create_edge_function
      (edge : ddpa_edge) (state : R.State.t)
    : (R.Stack_action.t list * R.Terminus.t) Enum.t =
    (* Unpack the edge *)
    let Ddpa_edge(acl1, acl0) = edge in
    (* Generate PDS edge functions for this DDPA edge *)
    Logger_utils.lazy_bracket_log (lazy_logger `trace)
      (fun () -> Printf.sprintf "DDPA %s edge function at state %s"
          (show_ddpa_edge edge) (Pds_state.show state))
      (fun edges ->
         let string_of_output (actions,target) =
           String_utils.string_of_tuple
             (String_utils.string_of_list R.Stack_action.show)
             R.Terminus.show
             (actions,target)
         in
         Printf.sprintf "Generates edges: %s"
           (String_utils.string_of_list string_of_output @@
            List.of_enum @@ Enum.clone edges)) @@
    fun () ->
    let zero = Enum.empty in
    let%orzero Program_point_state(acl0',ctx) = state in
    (* TODO: There should be a way to associate each edge function with
             its corresponding acl0 rather than using this guard. *)
    [%guard (compare_annotated_clause acl0 acl0' == 0) ];
    let open Option.Monad in
    let zero () = None in
    (* TODO: It'd be nice if we had a terser way to represent stack
             processing operations (those that simply reorder the stack
             without transitioning to a different node). *)
    let targeted_dynamic_pops = Enum.filter_map identity @@ List.enum
        [
          (* ********** Value Discovery ********** *)
          (* Variable Lookup Discovers Value *)
          begin
            let%orzero
              (Unannotated_clause(Abs_clause(x,Abs_value_body v))) = acl1
            in
            (* x = v *)
            return (Value_lookup(x, v), Program_point_state(acl1, ctx))
          end
          ;
          (* Variable Lookup Discovers Input *)
          begin
            let%orzero
              (Unannotated_clause(Abs_clause(x,Abs_input_body))) = acl1
            in
            (* x = input *)
            return (Value_lookup(x, Abs_value_int),
                    Program_point_state(acl1, ctx))
          end
          ;
          (* Intermediate Value *)
          begin
            return (Value_drop, Program_point_state(acl0,ctx))
          end
          ;
          (* ********** Value Processing ********** *)
          (* Value Requirement *)
          begin
            return (Require_value_1_of_2, Program_point_state(acl0,ctx))
          end
          ;
          (* ********** Variable Search ********** *)
          (* Value Alias *)
          begin
            let%orzero
              (Unannotated_clause(Abs_clause(x, Abs_var_body x'))) = acl1
            in
            (* x = x' *)
            return (Variable_aliasing(x,x'),Program_point_state(acl1,ctx))
          end
          ;
          (* Stateless Clause Skip *)
          begin
            let%orzero (Unannotated_clause(Abs_clause(x,_))) = acl1 in
            (* x' = b *)
            return ( Nonmatching_clause_skip x
                   , Program_point_state(acl1,ctx)
                   )
          end
          ;
          (* Block Marker Skip *)
          (* This is handled below as a special case because it does not involve
             a pop. *)
          (* ********** Navigation ********** *)
          (* Capture *)
          begin
            return ( Value_capture_1_of_3
                   , Program_point_state(acl0, ctx)
                   )
          end
          ;
          (* ********** Function Wiring ********** *)
          (* Function Top: Parameter Variable *)
          begin
            let%orzero (Binding_enter_clause(x,x',c)) = acl1 in
            let%orzero (Abs_clause(_,Abs_appl_body (_,x3''))) = c in
            begin
              if not (equal_abstract_var x' x3'') then
                raise @@ Utils.Invariant_failure "Ill-formed wiring node."
              else
                ()
            end;
            (* x =(down)c x' *)
            [%guard C.is_top c ctx];
            let ctx' = C.pop ctx in
            return (Variable_aliasing(x,x'),Program_point_state(acl1,ctx'))
          end
          ;
          (* Function Bottom: Flow Check *)
          begin
            let%orzero (Binding_exit_clause(x,_,c)) = acl1 in
            let%orzero (Abs_clause(x1'',Abs_appl_body(x2'',x3''))) = c in
            begin
              if not (equal_abstract_var x x1'') then
                raise @@ Utils.Invariant_failure "Ill-formed wiring node."
              else
                ()
            end;
            (* x =(up)c _ (for functions) *)
            return (
              Function_call_flow_validation(x2'',x3'',acl0,ctx,
                                            Unannotated_clause(c),ctx,x),
              Program_point_state(Unannotated_clause(c),ctx)
            )
          end
          ;
          (* Function Bottom: Return Variable *)
          begin
            let%orzero (Binding_exit_clause(x,x',c)) = acl1 in
            let%orzero (Abs_clause(x1'',Abs_appl_body _)) = c in
            begin
              if not (equal_abstract_var x x1'') then
                raise @@ Utils.Invariant_failure "Ill-formed wiring node."
              else
                ()
            end;
            (* x =(up)c x' *)
            let ctx' = C.push c ctx in
            return ( Function_call_flow_validation_resolution_1_of_2(x,x')
                   , Program_point_state(acl1,ctx')
                   )
          end
          ;
          (* Function Top: Non-Local Variable *)
          begin
            let%orzero (Binding_enter_clause(x'',x',c)) = acl1 in
            let%orzero (Abs_clause(_,Abs_appl_body(x2'',x3''))) = c in
            begin
              if not (equal_abstract_var x' x3'') then
                raise @@ Utils.Invariant_failure "Ill-formed wiring node."
              else
                ()
            end;
            (* x'' =(down)c x' *)
            [%guard C.is_top c ctx];
            let ctx' = C.pop ctx in
            return ( Function_closure_lookup(x'',x2'')
                   , Program_point_state(acl1,ctx')
                   )
          end
          ;
          (* ********** Conditional Wiring ********** *)
          (* Conditional Top *)
          (* This is handled below as a special case because it does not involve
             a pop. *)
          (* Conditional Bottom: Return Positive
             Conditional Bottom: Return Negative *)
          begin
            let%orzero (Binding_exit_clause(x,x',c)) = acl1 in
            let%orzero
              (Abs_clause(x2,Abs_conditional_body(x1,e1,_))) = c
            in
            begin
              if not (equal_abstract_var x x2) then
                raise @@ Utils.Invariant_failure "Ill-formed wiring node."
              else
                ()
            end;
            (* x =(up) x' for conditionals *)
            let Abs_expr(cls) = e1 in
            let e1ret = rv cls in
            let then_branch = equal_abstract_var e1ret x' in
            return
              ( Conditional_subject_evaluation(x,x',x1,then_branch,acl1,ctx),
                Program_point_state(Unannotated_clause(c),ctx)
              )
          end
          ;
          (* ********** Operations ********** *)
          (* Binary Operation Start *)
          begin
            let%orzero
              (Unannotated_clause(Abs_clause(x1,
                                             Abs_binary_operation_body(x2,_,x3)))) = acl1
            in
            (* x1 = x2 op x3 *)
            return ( Binary_operator_lookup_init(
                x1,x2,x3,acl1,ctx,acl0,ctx)
                   , Program_point_state(acl1,ctx)
              )
          end
          ;
          (* Binary Operation Evaluation *)
          begin
            let%orzero
              (Unannotated_clause(Abs_clause(x1,
                                             Abs_binary_operation_body(_,op,_)))) = acl1
            in
            (* x1 = x2 op x3 *)
            return ( Binary_operator_resolution_1_of_4(x1,op)
                   , Program_point_state(acl1,ctx)
                   )
          end
          ;
        ]
    in
    let nop_states =
      match acl1 with
      | Start_clause _ | End_clause _ | Nonbinding_enter_clause _ ->
        Enum.singleton @@ Program_point_state(acl1,ctx)
      | _ -> Enum.empty ()
    in
    Enum.append
      (targeted_dynamic_pops
       |> Enum.map
         (fun (action,state) ->
            ([Pop_dynamic_targeted(action)], Static_terminus state)))
      (nop_states
       |> Enum.map
         (fun state -> ([], Static_terminus state)))
  ;;

  let create_untargeted_dynamic_pop_action_function
      (_ : ddpa_edge) (_ : R.State.t) =
    List.enum [ Value_discovery_1_of_2; Do_jump ]
  ;;

end;;
