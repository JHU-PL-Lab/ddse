open Odefa_ast;;

open Ast;;
open Ast_pp;;
open Ddpa_abstract_ast;;
open Ddpa_context_stack;;

module Make
    (C : Context_stack)
    (S : (module type of Ddpa_pds_structure_types.Make(C)) with module C = C) =
struct
  module C = C;;
  module S = S;;
  open S;;
  type pds_targeted_dynamic_pop_action =
    | Value_lookup of abstract_var * abstract_value
    (** An action which represents the discovery of an immediate value
        assignment to a variable. *)
    | Value_drop
    (** An action to drop values from the top of the stack.  This is necessary
        for actions such as non-local lookup which perform a subordinate
        lookup but do not act upon the resulting value. *)
    | Value_discovery_2_of_2
    (** The second step of value discovery, which confirms that the special
        "bottom" stack element is next on the stack.  This step pops that
        element so that the targeted value state can be accepted (by empty
        stack).  Note that the first step of value discovery is untargeted. *)
    | Require_value_1_of_2
    (** The action that requires particular values on the stack.  It expects to
        see the declaration of requirement on top of the stack. *)
    | Require_value_2_of_2 of abstract_value
    (** The second step of value requirement, which confirms that the desired
        value is on the stack.  The value provided here is the one which is
        required. *)
    | Variable_aliasing of abstract_var * abstract_var
    (** Represents variable aliasing, as in "x = y".  The first variable
        is the one being declared; the second variable is the one being
        used.  This pop action is used for every rule which performs basic
        x-to-y aliasing regardless of whether the clause in question is
        annotated. *)
    | Nonmatching_clause_skip of abstract_var
    (** Represents skipping a non-matching clause.  The variable here is the
        variable defined by the clause; if the top element of the stack is not
        a lookup for this variable, the clause can be safely skipped. *)
    | Value_capture_1_of_3
    (** Represents the first step of the value capture action.  This step
        pops and stores the value being captured. *)
    | Value_capture_2_of_3 of abstract_value
    (** Represents the second step of the value capture action.  This step
        extracts the number of other stack elements to gather up before
        capturing the value. *)
    | Value_capture_3_of_3 of
        abstract_value * Pds_continuation.t list * Bounded_capture_size.t
    (** Represents the third step of the value capture action.  This action
        collects other stack elements into a list until it has consumed as
        many as the original Capture stack element dictated.  It then pushes
        a value to the stack followed by all of the elements it collected. *)
    | Function_call_flow_validation of
        abstract_var * abstract_var * annotated_clause * C.t *
        annotated_clause * C.t * abstract_var
    (** Represents the validation of a function at a call site to ensure that
        we only explore exit nodes which apply in this context.  The first
        variable is the called function. The second variable is the argument
        passed to the function.  The given states are used to build the targets
        to which to jump once the function argument has been validated and
        once a function value has been discovered.  The third variable is the
        call site for which this validation is occurring. *)
    | Function_call_flow_validation_resolution_1_of_2 of
        abstract_var * abstract_var
    (** The first step of resolving function call flow validation.  The first
        variable is the call site; the second variable is the return variable
        for the called function's wiring node. *)
    | Function_call_flow_validation_resolution_2_of_2 of
        abstract_var * abstract_var
    (** We've captured the "RealFlow?" and now expect to see a value. *)
    | Function_closure_lookup of
        abstract_var * abstract_var
    (** Represents a function closure lookup.  The first variable is the
        parameter of the function; the second variable is the function itself.
        If the lookup variable does not match the parameter, then this lookup
        is for a non-local and we must search for the function's definition
        first. *)
    | Conditional_subject_evaluation of
        abstract_var * abstract_var * abstract_var * bool *
        annotated_clause * C.t
    (** Represents the handling of an exit wiring node for a conditional.  The
        first variable is the conditional site; the second variable is the
        return variable of the conditional branch.  The third variable is the
        subject of the conditional.  The boolean indicates whether this is the
        "then" branch (true) or the "else" branch (false).  The state and
        context refer to this wiring clause so a jump can be issued after the
        subject is checked in this branch. *)
    | Record_projection_lookup of abstract_var * abstract_var * ident
    (** Represents the start of a record projection.  If the first variable
        matches our lookup target, then we've discovered that we are looking
        up the projection of the ident label from a record stored in the
        second variable. *)
    | Record_projection_1_of_2
    (** Represents the processing of a record projection on the stack.  This
        action requires two steps: one to grab the record and one to grab the
        value. *)
    | Record_projection_2_of_2 of abstract_record_value
    (** The second step of handling record projection. *)
    | Binary_operator_lookup_init of
        abstract_var * abstract_var * abstract_var *
        annotated_clause * C.t * annotated_clause * C.t
    (** Represents the kickstart of a process which looks up values for a
        binary operation.  The first variable above must be the
        current target of lookup.  The next two variables are the operands
        of the operation.  The remaining two pairs of values represent the
        source and target states of the DDPA edge. *)
    | Binary_operator_resolution_1_of_4 of abstract_var * binary_operator
    (** Represents the start of the resolution of a binary operator after its
        operands have been found.  The variable is the one defined by the
        operation; the operands are on the stack.  This action simply pops the
        Binary_operation header from the stack. *)
    | Binary_operator_resolution_2_of_4 of abstract_var * binary_operator
    (** The second step of binary operator resolution.  This step collects the
        SECOND operand if it is a valid operand for the given kind of
        operation.  (The operands are produced in opposite order on the
        stack.) *)
    | Binary_operator_resolution_3_of_4 of
        abstract_var * binary_operator * abstract_value
    (** The third step of binary operator resolution.  The variable is the one
        assigned by the operation; the value is the operation's second operand.
        This step collects the FIRST operand and transforms the operands into
        a result value.*)
    | Binary_operator_resolution_4_of_4 of
        abstract_var * abstract_value
    (** The forth step of binary operator resolution.  This step
        collects and checks the lookup variable. The `abstract_value' is
        the result of the operation. A check guarantees that the given result
        is valid for the given operation. *)
  [@@deriving eq, ord, show, to_yojson]
  ;;

  module Pds_targeted_dynamic_pop_action =
  struct
    type t = pds_targeted_dynamic_pop_action
    let equal = equal_pds_targeted_dynamic_pop_action
    let compare = compare_pds_targeted_dynamic_pop_action
    let pp = pp_pds_targeted_dynamic_pop_action
    let show = show_pds_targeted_dynamic_pop_action
    let to_yojson = pds_targeted_dynamic_pop_action_to_yojson
  end;;

  type pds_untargeted_dynamic_pop_action =
    | Do_jump
    (** The action for performing basic jump operations. *)
    | Value_discovery_1_of_2
    (** Represents the rule that, if a value is the only element on the stack,
        we transition to one of the result states.  To determine that the
        value is the only element, we must be able to pop the special "bottom"
        stack element, so this is the first step of the process (which pops
        the value).  Because the value dictates the target of the second
        step, this is an untargeted action.  The second step is targeted. *)
  [@@deriving eq, ord, show, to_yojson]
  ;;

  module Pds_untargeted_dynamic_pop_action =
  struct
    type t = pds_untargeted_dynamic_pop_action
    let equal = equal_pds_untargeted_dynamic_pop_action
    let compare = compare_pds_untargeted_dynamic_pop_action
    let pp = pp_pds_untargeted_dynamic_pop_action
    let show = show_pds_untargeted_dynamic_pop_action
    let to_yojson = pds_untargeted_dynamic_pop_action_to_yojson
  end;;
end;;
