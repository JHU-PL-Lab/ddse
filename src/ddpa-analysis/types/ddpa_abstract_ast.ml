open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast;;
open Ast_pp;;
open Pp_utils;;

(** A type to express abstract variables. *)
type abstract_var =
  | Abs_var of ident
[@@deriving eq, ord, to_yojson, show]
;;

(** A type to expression abstract record values. *)
type abstract_record_value =
  | Abs_record_value of abstract_var Ident_map.t
[@@deriving eq, ord, to_yojson]
;;

(** A type to expression abstract reference values. *)
type abstract_ref_value =
  | Abs_ref_value of abstract_var
[@@deriving eq, ord, to_yojson]
;;

(** A type to express abstract values. *)
type abstract_value =
  | Abs_value_record of abstract_record_value
  | Abs_value_function of abstract_function_value
  | Abs_value_int
  | Abs_value_bool of bool
[@@deriving eq, ord, to_yojson]

and abstract_function_value =
  | Abs_function_value of abstract_var * abstract_expr
[@@deriving eq, ord, to_yojson]

(** A type to represent the bodies of abstract clauses. *)
and abstract_clause_body =
  | Abs_value_body of abstract_value
  | Abs_var_body of abstract_var
  | Abs_input_body
  | Abs_appl_body of abstract_var * abstract_var
  | Abs_conditional_body of abstract_var * abstract_expr * abstract_expr
  | Abs_match_body of abstract_var * pattern
  | Abs_projection_body of abstract_var * ident
  | Abs_binary_operation_body of abstract_var * binary_operator * abstract_var
[@@deriving eq, ord, to_yojson]

(** A type to represent abstract clauses. *)
and abstract_clause =
  | Abs_clause of abstract_var * abstract_clause_body
[@@deriving eq, ord, to_yojson]

(** A type to represent abstract expressions. *)
and abstract_expr =
  | Abs_expr of abstract_clause list
[@@deriving eq, ord, to_yojson]
;;

let pp_abstract_var formatter (Abs_var(i)) = pp_ident formatter i;;

let rec pp_abstract_function_value formatter (Abs_function_value(x,e)) =
  Format.fprintf formatter "%a -> (@ %a)"
    pp_abstract_var x pp_abstract_expr e

and pp_abstract_value formatter v =
  match v with
  | Abs_value_record r -> pp_abstract_record_value formatter r
  | Abs_value_function f -> pp_abstract_function_value formatter f
  | Abs_value_int -> Format.pp_print_string formatter "int"
  | Abs_value_bool b ->
    Format.pp_print_string formatter @@ if b then "true" else "false"

and pp_abstract_record_value formatter (Abs_record_value els) =
  let pp_element formatter (k,v) =
    Format.fprintf formatter "%a=%a" pp_ident k pp_abstract_var v
  in
  pp_concat_sep_delim "{" "}" "," pp_element formatter @@ Ident_map.enum els

and pp_abstract_ref_value formatter (Abs_ref_value x) =
  Format.fprintf formatter "ref %a" pp_abstract_var x

and pp_abstract_clause_body formatter b =
  match b with
  | Abs_var_body(x) -> pp_abstract_var formatter x
  | Abs_value_body(v) -> pp_abstract_value formatter v
  | Abs_input_body -> Format.pp_print_string formatter "input"
  | Abs_appl_body(x1,x2) ->
    Format.fprintf formatter "%a %a" pp_abstract_var x1 pp_abstract_var x2
  | Abs_conditional_body(x,e1,e2) ->
    Format.fprintf formatter
      "%a @[<4>? @[<2>(%a)@] : @[<2>(%a)@]@]"
      pp_abstract_var x
      pp_abstract_expr e1
      pp_abstract_expr e2
  | Abs_match_body(x,p) ->
    Format.fprintf formatter "%a ~ %a" pp_abstract_var x pp_pattern p
  | Abs_projection_body(x,l) ->
    Format.fprintf formatter "%a.%a" pp_abstract_var x pp_ident l
  | Abs_binary_operation_body(x1,op,x2) ->
    Format.fprintf formatter "%a %a %a"
      pp_abstract_var x1 pp_binary_operator op pp_abstract_var x2

and pp_abstract_clause formatter (Abs_clause(x,b)) =
  Format.fprintf formatter "%a = @[<hv 2>%a@]"
    pp_abstract_var x pp_abstract_clause_body b

and pp_abstract_expr formatter (Abs_expr(cls)) =
  pp_concat_sep ";" pp_abstract_clause formatter @@ List.enum cls
;;

let rec pp_brief_abstract_function_value formatter (Abs_function_value(x,_)) =
  Format.fprintf formatter "%a -> ..." pp_abstract_var x

and pp_brief_abstract_value formatter v =
  match v with
  | Abs_value_record r -> pp_brief_abstract_record_value formatter r
  | Abs_value_function f -> pp_brief_abstract_function_value formatter f
  | Abs_value_int -> Format.pp_print_string formatter "int"
  | Abs_value_bool b ->
    Format.pp_print_string formatter @@ if b then "true" else "false"

and pp_brief_abstract_record_value formatter (Abs_record_value els) =
  let pp_brief_element formatter (k,v) =
    Format.fprintf formatter "%a=%a" pp_ident k pp_abstract_var v
  in
  pp_concat_sep_delim "{" "}" "," pp_brief_element formatter @@ Ident_map.enum els

and pp_brief_abstract_ref_value formatter (Abs_ref_value x) =
  Format.fprintf formatter "ref %a" pp_abstract_var x

and pp_brief_abstract_clause_body formatter b =
  match b with
  | Abs_var_body(x) -> pp_abstract_var formatter x
  | Abs_value_body(v) -> pp_brief_abstract_value formatter v
  | Abs_input_body -> Format.pp_print_string formatter "input"
  | Abs_appl_body(x1,x2) ->
    Format.fprintf formatter "%a %a" pp_abstract_var x1 pp_abstract_var x2
  | Abs_conditional_body(x,_,_) ->
    Format.fprintf formatter
      "%a @[<4>? ...@]"
      pp_abstract_var x
  | Abs_match_body(x,_) ->
    Format.fprintf formatter "%a ~ ..." pp_abstract_var x
  | Abs_projection_body(x,l) ->
    Format.fprintf formatter "%a.%a" pp_abstract_var x pp_ident l
  | Abs_binary_operation_body(x1,op,x2) ->
    Format.fprintf formatter "%a %a %a"
      pp_abstract_var x1 pp_binary_operator op pp_abstract_var x2

and pp_brief_abstract_clause formatter (Abs_clause(x,b)) =
  Format.fprintf formatter "%a = @[<hv 2>%a@]"
    pp_abstract_var x pp_brief_abstract_clause_body b

and pp_brief_abstract_expr formatter (Abs_expr(cls)) =
  pp_concat_sep ";" pp_brief_abstract_clause formatter @@ List.enum cls
;;

let show_abstract_clause = pp_to_string pp_abstract_clause;;

let var_of_abstract_clause (Abs_clause(x,_)) = x;;
let pp_var_of_abstract_clause formatter acl =
  pp_abstract_var formatter (var_of_abstract_clause acl)
;;

let is_abstract_clause_immediate (Abs_clause(_,b)) =
  match b with
  | Abs_var_body _
  | Abs_value_body _
  | Abs_input_body
  | Abs_match_body _
  | Abs_projection_body _
  | Abs_binary_operation_body _ -> true
  | Abs_appl_body _
  | Abs_conditional_body _ -> false
;;

module Abs_value =
struct
  type t = abstract_value
  let equal = equal_abstract_value
  let compare = compare_abstract_value
  let pp = pp_abstract_value
  let to_yojson = abstract_value_to_yojson
end;;

module Abs_value_set =
struct
  module Impl = Set.Make(Abs_value);;
  include Impl;;
  include Pp_utils.Set_pp(Impl)(Abs_value);;
  include Yojson_utils.Set_to_yojson(Impl)(Abs_value);;
end;;

let pp_abs_value_set formatter s =
  pp_concat_sep_delim "{" "}" ", " pp_abstract_value formatter @@
  Abs_value_set.enum s
;;

module Abs_clause =
struct
  type t = abstract_clause
  let compare = compare_abstract_clause
  let pp = pp_abstract_clause
  let to_yojson = abstract_clause_to_yojson
end;;

module Abs_clause_set =
struct
  module Impl = Set.Make(Abs_clause);;
  include Impl;;
  include Pp_utils.Set_pp(Impl)(Abs_clause);;
  include Yojson_utils.Set_to_yojson(Impl)(Abs_clause);;
end;;

type annotated_clause =
  | Unannotated_clause of abstract_clause
  | Binding_enter_clause of abstract_var * abstract_var * abstract_clause
  | Binding_exit_clause of abstract_var * abstract_var * abstract_clause
  | Nonbinding_enter_clause of abstract_value * abstract_clause
  | Start_clause of abstract_var
  (** This variable is the return variable of the block that this clause
      starts. *)
  | End_clause of abstract_var
  (** This variable is the return variable of the block that this clause
      ends. *)
[@@deriving ord, eq, to_yojson]
;;

let pp_annotated_clause formatter annotated_clause =
  match annotated_clause with
  | Unannotated_clause acl -> pp_abstract_clause formatter acl
  | Binding_enter_clause(x,x',c) ->
    pp_abstract_var formatter x;
    Format.pp_print_string formatter " = ";
    pp_abstract_var formatter x';
    Format.pp_print_string formatter " @+ ";
    pp_abstract_clause formatter c;
  | Binding_exit_clause(x,x',c) ->
    pp_abstract_var formatter x;
    Format.pp_print_string formatter " = ";
    pp_abstract_var formatter x';
    Format.pp_print_string formatter " @- ";
    pp_abstract_clause formatter c;
  | Nonbinding_enter_clause(v,c) ->
    pp_abstract_value formatter v;
    Format.pp_print_string formatter " @+ ";
    pp_abstract_clause formatter c;
  | Start_clause(x) ->
    Format.pp_print_string formatter "start ";
    pp_abstract_var formatter x;
  | End_clause(x) ->
    Format.pp_print_string formatter "end ";
    pp_abstract_var formatter x;
;;
let show_annotated_clause = Jhupllib.Pp_utils.pp_to_string pp_annotated_clause;;

let pp_brief_annotated_clause formatter annotated_clause =
  match annotated_clause with
  | Unannotated_clause acl -> pp_brief_abstract_clause formatter acl
  | Binding_enter_clause(x,x',Abs_clause(x'',_)) ->
    pp_abstract_var formatter x;
    Format.pp_print_string formatter " = ";
    pp_abstract_var formatter x';
    Format.pp_print_string formatter " @+ ";
    pp_abstract_var formatter x'';
  | Binding_exit_clause(x,x',Abs_clause(x'',_)) ->
    pp_abstract_var formatter x;
    Format.pp_print_string formatter " = ";
    pp_abstract_var formatter x';
    Format.pp_print_string formatter " @- ";
    pp_abstract_var formatter x'';
  | Nonbinding_enter_clause(v,Abs_clause(x'',_)) ->
    pp_abstract_value formatter v;
    Format.pp_print_string formatter " @+ ";
    pp_abstract_var formatter x'';
  | Start_clause(x) ->
    Format.pp_print_string formatter "start ";
    pp_abstract_var formatter x;
  | End_clause(x) ->
    Format.pp_print_string formatter "end ";
    pp_abstract_var formatter x;
;;
let show_brief_annotated_clause =
  Jhupllib.Pp_utils.pp_to_string pp_brief_annotated_clause
;;

let is_annotated_clause_immediate acl =
  match acl with
  | Unannotated_clause(cl) -> is_abstract_clause_immediate cl
  | Binding_enter_clause _
  | Binding_exit_clause _
  | Nonbinding_enter_clause _
  | Start_clause _
  | End_clause _ -> true
;;

module Annotated_clause =
struct
  type t = annotated_clause
  let compare = compare_annotated_clause
  let pp = pp_annotated_clause
  let to_yojson = annotated_clause_to_yojson
end;;

module Annotated_clause_set =
struct
  module Impl = Set.Make(Annotated_clause);;
  include Impl;;
  include Pp_utils.Set_pp(Impl)(Annotated_clause);;
  include Yojson_utils.Set_to_yojson(Impl)(Annotated_clause);;
end;;

module Annotated_clause_map =
struct
  module Impl = Map.Make(Annotated_clause);;
  include Impl;;
  include Pp_utils.Map_pp(Impl)(Annotated_clause);;
  include Yojson_utils.Map_to_yojson(Impl)(Annotated_clause);;
end;;

let pp_annotated_clause_set =
  Pp_utils.pp_set pp_annotated_clause Annotated_clause_set.enum
;;
