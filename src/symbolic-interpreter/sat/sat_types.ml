(** This module contains data types for the SAT solving process used by
    symbolic interpretation. *)

open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast;;
open Ast_pp;;
open Interpreter_types;;
open Pp_utils;;

(** The type of right-hand sides of formulae generated during symbolic
    interpretation. *)
type formula_expression =
  | Formula_expression_binop of symbol * binary_operator * symbol
  | Formula_expression_alias of symbol
  | Formula_expression_value of value
  | Formula_expression_projection of symbol * ident
[@@deriving eq, ord, to_yojson]
;;

let pp_formula_expression : formula_expression pretty_printer =
  fun formatter e ->
  match e with
  | Formula_expression_binop (x,op,y) ->
    pp_symbol formatter x;
    Format.pp_print_char formatter ' ';
    pp_binary_operator formatter op;
    Format.pp_print_char formatter ' ';
    pp_symbol formatter y;
  | Formula_expression_alias x ->
    pp_symbol formatter x;
  | Formula_expression_value v ->
    pp_value formatter v;
  | Formula_expression_projection(x,lbl) ->
    pp_symbol formatter x;
    Format.pp_print_char formatter '.';
    pp_ident formatter lbl;
;;

let pp_formula_expression_brief : formula_expression pretty_printer =
  fun formatter e ->
  match e with
  | Formula_expression_binop (x,op,y) ->
    pp_symbol formatter x;
    Format.pp_print_char formatter ' ';
    Ast_pp_brief.pp_binary_operator formatter op;
    Format.pp_print_char formatter ' ';
    pp_symbol formatter y;
  | Formula_expression_alias x ->
    pp_symbol formatter x;
  | Formula_expression_value v ->
    Ast_pp_brief.pp_value formatter v;
  | Formula_expression_projection(x,lbl) ->
    pp_symbol formatter x;
    Format.pp_print_char formatter '.';
    pp_ident formatter lbl;
;;

(** The type of formulae which are generated during symbolic interpretation. *)
type formula =
  | Formula of symbol * formula_expression
[@@deriving eq, ord, to_yojson]
;;

let pp_formula : formula pretty_printer =
  fun formatter formula ->
  let Formula(x,e) = formula in
  pp_symbol formatter x;
  Format.pp_print_string formatter " = ";
  pp_formula_expression formatter e;
;;

let pp_brief_formula : formula pretty_printer =
  fun formatter formula ->
  let Formula(x,e) = formula in
  pp_symbol formatter x;
  Format.pp_print_string formatter " = ";
  pp_formula_expression_brief formatter e;
;;
let show_brief_formula = Jhupllib.Pp_utils.pp_to_string pp_brief_formula;;

module Formula_expression = struct
  type t = formula_expression [@@deriving eq, ord, show, to_yojson];;
end;;

module Formula = struct
  type t = formula [@@deriving eq, ord, show, to_yojson];;
  let show_brief = show_brief_formula;;
end;;

module Formula_set = struct
  module S = Set.Make(Formula);;
  include S;;
  include Pp_utils.Set_pp(S)(Formula);;
  include Yojson_utils.Set_to_yojson(S)(Formula);;
  module Pp_brief = Pp_utils.Set_pp(S)(
    struct
      type t = Formula.t;;
      let pp = pp_brief_formula;;
    end);;
end;;

module Formula_map = struct
  module S = Map.Make(Formula);;
  include S;;
  include Pp_utils.Map_pp(S)(Formula);;
  include Yojson_utils.Map_to_yojson(S)(Formula);;
  module Pp_brief = Pp_utils.Map_pp(S)(
    struct
      type t = Formula.t;;
      let pp = pp_brief_formula;;
    end);;
end;;
