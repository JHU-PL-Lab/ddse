open Batteries;;
open Jhupllib;;
open Odefa_ast;;

open Ast;;
open Interpreter_types;;
open Sat_types;;

let lazy_logger = Logger_utils.make_lazy_logger "Formulae";;

(* NOTE: this implementation makes use of mutation, but the interface it
   provides to the rest of the system should be immutable; the mutation here is
   only for performance. *)

type symbol_type =
  | IntSymbol
  | BoolSymbol
  | RecordSymbol
  | FunctionSymbol of function_value
[@@deriving eq]
;;

let pp_symbol_type formatter t =
  match t with
  | IntSymbol -> Format.pp_print_string formatter "int"
  | BoolSymbol -> Format.pp_print_string formatter "bool"
  | RecordSymbol -> Format.pp_print_string formatter "record"
  | FunctionSymbol fv -> Ast_pp_brief.pp_function_value formatter fv
;;

exception SymbolTypeContradiction of string * symbol * symbol_type list;;
exception SymbolValueContradiction of string * symbol * value * value;;

(** Describes the type inference state of a symbol in a collection.  The
    InferredType state indicates that all values assigned to this symbol in any
    solution to the associated formulae will have the specified type.  The
    inferred alias state indicates that the type of this symbol's solution
    values will be the same as another symbol's. *)
type inference_state =
  | InferredType of symbol_type
  | InferredAlias of symbol
[@@deriving show]
;;
let _ = show_inference_state;;

type t =
  { formulae : Formula_set.t;
    value_formulae_map : value Symbol_map.t;
    mutable inference_map : inference_state Symbol_map.t;
  }
;;

let _get_state (symbol : Symbol.t) (collection : t) : inference_state option =
  Symbol_map.Exceptionless.find symbol collection.inference_map
;;

let _set_state
    (symbol : Symbol.t) (state : inference_state) (collection : t)
  : unit =
  collection.inference_map <-
    Symbol_map.add symbol state collection.inference_map
;;

(** Determines the input types and output type of a binary operator. *)
let _infer_binop_signature (binop : binary_operator)
  : symbol_type * symbol_type * symbol_type =
  match binop with
  | Binary_operator_plus -> (IntSymbol, IntSymbol, IntSymbol)
  | Binary_operator_minus -> (IntSymbol, IntSymbol, IntSymbol)
  | Binary_operator_times -> (IntSymbol, IntSymbol, IntSymbol)
  | Binary_operator_divide -> (IntSymbol, IntSymbol, IntSymbol)
  | Binary_operator_modulus -> (IntSymbol, IntSymbol, IntSymbol)
  | Binary_operator_less_than -> (IntSymbol, IntSymbol, BoolSymbol)
  | Binary_operator_less_than_or_equal_to -> (IntSymbol, IntSymbol, BoolSymbol)
  | Binary_operator_equal_to -> (IntSymbol, IntSymbol, BoolSymbol)
  | Binary_operator_and -> (BoolSymbol, BoolSymbol, BoolSymbol)
  | Binary_operator_or -> (BoolSymbol, BoolSymbol, BoolSymbol)
  | Binary_operator_xor -> (BoolSymbol, BoolSymbol, BoolSymbol)
;;

(** Asserts that two types, both given to the same symbol, are equal. *)
let _assert_equal_types
    (symbol : Symbol.t) (t1 : symbol_type) (t2 : symbol_type)
  : unit =
  if equal_symbol_type t1 t2 then () else begin
    raise @@ SymbolTypeContradiction(
      Printf.sprintf "Multiple inferred types for symbol %s"
        (Symbol.show symbol),
      symbol, [t1;t2])
  end
;;

(** Flattens symbols during inference.  This procedure starts at a symbol and
    follows its chain of indirections until reaching either an alias or a
    type.  It then remaps each variable in the chain to the end of that
    chain.  Upon completion, the variable either refers to a concrete type
    (if possible), nothing (if it wasn't in the map to begin with), or an
    alias (but only if the variable to which it is aliased does not exist). *)
let _flatten (symbol : Symbol.t) (collection : t) : unit =
  let rec follow (s : Symbol.t) : inference_state option =
    let my_state = _get_state s collection in
    match my_state with
    | Some (InferredAlias s') ->
      let their_state = follow s' in
      begin
        match their_state with
        | None -> my_state
        | Some state -> _set_state s state collection; Some state
      end
    | None
    | Some (InferredType _) -> my_state
  in
  ignore @@ follow symbol
;;

(** Unifies two symbols during inference.  Either both symbols will have the
    same inference state or one will point directly to the other.  If an error
    occurs (e.g. int = s1 = s2 = bool), a FormulaTypeError is raised. *)
let _unify (symbol1 : Symbol.t) (symbol2 : Symbol.t) (collection : t) : unit =
  _flatten symbol1 collection;
  _flatten symbol2 collection;
  let state1o = _get_state symbol1 collection in
  let state2o = _get_state symbol2 collection in
  match state1o, state2o with
  | None, _ ->
    _set_state symbol1 (InferredAlias symbol2) collection
  | Some _, None ->
    _set_state symbol2 (InferredAlias symbol1) collection
  | Some (InferredType t1), Some (InferredType t2) ->
    (* Make sure both symbols map to the same type. *)
    _assert_equal_types symbol1 t1 t2
  | Some (InferredType _), Some (InferredAlias symbol2') ->
    (* Make symbol2', which can't exist (due to flattening), point to
       symbol1. *)
    _set_state symbol2' (InferredAlias symbol1) collection
  | Some (InferredAlias symbol1'), Some (InferredType _) ->
    (* Make symbol1', which can't exist (due to flattening), point to
       symbol2. *)
    _set_state symbol1' (InferredAlias symbol2) collection
  | Some (InferredAlias symbol1'), Some (InferredAlias symbol2') ->
    (* Due to flattening, neither symbol1' nor symbol2' can exist.  Make one
       point to the other. *)
    _set_state symbol1' (InferredAlias symbol2') collection
;;

(** Constrains a symbol to have a particular type.  If that symbol is already
    in an inference state, this routine unifies those results. *)
let _assign (symbol : Symbol.t) (t : symbol_type) (collection : t) : unit =
  _flatten symbol collection;
  match _get_state symbol collection with
  | None -> _set_state symbol (InferredType t) collection
  | Some (InferredType t') -> _assert_equal_types symbol t t'
  | Some (InferredAlias symbol') ->
    _set_state symbol' (InferredType t) collection;
    _set_state symbol (InferredType t) collection;
;;

(* ************ Interface Functions ************ *)

let empty : t =
  { formulae = Formula_set.empty;
    value_formulae_map = Symbol_map.empty;
    inference_map = Symbol_map.empty;
  }
;;

let add (formula : formula) (collection : t) : t =
  if Formula_set.mem formula collection.formulae then collection else
    begin
      lazy_logger `trace (fun () ->
          Printf.sprintf "Adding %s to %s"
            (Formula.show_brief formula)
            (Formula_set.Pp_brief.show collection.formulae)
        );
      (* Derive a set containing the new formula. *)
      let formulae' = Formula_set.add formula collection.formulae in
      (* Derive a map containing new value formulae if necessary. *)
      let value_formulae_map' =
        match formula with
        | Formula(symbol,Formula_expression_value(v)) ->
          begin
            match Symbol_map.Exceptionless.find
                    symbol collection.value_formulae_map with
            | None ->
              Symbol_map.add symbol v collection.value_formulae_map
            | Some v' ->
              if equal_value v v' then
                collection.value_formulae_map
              else
                raise @@ SymbolValueContradiction
                  (Printf.sprintf
                     "Immediately contradictory value assignments: %s = %s and %s = %s"
                     (show_symbol symbol) (Ast_pp.show_value v)
                     (show_symbol symbol) (Ast_pp.show_value v'),
                   symbol, v, v')
          end
        | _ -> collection.value_formulae_map
      in
      let collection' =
        { collection with
          formulae = formulae';
          value_formulae_map = value_formulae_map';
        }
      in
      (* Infer type information. *)
      let Formula(symbol, expr) = formula in
      begin
        match expr with
        | Formula_expression_value v ->
          let typ =
            match v with
            | Value_record _ -> RecordSymbol
            | Value_function f -> FunctionSymbol f
            | Value_int _ -> IntSymbol
            | Value_bool _ -> BoolSymbol
          in
          _assign symbol typ collection';
        | Formula_expression_alias symbol' ->
          _unify symbol symbol' collection'
        | Formula_expression_binop (symbol1, op, symbol2) ->
          let (tin1,tin2,tout) = _infer_binop_signature op in
          _assign symbol1 tin1 collection';
          _assign symbol2 tin2 collection';
          _assign symbol tout collection';
        | Formula_expression_projection (symbol', _label) ->
          (* We know that the thing being projected from must be a record, but
             we don't know anything else. *)
          _assign symbol' RecordSymbol collection';
      end;
      collection'
    end
;;

let singleton (formula : formula) : t =
  add formula empty
;;

let union (collection1 : t) (collection2 : t) : t =
  let (smaller, larger) =
    if Formula_set.cardinal collection1.formulae <
       Formula_set.cardinal collection2.formulae then
      (collection1, collection2)
    else
      (collection2, collection1)
  in
  smaller.formulae
  |> Formula_set.enum
  |> Enum.fold
    (fun acc formula -> add formula acc)
    larger
;;

let enum (collection : t) : formula Enum.t =
  Formula_set.enum collection.formulae
;;

let of_enum (enum : formula Enum.t) : t =
  enum
  |> Enum.fold
    (fun a e -> add e a)
    empty
;;

let iter (fn : formula -> unit) (collection : t) : unit =
  Enum.iter fn @@ enum collection
;;

let type_of (symbol : symbol) (collection : t) : symbol_type option =
  _flatten symbol collection;
  match _get_state symbol collection with
  | None -> raise Not_found
  | Some(InferredType t) -> Some t
  | Some(InferredAlias _) -> None
;;

let pp formatter collection =
  Formula_set.pp formatter collection.formulae
;;

let show = Jhupllib.Pp_utils.pp_to_string pp;;

let pp_brief formatter collection =
  Formula_set.Pp_brief.pp formatter collection.formulae
;;

let show_brief = Jhupllib.Pp_utils.pp_to_string pp_brief;;
