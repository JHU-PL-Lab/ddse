open Batteries;;

open Odefa_ast;;

open Z3;;
open Z3.Arithmetic;;
open Z3.Boolean;;

open Ast;;
open Interpreter_types;;
open Sat_types;;
open Symbol_cache;;

type solution = symbol -> Ast.value option;;

exception Non_solver_type;;

let z3_expr_of_symbol
    (ctx : Z3.context)
    (symbol_cache : symbol_cache)
    (formulae : Formulae.t)
    (symbol : symbol)
  : Expr.expr option =
  let z3symbol = define_symbol symbol_cache symbol in
  match Formulae.type_of symbol formulae with
  | Some IntSymbol -> Some(Integer.mk_const ctx z3symbol)
  | Some BoolSymbol -> Some(Boolean.mk_const ctx z3symbol)
  | Some (FunctionSymbol _) -> None
  | None -> None
;;

let add_formula
    (ctx : Z3.context)
    (solver : Z3.Solver.solver)
    (expr_of_symbol : symbol -> Expr.expr option)
    (formula : Formula.t)
  : unit =
  let translate (symbol : Symbol.t) : Expr.expr =
    match expr_of_symbol symbol with
    | Some expr -> expr
    | None -> raise Non_solver_type
  in
  try
    let Formula(symbol0, expr) = formula in
    let e0 = translate symbol0 in
    match expr with
    | Formula_expression_value v ->
      let e1o =
        match v with
        | Value_function _ ->
          None
        | Value_int n ->
          Some (Integer.mk_numeral_i ctx n)
        | Value_bool b ->
          Some (Boolean.mk_val ctx b)
      in
      begin
        match e1o with
        | None -> ()
        | Some e1 ->
          let c = mk_eq ctx e0 e1 in
          Solver.add solver [c]
      end
    | Formula_expression_alias symbol1 ->
      let e1 = translate symbol1 in
      let c = mk_eq ctx e0 e1 in
      Solver.add solver [c]
    | Formula_expression_binop (symbol1, op, symbol2) ->
      let e1 = translate symbol1 in
      let e2 = translate symbol2 in
      let mk_op =
        let z3_listop_to_binop f =
          fun context arg1 arg2 -> f context [arg1;arg2]
        in
        match op with
        | Binary_operator_plus -> z3_listop_to_binop mk_add ctx
        | Binary_operator_minus -> z3_listop_to_binop mk_sub ctx
        | Binary_operator_times -> z3_listop_to_binop mk_mul ctx
        | Binary_operator_divide -> mk_div ctx
        | Binary_operator_modulus -> Z3.Arithmetic.Integer.mk_mod ctx
        | Binary_operator_less_than -> mk_lt ctx
        | Binary_operator_less_than_or_equal_to -> mk_le ctx
        | Binary_operator_equal_to -> mk_eq ctx
        | Binary_operator_and -> z3_listop_to_binop mk_and ctx
        | Binary_operator_or -> z3_listop_to_binop mk_or ctx
        | Binary_operator_xor -> mk_xor ctx
      in
      let c = mk_eq ctx e0 (mk_op e1 e2) in
      Solver.add solver [c]
  with
  | Non_solver_type ->
    (* Someone's type wasn't found in the type map.  This means either that the
       symbol was unconstrained or the type was something the solver can't
       reason about.  Ignore this case. *)
    ()
;;

let add_formulae
    (ctx : Z3.context)
    (solver : Z3.Solver.solver)
    (symbol_cache : symbol_cache)
    (formulae : Formulae.t)
  : unit =
  let expr_of_symbol = z3_expr_of_symbol ctx symbol_cache formulae in
  formulae
  |> Formulae.iter (add_formula ctx solver expr_of_symbol)
;;

let solve (formulae : Formulae.t) :
  (Interpreter_types.symbol -> value option) option =
  let ctx = Z3.mk_context [] in
  let solver = Solver.mk_solver ctx None in
  let symbol_cache = new_symbol_cache ctx in
  add_formulae ctx solver symbol_cache formulae;
  match Solver.check solver [] with
  | Solver.SATISFIABLE ->
    begin
      match Solver.get_model solver with
      | None ->
        raise @@ Jhupllib.Utils.Invariant_failure
          "Z3 reports no model for a checked formula set"
      | Some model ->
        let get_value symbol =
          match z3_expr_of_symbol ctx symbol_cache formulae symbol with
          | None -> None
          | Some expr ->
            begin
              match Formulae.type_of symbol formulae with
              | Some IntSymbol ->
                begin
                  match Model.eval model expr true with
                  | None -> None
                  | Some expr' ->
                    (* Z3 documents a get_int function, but the latest on OPAM
                       doesn't seem to have it defined. *)
                    let n = Z3.Arithmetic.Integer.get_big_int expr' in
                    Some(Value_int(Big_int.int_of_big_int n))
                end
              | Some BoolSymbol ->
                begin
                  match Model.eval model expr true with
                  | None -> None
                  | Some expr' ->
                    begin
                      match Boolean.get_bool_value expr' with
                      | Z3enums.L_TRUE -> Some(Value_bool true)
                      | Z3enums.L_FALSE -> Some(Value_bool false)
                      | Z3enums.L_UNDEF ->
                        raise @@ Jhupllib.Utils.Not_yet_implemented "L_UNDEF"
                    end
                end
              | Some (FunctionSymbol _) -> None
              | None -> None
            end
        in
        Some get_value
    end
  | Solver.UNSATISFIABLE ->
    (* Return no dictionary. *)
    None
  | Solver.UNKNOWN ->
    failwith @@ Printf.sprintf "Unknown result in solve.check: %s"
      (Solver.get_reason_unknown solver)
;;

let solvable (formulae : Formulae.t) : bool =
  Option.is_some @@ solve formulae
;;
