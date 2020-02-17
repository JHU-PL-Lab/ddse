open Batteries;;
open Odefa_ast;;

open Ast;;
open Interpreter_types;;

type symbol_cache = Z3.context * Z3.Symbol.symbol Symbol_map.t ref;;

let new_symbol_cache ctx = (ctx, ref Symbol_map.empty);;

let symbol_suffix_of_relative_stack
    (Relative_stack.Relative_stack(costk,stk)) : string =
  let costk_name =
    String.join "$" @@ List.map (fun (Ident(s)) -> s) costk
  in
  let stk_name =
    String.join "$" @@ List.map (fun (Ident(s)) -> s) stk
  in
  Printf.sprintf "$$%s$$%s" costk_name stk_name
;;

let name_of_symbol (s : symbol) =
  match s with
  | SpecialSymbol SSymTrue -> "$$$true"
  | Symbol(Ident name, relstack) ->
    name ^ symbol_suffix_of_relative_stack relstack
;;

let define_symbol
    (symbol_cache : symbol_cache)
    (symbol : Symbol.t)
  : Z3.Symbol.symbol =
  let (ctx,r) = symbol_cache in
  match Symbol_map.Exceptionless.find symbol !r with
  | None ->
    let z3sym = Z3.Symbol.mk_string ctx @@ name_of_symbol symbol in
    r := Symbol_map.add symbol z3sym !r;
    z3sym
  | Some z3sym -> z3sym
;;
