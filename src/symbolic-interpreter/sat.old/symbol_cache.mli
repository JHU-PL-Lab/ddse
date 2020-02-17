(**
   This module defines the notion of a "symbol cache".  It is used to create
   and maintain a mapping between Z3 symbols and symbolic variables in the
   interpreter.  Symbol caches are mutable, but operations on them are not
   visibly stateful.
*)

open Interpreter_types;;

type symbol_cache

(**
   Creates a new symbol cache with an embedded Z3 context.
*)
val new_symbol_cache : Z3.context -> symbol_cache;;

(**
   Defines a symbol to Z3 using the cache as appropriate.
*)
val define_symbol : symbol_cache -> Symbol.t -> Z3.Symbol.symbol;;
