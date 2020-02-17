(**
   This module defines a routine which performs satisfiability checks on a
   collection of formulae.  This module does not check complex structures such
   as functions and relies upon the Formulae module to detect immediate
   inconsistencies (such as when functions are declared equal to integers).  It
   will, however, discover cases in which e.g. integer variables are constrained
   to have no solutions.
*)

open Odefa_ast;;

open Interpreter_types;;

(**
   The type of a solution to a set of formulae.
*)
type solution = (symbol -> Ast.value option);;

(**
   Given a collection of formulae, determines whether or not a solution exists.
*)
val solvable : Formulae.t -> bool

(**
   Given a collection of formulae, determines a solution for them.  If no
   solution can be found, None is returned.  Otherwise, the returned function
   maps symbols to their concrete values in the solution.  If a symbol is not
   assigned in the solution, the returned function produces None.
*)
val solve : Formulae.t -> solution option
