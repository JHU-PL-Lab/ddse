(**
   This module provides a mechanism for command-line parsing of test generator
   configurations.
*)

open Odefa_ast;;
open Odefa_test_generation;;

open Ast;;

type generator_args = {
  ga_generator_configuration : Generator_configuration.configuration;
  ga_filename : string;
  ga_target_point : Ident.t;
  ga_maximum_steps : int option;
  ga_maximum_results : int option;
  ga_exploration_policy :
    Odefa_symbolic_interpreter.Interpreter.exploration_policy;
  ga_compact_output : bool;
};;

(** Parses the command line arguments.  If a parse error occurs, this function
    prints an appropriate error message and terminates the program.  Otherwise,
    the returned values are the generator configuration, the name of the file
    to analyze, and the variable in the program to reach. *)
val parse_args : unit -> generator_args;;
