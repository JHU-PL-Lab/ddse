open Batteries;;
(* open Jhupllib;; *)

open Odefa_ast;;
open Odefa_symbolic_interpreter;;

open Ast;;
open Interpreter_types;;

(* open Ode_ast;;
   open Ode_interpreter;;
   open Ode_parser;; *)
(*
let e = Parser.parse_program
    (BatIO.input_string @@
     {program|
         input___0 = input;
         x = input___0;
         bool___1 = true;
         record___2 = {last=bool___1};
         r0 = record___2;
         int___3 = 1;
         bool___4 = lse;
         record___5 = {elem=int___3, last=bool___4, next=r0};
         r1 = record___5;
         int___6 = 2;
         bool___7 = lse;
         record___8 = {elem=int___6, last=bool___7, next=r1};
         r2 = record___8;
         record_proj___9 = r2.next;
         tmp1 = record_proj___9;
         record_proj___10 = tmp1.elem;
         result = record_proj___10;
         binop___11 = result == x;
         nal = binop___11 ? (int___12 = 1; target = int___12; int___13 = 1) :
                                  (int___14 = 2; not_target = int___14; int___15 = 2
                                    );
     |program}
    )
;;

let x,env = Interpreter.eval ~input_source:(n _ -> Ast.Value_int 0) e;;

print_endline @@ Ast_pp.show_var x;;
print_endline @@ "";;
print_endline @@ Interpreter.show_evaluation_environment env;; *)

let empty_stack = Relative_stack.empty;;
let empty_stack_symbol x = Symbol(Ident(x), empty_stack);;
let a = Ident "a";;
let b = Ident "b";;
let c = Ident "c";;
let r = empty_stack_symbol "r";;
let x = empty_stack_symbol "x";;
let y = empty_stack_symbol "y";;
let z = empty_stack_symbol "z";;
let w = empty_stack_symbol "w";;

let alias s1 s2 = Constraint.Constraint_alias(s1, s2);;
let set_int s n = Constraint.Constraint_value(s, Constraint.Int n);;
let set_bool s n = Constraint.Constraint_value(s, Constraint.Bool n);;
let set_rec s m = Constraint.Constraint_value(
    s, Constraint.Record(Ident_map.of_enum @@ List.enum m));;
let set_proj s s' l = Constraint.Constraint_projection(s, s', l);;

let constraints =
  [ set_int x 5;
    set_bool y true;
    set_rec r [(a, x); (b, y)];
    set_proj z r a;
    set_proj w r b;
  ]
;;

constraints
|> List.fold_left
  (fun solver c ->
     print_endline "## solver:";
     print_endline @@ Solver.show solver;
     print_endline "## constraint:";
     print_endline @@ Constraint.show c;
     let solver' = Solver.add c solver in
     print_endline "## solver':";
     print_endline @@ Solver.show solver';
     print_endline "==================";
     solver'
  )
  Solver.empty
;;
