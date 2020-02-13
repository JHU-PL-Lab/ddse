open Odefa_ast;;

open Ast;;
open Batteries;;
open Jhupllib;;

module Int_map = Map.Make(struct type t = int let compare = compare end);;

type source_statistics =
  { ss_num_program_points : int;
    ss_num_function_definitions : int;
    ss_num_function_calls : int;
    ss_num_variable_references : int;
    ss_num_non_local_variable_references : int;
    ss_num_non_local_variable_references_by_depth : int Int_map.t;
    ss_max_lexical_depth : int;
  }
;;

let empty =
  { ss_num_program_points = 0;
    ss_num_function_definitions = 0;
    ss_num_function_calls = 0;
    ss_num_variable_references = 0;
    ss_num_non_local_variable_references = 0;
    ss_num_non_local_variable_references_by_depth = Int_map.empty;
    ss_max_lexical_depth = 0;
  }
;;

type depth_bindings = int Ident_map.t;;

let pp_depth_bindings =
  Jhupllib_pp_utils.pp_map pp_ident Format.pp_print_int Ident_map.enum
;;
let _ = pp_depth_bindings;;

let db_add (Var(i,_) : var) (db : depth_bindings) : depth_bindings =
  Ident_map.add i 0 db
;;

let db_deeper (db : depth_bindings) : depth_bindings =
  Ident_map.map (fun x -> x + 1) db
;;

let ss_higher (ss : source_statistics) : source_statistics =
  { ss with ss_max_lexical_depth = ss.ss_max_lexical_depth + 1 }
;;

let ss_join (ss1 : source_statistics) (ss2 : source_statistics)
  : source_statistics =
  { ss_num_program_points =
      ss1.ss_num_program_points + ss2.ss_num_program_points;
    ss_num_function_definitions =
      ss1.ss_num_function_definitions + ss2.ss_num_function_definitions;
    ss_num_function_calls =
      ss1.ss_num_function_calls + ss2.ss_num_function_calls;
    ss_num_variable_references =
      ss1.ss_num_variable_references + ss2.ss_num_variable_references;
    ss_num_non_local_variable_references =
      ss1.ss_num_non_local_variable_references +
      ss2.ss_num_non_local_variable_references;
    ss_num_non_local_variable_references_by_depth =
      Int_map.merge
        (fun _ ao bo ->
           match ao, bo with
           | Some a, Some b -> Some (a + b)
           | Some a, None -> Some a
           | None, Some b -> Some b
           | None, None -> None
        )
        ss1.ss_num_non_local_variable_references_by_depth
        ss2.ss_num_non_local_variable_references_by_depth;
    ss_max_lexical_depth =
      max ss1.ss_max_lexical_depth ss2.ss_max_lexical_depth;
  }
;;

let ss_var_ref
    (Var(i,_) : var)
    (db : depth_bindings)
    (ss : source_statistics)
  : source_statistics =
  let depth = Ident_map.find i db in
  { ss with
    ss_num_variable_references = ss.ss_num_variable_references + 1;
    ss_num_non_local_variable_references =
      ss.ss_num_non_local_variable_references + (if depth = 0 then 0 else 1);
    ss_num_non_local_variable_references_by_depth =
      let m = ss.ss_num_non_local_variable_references_by_depth in
      if depth = 0 then m else
        Int_map.add depth (Int_map.find_default 0 depth m + 1) m;
  }
;;

let ss_vars_ref (xs : var list) (db : depth_bindings) (ss : source_statistics)
  : source_statistics =
  List.fold_left (fun ss' x -> ss_var_ref x db ss') ss xs
;;

let rec calc_expr (Expr cs : expr) (db : depth_bindings) : source_statistics =
  (* Note: we're just binding *every* variable in the expression simultaneously.
     This is akin to variable lifting in languages such as Python.  Odefa does
     not have precisely those semantics, but the well-formedness check is
     responsible for discarding those cases where forward references are
     invalid. *)
  let db' =
    List.fold_left
      (fun dbacc (Clause(x,_)) ->
         db_add x dbacc
      )
      db cs
  in
  calc_clauses cs db'

and calc_clauses (cs : clause list) (db : depth_bindings) =
  match cs with
  | [] -> raise @@ Utils.Invariant_failure("Empty clause list!")
  | c :: [] ->
    calc_clause c db
  | c :: cs' ->
    let ss = calc_clause c db in
    ss_join ss @@ calc_clauses cs' db

and calc_clause (Clause(_,b) : clause) (db : depth_bindings)
  : source_statistics =
  let ss = calc_clause_body b db in
  { ss with
    ss_num_program_points = ss.ss_num_program_points + 1 }

and calc_clause_body (b : clause_body) (db : depth_bindings)
  : source_statistics =
  match b with
  | Value_body v -> calc_value v db
  | Var_body x -> ss_var_ref x db empty
  | Input_body -> empty
  | Appl_body (x1, x2) ->
    let ss = ss_vars_ref [x1;x2] db empty in
    { ss with
      ss_num_function_calls = ss.ss_num_function_calls + 1
    }
  | Conditional_body (x, e1, e2) ->
    ss_var_ref x db @@
    ss_join (calc_expr e1 db) (calc_expr e2 db)
  | Match_body(x, _) ->
    ss_var_ref x db empty
  | Projection_body(x, _) ->
    ss_var_ref x db empty
  | Binary_operation_body (x1, _, x2) ->
    ss_vars_ref [x1; x2] db empty

and calc_value (v : value) (db : depth_bindings) : source_statistics =
  match v with
  | Value_record(Record_value m) ->
    { empty with
      ss_num_variable_references = Ident_map.cardinal m
    }
  | Value_function f ->
    let ss = calc_function_value f db in
    { ss with
      ss_num_function_definitions = ss.ss_num_function_definitions + 1
    }
  | Value_int _
  | Value_bool _ ->
    empty

and calc_function_value (f : function_value) (db : depth_bindings)
  : source_statistics =
  let Function_value(x, e) = f in
  let db' = db_add x @@ db_deeper db in
  ss_higher @@ calc_expr e db'
;;

let calculate_statistics (e : expr) : source_statistics =
  calc_expr e Ident_map.empty
;;
