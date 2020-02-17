open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast_tools;;
open Preliminary_conversion;;
open Translator_utils;;

(** In this module we will translate from odefa-natural to odefa in the
    following order:

    * Desugar Let Rec
    * Desugar lists
    * Desugar variants
    * Desugar pattern vars
    * Desugar pattern matching
    * Ensure that program has unique var names
*)

open TranslationMonad;;

let lazy_logger = Logger_utils.make_lazy_logger "On_to_odefa";;

let nonempty_body ((body : Ast.clause list), (var : Ast.var))
  : (Ast.clause list * Ast.var) m =
  match body with
  | [] ->
    let%bind x = fresh_var "var" in
    return @@ ([Ast.Clause(x, Var_body var)], x)
  | _ ->
    return (body, var)
;;

let flatten_fun (param_names : On_ast.Ident.t list) (body : Ast.expr)
  : (Ast.expr * Ast.var) m =
  list_fold_right_m
    (fun (param : On_ast.Ident.t) ((expr : Ast.expr), (_ : Ast.Var.t)) ->
       let On_ast.Ident(param_name : string) = param in
       let odefa_ident : Ast.Ident.t = Ast.Ident(param_name) in
       let%bind (new_var : Ast.var) = fresh_var "flatten_fun" in
       let new_clause : Ast.clause =
         Ast.Clause(new_var,
                    Ast.Value_body(Ast.Value_function(
                        Ast.Function_value(Ast.Var(odefa_ident, None), expr)
                      )))
       in
       let expr' : Ast.expr = Ast.Expr([new_clause]) in
       return (expr', new_var)
    )
    param_names
    (body, retv body)
;;

let ident_map_map_m (fn : 'a -> 'b m) (m : 'a On_ast.Ident_map.t)
  : 'b On_ast.Ident_map.t m =
  m
  |> On_ast.Ident_map.enum
  |> Enum.map (fun (k,v) -> let%bind v' = fn v in return (k,v'))
  |> List.of_enum
  |> sequence
  |> lift1 List.enum
  |> lift1 On_ast.Ident_map.of_enum
;;

let rec rec_transform (e1 : On_ast.expr) : On_ast.expr m =
  match e1 with
  | Var _ | Int _ | Bool _ | Input ->
    return e1
  | Function (id_list, fe) ->
    let%bind transformed_expr = rec_transform fe in
    return @@ On_ast.Function (id_list, transformed_expr)
  | Appl (apple1, apple2) ->
    let%bind transformed_expr1 = rec_transform apple1 in
    let%bind transformed_expr2 = rec_transform apple2 in
    return @@ On_ast.Appl (transformed_expr1, transformed_expr2)
  | Let (let_id, lete1, lete2) ->
    let%bind transformed_expr1 = rec_transform lete1 in
    let%bind transformed_expr2 = rec_transform lete2 in
    return @@ On_ast.Let (let_id, transformed_expr1, transformed_expr2)
  | LetFun (funsig, fe) ->
    let (Funsig (id, id_list, bodye')) = funsig in
    let%bind transform_bodye = rec_transform bodye' in
    let%bind transformed_fe = rec_transform fe in
    let new_sig = On_ast.Funsig (id, id_list, transform_bodye) in
    return @@ On_ast.LetFun(new_sig, transformed_fe)
  | LetRecFun (fun_sig_list, rece) ->
    let%bind transformed_rece = rec_transform rece in
    let original_names =
      List.map (fun single_sig ->
          let (On_ast.Funsig (id, _, _)) = single_sig
          in id) fun_sig_list
    in
    let%bind new_names =
      sequence @@ List.map
        (fun (On_ast.Ident old_name) ->
           let%bind new_name = fresh_name old_name in
           return @@ On_ast.Ident new_name
        )
        original_names
    in
    let name_pairs = List.combine original_names new_names in
    let appls_for_funs = List.fold_left (fun appl_dict -> fun base_fun ->
        let (original_fun_name, new_fun_name) = base_fun in
        let sub_appl =
          List.fold_left
            (fun acc -> fun fun_name -> On_ast.Appl(acc, Var(fun_name)))
            (Var(new_fun_name)) new_names in
        On_ast.Ident_map.add original_fun_name sub_appl appl_dict) On_ast.Ident_map.empty name_pairs
    in
    let let_maker_fun = (fun fun_name -> fun acc ->
        let cur_appl_expr = On_ast.Ident_map.find fun_name appls_for_funs in
        On_ast.Let(fun_name, cur_appl_expr, acc))
    in
    let transformed_outer_expr =
      List.fold_right let_maker_fun original_names transformed_rece
    in
    let sig_name_pairs = List.combine fun_sig_list new_names in
    let%bind ret_expr =
      list_fold_right_m (fun (fun_sig, fun_new_name) -> fun acc ->
          let (On_ast.Funsig (_, param_list, cur_f_expr)) = fun_sig in
          let%bind transformed_cur_f_expr = rec_transform cur_f_expr in
          let new_param_list = new_names @ param_list in
          let new_fun_expr = List.fold_right let_maker_fun original_names transformed_cur_f_expr in
          return @@ On_ast.Let(fun_new_name, Function (new_param_list, new_fun_expr), acc)
        ) sig_name_pairs transformed_outer_expr
    in
    return ret_expr
  | Not e ->
    let%bind transformed_expr = rec_transform e in
    return @@ On_ast.Not(transformed_expr)
  | Plus (pe1, pe2) ->
    let%bind transformed_expr1 = rec_transform pe1 in
    let%bind transformed_expr2 = rec_transform pe2 in
    return @@ On_ast.Plus (transformed_expr1, transformed_expr2)
  | Minus (me1, me2) ->
    let%bind transformed_expr1 = rec_transform me1 in
    let%bind transformed_expr2 = rec_transform me2 in
    return @@ On_ast.Minus (transformed_expr1, transformed_expr2)
  | Times (me1, me2) ->
    let%bind transformed_expr1 = rec_transform me1 in
    let%bind transformed_expr2 = rec_transform me2 in
    return @@ On_ast.Times (transformed_expr1, transformed_expr2)
  | Divide (me1, me2) ->
    let%bind transformed_expr1 = rec_transform me1 in
    let%bind transformed_expr2 = rec_transform me2 in
    return @@ On_ast.Divide (transformed_expr1, transformed_expr2)
  | Modulus (me1, me2) ->
    let%bind transformed_expr1 = rec_transform me1 in
    let%bind transformed_expr2 = rec_transform me2 in
    return @@ On_ast.Modulus (transformed_expr1, transformed_expr2)
  | Equal (eqe1, eqe2) ->
    let%bind transformed_expr1 = rec_transform eqe1 in
    let%bind transformed_expr2 = rec_transform eqe2 in
    return @@ On_ast.Equal (transformed_expr1, transformed_expr2)
  | LessThan (lte1, lte2) ->
    let%bind transformed_expr1 = rec_transform lte1 in
    let%bind transformed_expr2 = rec_transform lte2 in
    return @@ On_ast.LessThan (transformed_expr1, transformed_expr2)
  | Leq (leqe1, leqe2) ->
    let%bind transformed_expr1 = rec_transform leqe1 in
    let%bind transformed_expr2 = rec_transform leqe2 in
    return @@ On_ast.Leq (transformed_expr1, transformed_expr2)
  | And (ande1, ande2) ->
    let%bind transformed_expr1 = rec_transform ande1 in
    let%bind transformed_expr2 = rec_transform ande2 in
    return @@ On_ast.And (transformed_expr1, transformed_expr2)
  | Or (ore1, ore2) ->
    let%bind transformed_expr1 = rec_transform ore1 in
    let%bind transformed_expr2 = rec_transform ore2 in
    return @@ On_ast.Or (transformed_expr1, transformed_expr2)
  | If (ife, thene, elsee) ->
    let%bind transformed_expr1 = rec_transform ife in
    let%bind transformed_expr2 = rec_transform thene in
    let%bind transformed_expr3 = rec_transform elsee in
    return @@ On_ast.If (transformed_expr1, transformed_expr2, transformed_expr3)
  (* TODO RECORD *)
  | Record _ -> return e1
  | RecordProj (e, lab) ->
    let%bind transformed_expr = rec_transform e in
    return @@ On_ast.RecordProj (transformed_expr, lab)
;;

(* Function that removes duplicate naming so that we adhere to Odefa's naming
   rules. Is called when we detect a duplicate naming.
   NOTE: We should stop when we encounter a LET statement
   (or frankly a function) that rewrites the var???
*)
let rec replace_duplicate_naming
    (e : On_ast.expr)
    (old_name : On_ast.ident)
    (new_name : On_ast.ident)
  : On_ast.expr =
  match e with
  | Int _ | Bool _ | Input -> e
  | Var (id) ->
    if id = old_name then Var(new_name) else Var(id)
  | Function (id_list, e') ->
    if (List.mem old_name id_list) then e
    else
      let new_e' = replace_duplicate_naming e' old_name new_name in
      Function(id_list, new_e')
  | Appl (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Appl(new_e1, new_e2)
  | Let (id, e1, e2) ->
    if id = old_name then e
    else
      let new_e1 = replace_duplicate_naming e1 old_name new_name in
      let new_e2 = replace_duplicate_naming e2 old_name new_name in
      Let(id, new_e1, new_e2)
  | LetRecFun (_, _) ->
    raise @@ Utils.Invariant_failure
      "rec functions should have been encoded!"
  | LetFun (f_sig, e') ->
    let (On_ast.Funsig(id, id_list, fun_e)) = f_sig in
    (* If the old_name is same as the function name, then we don't want
       to change anything. *)
    if id = old_name then e
    else
      (
        (* If the old_name is same as one of the names of the params, then
           we only want to change the code outside of the function.
        *)
        if List.mem old_name id_list then
          (
            let new_e' = replace_duplicate_naming e' old_name new_name in
            LetFun (f_sig, new_e')
          )
        else (* change both the inside and the outside expressions *)
          (
            let new_inner_e = replace_duplicate_naming fun_e old_name new_name in
            let new_outer_e = replace_duplicate_naming e' old_name new_name in
            let new_funsig = On_ast.Funsig(id, id_list, new_inner_e) in
            LetFun(new_funsig, new_outer_e)
          )
      )
  | Plus (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Plus (new_e1, new_e2)
  | Minus (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Minus (new_e1, new_e2)
  | Times (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Times (new_e1, new_e2)
  | Divide (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Divide (new_e1, new_e2)
  | Modulus (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Modulus (new_e1, new_e2)
  | Equal (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Equal (new_e1, new_e2)
  | LessThan (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    LessThan (new_e1, new_e2)
  | Leq (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Leq (new_e1, new_e2)
  | And (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    And (new_e1, new_e2)
  | Or (e1, e2) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    Or (new_e1, new_e2)
  | Not (e') ->
    let new_e' = replace_duplicate_naming e' old_name new_name in
    Not (new_e')
  | If (e1, e2, e3) ->
    let new_e1 = replace_duplicate_naming e1 old_name new_name in
    let new_e2 = replace_duplicate_naming e2 old_name new_name in
    let new_e3 = replace_duplicate_naming e3 old_name new_name in
    If (new_e1, new_e2, new_e3)
  | Record fields ->
    Record (On_ast.Ident_map.map (fun e -> replace_duplicate_naming e old_name new_name) fields)
  | RecordProj (e, lab) -> RecordProj (replace_duplicate_naming e old_name new_name, lab)
;;

(* A function that finds all of the duplicate naming that happens for a given
   expression, and then calls replace_duplicate_naming to change the latter
   naming.
*)
let find_replace_duplicate_naming (e : On_ast.expr) : On_ast.expr m =
  let find_replace_on_fun_params_folder
      (curr_id : On_ast.Ident.t)
      (acc : (On_ast.expr * On_ast.Ident.t list * On_ast.Ident.t list))
    : (On_ast.expr * On_ast.Ident.t list * On_ast.Ident.t list) m =
    let (curr_e, curr_id_list, fun_id_list) = acc in
    if List.mem curr_id curr_id_list then
      (
        let On_ast.Ident(name_string) = curr_id in
        let%bind name_string' = fresh_name name_string in
        let new_name = On_ast.Ident(name_string') in
        let new_e = replace_duplicate_naming curr_e curr_id new_name in
        let new_list = new_name :: curr_id_list in
        let new_fun_list = new_name :: fun_id_list in
        return (new_e, new_list, new_fun_list)
      )
    else
      (
        let new_list = curr_id :: curr_id_list in
        let new_fun_list = curr_id :: fun_id_list in
        return (curr_e, new_list, new_fun_list)
      )
  in
  let rec recurse
      (e : On_ast.expr)
      (ident_list : On_ast.ident list)
    : (On_ast.expr * On_ast.ident list) m =
    Logger_utils.lazy_bracket_log
      (lazy_logger `trace)
      (fun () -> "enter")
      (fun _ -> "exit")
    @@ fun () ->
    match e with
    | Int _ | Bool _ | Var _ | Input -> return (e , ident_list)
    | Function (id_list, e') ->
      (* we assume that the id_list of this function consists of unique elements *)
      (* TODO: clean up the naming of id_list *)
      let%bind (init_e, init_id_list) = recurse e' ident_list in
      let%bind (final_e, final_id_list, final_fun_id_list) =
        list_fold_right_m find_replace_on_fun_params_folder
          id_list (init_e, init_id_list, [])
      in
      return (On_ast.Function (final_fun_id_list, final_e), final_id_list)
    | Appl (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Appl(new_e1, new_e2), e2_id_list)
    | Let (id, e1, e2) ->
      let%bind (init_e2, init_e2_id_list) = recurse e2 ident_list in
      let%bind (init_e1, init_e1_id_list) = recurse e1 init_e2_id_list in
      if List.mem id init_e1_id_list then
        (
          let On_ast.Ident(name_string) = id in
          let%bind name_string' = fresh_name name_string in
          let new_name = On_ast.Ident(name_string') in
          (* let new_e1 = replace_duplicate_naming init_e1 id new_name in *)
          let new_e2 = replace_duplicate_naming init_e2 id new_name in
          let new_list = new_name :: init_e1_id_list in
          return (On_ast.Let(new_name, init_e1, new_e2), new_list)
        )
      else
        (
          let new_list = id :: init_e1_id_list in
          return (On_ast.Let(id, init_e1, init_e2), new_list)
        )
    | LetRecFun _ ->
      raise @@ Utils.Invariant_failure "let rec should have been encoded!"
    | LetFun (f_sig, e') ->
      let Funsig(f_name, param_list, f_e) = f_sig in
      let%bind (outer_e, outer_e_list) = recurse e' ident_list in
      let%bind (init_inner_e, init_list) = recurse f_e outer_e_list in
      (* taking care of the funsig part*)
      let%bind (final_inner_e, ident_list', param_list') =
        list_fold_right_m find_replace_on_fun_params_folder
          param_list (init_inner_e, init_list, [])
      in
      (* checking if the let part has conflicts *)
      if List.mem f_name ident_list' then
        (
          (* if there are conflicts, we need to change the id in the let binding,
             and accomodate on the outer expression
          *)
          let On_ast.Ident(name_string) = f_name in
          let%bind name_string' = fresh_name name_string in
          let new_name = On_ast.Ident(name_string') in
          let new_outer_e = replace_duplicate_naming outer_e f_name new_name in
          let new_list = new_name :: ident_list' in
          let new_funsig = On_ast.Funsig(new_name, param_list', final_inner_e) in
          return (On_ast.LetFun(new_funsig, new_outer_e), new_list)
        )
      else
        (
          let new_list = f_name :: ident_list' in
          let new_funsig = On_ast.Funsig(f_name, param_list', final_inner_e) in
          return (On_ast.LetFun(new_funsig, outer_e), new_list)
        )
    | Plus (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Plus(new_e1, new_e2), e2_id_list)
    | Minus (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Minus(new_e1, new_e2), e2_id_list)
    | Times (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Times(new_e1, new_e2), e2_id_list)
    | Divide (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Divide(new_e1, new_e2), e2_id_list)
    | Modulus (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Modulus(new_e1, new_e2), e2_id_list)
    | Equal (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Equal(new_e1, new_e2), e2_id_list)
    | LessThan (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.LessThan(new_e1, new_e2), e2_id_list)
    | Leq (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Leq(new_e1, new_e2), e2_id_list)
    | And (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.And(new_e1, new_e2), e2_id_list)
    | Or (e1, e2) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      return (On_ast.Or(new_e1, new_e2), e2_id_list)
    | Not (e') ->
      let%bind (new_e', e1_id_list) = recurse e' ident_list in
      return (On_ast.Not(new_e'), e1_id_list)
    | If (e1, e2, e3) ->
      let%bind (new_e1, e1_id_list) = recurse e1 ident_list in
      let%bind (new_e2, e2_id_list) = recurse e2 e1_id_list in
      let%bind (new_e3, e3_id_list) = recurse e3 e2_id_list in
      return (On_ast.If(new_e1, new_e2, new_e3), e3_id_list)
    | Record m ->
      let mappings = List.of_enum @@ On_ast.Ident_map.enum m in
      let rec loop mappings map id_list =
        match mappings with
        | [] -> return (map, id_list)
        | h::t ->
          let (lbl,expr) = h in
          let%bind (new_expr,new_id_list) = recurse expr id_list in
          let map' = On_ast.Ident_map.add lbl new_expr map in
          loop t map' new_id_list
      in
      let%bind (m,id_list) = loop mappings On_ast.Ident_map.empty ident_list in
      return (On_ast.Record(m), id_list)
    | RecordProj (e', lbl) ->
      let%bind (new_e', e'_id_list) = recurse e' ident_list in
      return (On_ast.RecordProj(new_e', lbl), e'_id_list)
  in
  let%bind x = recurse e [] in
  return @@ fst x
;;


let rec flatten_binop
    (e1 : On_ast.expr)
    (e2 : On_ast.expr)
    (binop : Ast.binary_operator)
  : (Ast.clause list * Ast.var) m =
  let%bind (e1_clist, e1_var) = flatten_expr e1 in
  let%bind (e2_clist, e2_var) = flatten_expr e2 in
  let%bind new_var = fresh_var "binop" in
  let new_clause =
    Ast.Clause (
      new_var,
      Ast.Binary_operation_body (e1_var, binop, e2_var)
    )
  in
  return (e1_clist @ e2_clist @ [new_clause], new_var)

and

  flatten_expr (e : On_ast.expr) : (Ast.clause list * Ast.var) m =
  match e with
  | Var (id) ->
    let Ident(i_string) = id in
    let return_var = Ast.Var(Ast.Ident(i_string), None) in
    return ([], return_var)
  | Input ->
    let%bind new_var = fresh_var "input" in
    return ([Ast.Clause(new_var, Ast.Input_body)], new_var)
  | Function (id_list, e) ->
    let%bind (fun_c_list, _) = nonempty_body @@@ flatten_expr e in
    let body_expr = Ast.Expr(fun_c_list) in
    let%bind (Expr(fun_clause), return_var) = flatten_fun id_list body_expr in
    return (fun_clause, return_var)
  | Appl (e1, e2) ->
    let%bind (e1_clist, e1_var) = flatten_expr e1 in
    let%bind (e2_clist, e2_var) = flatten_expr e2 in
    let%bind new_var = fresh_var "appl" in
    let new_clause =
      Ast.Clause (
        new_var,
        Ast.Appl_body (e1_var, e2_var)
      )
    in
    return (e1_clist @ e2_clist @ [new_clause], new_var)
  | Let (var_ident, e1, e2) ->
    let%bind (e1_clist, e1_var) = flatten_expr e1 in
    let%bind (e2_clist, e2_var) = flatten_expr e2 in
    let Ident(var_name) = var_ident in
    let letvar = Ast.Var(Ast.Ident(var_name), None) in
    let assignment_clause = Ast.Clause(letvar, Ast.Var_body(e1_var)) in
    return (e1_clist @ [assignment_clause] @ e2_clist, e2_var)
  | LetFun (sign, e) ->
    (* TODO: check for bugs!!! *)
    (* Translating the function signature... *)
    let Funsig(fun_name, id_list, fun_e) = sign in
    let%bind (body_clist, _) = nonempty_body @@@ flatten_expr fun_e in
    let%bind (Expr(fun_clauses), return_var) =
      flatten_fun id_list (Expr(body_clist))
    in
    (* Flattening the "e2"... *)
    let%bind (e_clist, e_var) = flatten_expr e in
    (* Assigning the function to the given function name... *)
    let On_ast.Ident(var_name) = fun_name in
    let letvar = Ast.Var(Ast.Ident(var_name), None) in
    let assignment_clause = Ast.Clause(letvar, Ast.Var_body(return_var)) in
    return (fun_clauses @ [assignment_clause] @ e_clist, e_var)
  | LetRecFun (_, _) ->
    (* | LetRecFun (sig_list, e) ->  *)
    raise @@ Utils.Invariant_failure "LetRecFun passed to flatten_expr"
  | Plus (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_plus
  | Minus (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_minus
  | Times (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_times
  | Divide (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_divide
  | Modulus (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_modulus
  | Equal (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_equal_to
  | LessThan (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_less_than
  | Leq (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_less_than_or_equal_to
  | And (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_and
  | Or (e1, e2) ->
    flatten_binop e1 e2 Ast.Binary_operator_or
  | Not (e) ->
    flatten_binop e (Bool true) Ast.Binary_operator_xor
  | If (e1, e2, e3) ->
    let%bind (e1_clist, e1_var) = flatten_expr e1 in
    let%bind (e2_clist, _) = nonempty_body @@@ flatten_expr e2 in
    let e2_expr = Ast.Expr(e2_clist) in
    let%bind (e3_clist, _) = nonempty_body @@@ flatten_expr e3 in
    let e3_expr = Ast.Expr(e3_clist) in
    let%bind new_clausevar = fresh_var "if" in
    let conditional_clause =
      Ast.Clause(new_clausevar,
                 Ast.Conditional_body(e1_var, e2_expr, e3_expr))
    in
    return (e1_clist @ [conditional_clause], new_clausevar)
  | Int (n) ->
    let%bind int_var = fresh_var "int" in
    let new_clause = Ast.Clause(int_var, Ast.Value_body(Ast.Value_int(n))) in
    return ([new_clause], int_var)
  | Bool (b) ->
    let%bind bool_var = fresh_var "bool" in
    let new_clause = Ast.Clause(bool_var, Ast.Value_body(Ast.Value_bool(b))) in
    return ([new_clause], bool_var)
  | Record (recexpr_map) ->
    (* function for Enum.fold that generates the clause list and the
       id -> var map for Odefa's record *)
    let flatten_and_map acc ident_expr_tuple :
      (Ast.clause list * Ast.var Ast.Ident_map.t) m =
      let (clist, recmap) = acc in
      let (id, e) = ident_expr_tuple in
      let On_ast.Ident(id_string) = id in
      let ast_id = Ast.Ident(id_string) in
      let%bind (e_clist, e_var) = flatten_expr e in
      let new_clist = clist @ e_clist in
      let new_map = Ast.Ident_map.add ast_id e_var recmap in
      return (new_clist, new_map)
    in
    let empty_acc = ([], Ast.Ident_map.empty) in
    let%bind (clist, map) =
      On_ast.Ident_map.enum recexpr_map
      |> List.of_enum
      |> list_fold_left_m flatten_and_map empty_acc
    in
    let%bind rec_var = fresh_var "record" in
    let new_clause = Ast.Clause(rec_var,
                                Ast.Value_body(Ast.Value_record(
                                    Ast.Record_value (map)
                                  ))) in
    return (clist @ [new_clause], rec_var)
  | RecordProj (e, lab) ->
    let%bind (e_clist, e_var) = flatten_expr e in
    let On_ast.Label(l_string) = lab in
    let l_ident = Ast.Ident(l_string) in
    let%bind new_var = fresh_var "record_proj" in
    let new_clause = Ast.Clause(new_var,
                                Ast.Projection_body(e_var, l_ident)
                               ) in
    return (e_clist @ [new_clause], new_var)
;;

let translate
    ?translation_context:(translation_context=None)
    (e : On_ast.expr)
  : Odefa_ast.Ast.expr =
  let e_m =
    let%bind transformed_e =
      return e
      >>= rec_transform
      >>= return % list_transform
      >>= find_replace_duplicate_naming
    in
    let%bind (c_list, _) = flatten_expr transformed_e in
    let Clause(last_var, _) = List.last c_list in
    let res_var = Ast.Var(Ident("~result"), None) in
    let res_clause = Ast.Clause(res_var, Ast.Var_body(last_var)) in
    return @@ Ast.Expr(c_list @ [res_clause])
  in
  let context =
    match translation_context with
    | None -> new_translation_context "~"
    | Some ctx -> ctx
  in
  run context e_m
;;
