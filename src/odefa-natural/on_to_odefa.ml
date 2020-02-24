open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast_tools;;
open Preliminary_conversion;;
(* open Simplification;; *)
open Translator_utils;;

(** In this module we will translate from odefa-natural to odefa in the
    following order:

    * Alphatize program
    * Annotate recursive call sites
    * Desugar let rec
    * Desugar lists
    * Desugar variants
    * Desugar pattern vars
    * Desugar pattern matching
    * Alphatize program again (to allow above transformations to introduce
      dupes)
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

let flatten_fun
    ?binding_name:(binding_name=(None:On_ast.Ident.t option))
    (param_names : On_ast.Ident.t list)
    (body : Ast.expr)
  : (Ast.expr * Ast.var) m =
  list_fold_right_m
    (fun (param : On_ast.Ident.t) ((expr : Ast.expr), (_ : Ast.Var.t)) ->
       let On_ast.Ident(param_name : string) = param in
       let odefa_ident : Ast.Ident.t = Ast.Ident(param_name) in
       let%bind (new_var : Ast.var) =
         match binding_name with
         | None -> fresh_var "flatten_fun"
         | Some(Ident(s)) -> fresh_var s
       in
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

(** Determines all variables contained within a pattern. *)
let rec pat_vars (pat : On_ast.pattern) : On_ast.Ident_set.t =
  match pat with
  | On_ast.AnyPat -> On_ast.Ident_set.empty
  | On_ast.IntPat -> On_ast.Ident_set.empty
  | On_ast.TruePat -> On_ast.Ident_set.empty
  | On_ast.FalsePat -> On_ast.Ident_set.empty
  | On_ast.RecPat m ->
    m
    |> On_ast.Ident_map.enum
    |> Enum.fold
      (fun idents (_,pat') ->
         On_ast.Ident_set.union idents (pat_vars pat')
      )
      On_ast.Ident_set.empty
  | On_ast.VariantPat(Variant(_,pat')) -> pat_vars pat'
  | On_ast.VarPat x -> On_ast.Ident_set.singleton x
  | On_ast.FunPat -> On_ast.Ident_set.empty
  | On_ast.EmptyLstPat -> On_ast.Ident_set.empty
  | On_ast.LstDestructPat (p1, p2) ->
    On_ast.Ident_set.union (pat_vars p1) (pat_vars p2)
;;

(** Performs variable substitution on a pattern. *)
let rec pat_rename_vars
    (renaming : On_ast.Ident.t On_ast.Ident_map.t)
    (pat : On_ast.pattern)
  : On_ast.pattern =
  match pat with
  | On_ast.AnyPat -> pat
  | On_ast.IntPat -> pat
  | On_ast.TruePat -> pat
  | On_ast.FalsePat -> pat
  | On_ast.RecPat m ->
    On_ast.RecPat(On_ast.Ident_map.map (pat_rename_vars renaming) m)
  | On_ast.VariantPat(Variant(lbl,pat')) ->
    On_ast.VariantPat(Variant(lbl, pat_rename_vars renaming pat'))
  | On_ast.VarPat i -> On_ast.VarPat(On_ast.Ident_map.find_default i i renaming)
  | On_ast.FunPat -> pat
  | On_ast.EmptyLstPat -> pat
  | On_ast.LstDestructPat (hd, tl) ->
    On_ast.LstDestructPat(pat_rename_vars renaming hd,
                          pat_rename_vars renaming tl)
;;

(* Transform an expression to eliminate "let rec" expressions by encoding with
   self-passing. *)
let rec_transform (e : On_ast.expr) : On_ast.expr m =
  let transformer recurse e =
    match e with
    | On_ast.LetRecFun(fun_sig_list, rec_expr) ->
      let%bind transformed_rec_expr = recurse rec_expr in
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
      let%bind appls_for_funs =
        list_fold_left_m
          (fun appl_dict -> fun base_fun ->
             let (original_fun_name, new_fun_name) = base_fun in
             let sub_appl =
               List.fold_left
                 (fun acc fun_name -> On_ast.Appl(acc, Var(fun_name)))
                 (Var(new_fun_name)) new_names in
             return @@
             On_ast.Ident_map.add
               original_fun_name sub_appl appl_dict)
          On_ast.Ident_map.empty name_pairs
      in
      let let_maker_fun = (fun fun_name -> fun acc ->
          let cur_appl_expr = On_ast.Ident_map.find fun_name appls_for_funs in
          On_ast.Let(fun_name, cur_appl_expr, acc))
      in
      let transformed_outer_expr =
        List.fold_right let_maker_fun original_names transformed_rec_expr
      in
      let sig_name_pairs = List.combine fun_sig_list new_names in
      let%bind ret_expr =
        list_fold_right_m (fun (fun_sig, fun_new_name) -> fun acc ->
            let (On_ast.Funsig (_, param_list, cur_f_expr)) = fun_sig in
            let%bind transformed_cur_f_expr = recurse cur_f_expr in
            let new_param_list = new_names @ param_list in
            let new_fun_expr =
              List.fold_right
                let_maker_fun original_names transformed_cur_f_expr
            in
            return @@
            On_ast.Let(fun_new_name,
                       Function (new_param_list, new_fun_expr),
                       acc)
          ) sig_name_pairs transformed_outer_expr
      in
      return ret_expr
    | _ ->
      return e
  in
  Translator_utils.m_transform_expr transformer e
;;

(* Performs alpha substitution on a given expression. *)
let rec rename_variable
    (old_name : On_ast.ident)
    (new_name : On_ast.ident)
    (e : On_ast.expr)
  : On_ast.expr =
  (* NOTE: the generic homomorphism routine m_env_transform_expr does not allow
     us to change the environment of the homomorphism as we descend or to block
     descending into a given subtree, so we can't use it here. *)
  let recurse = rename_variable old_name new_name in
  match e with
  | On_ast.Var(id) ->
    if id = old_name then
      On_ast.Var(new_name)
    else
      On_ast.Var(id)
  | On_ast.Input -> On_ast.Input
  | On_ast.Function (id_list, e') ->
    if (List.exists (On_ast.Ident.equal old_name) id_list) then
      e
    else
      let new_e' = recurse e' in
      On_ast.Function(id_list, new_e')
  | On_ast.Appl(e1, e2) ->
    On_ast.Appl(recurse e1, recurse e2)
  | On_ast.Let (id, e1, e2) ->
    let new_e1 = recurse e1 in
    if id = old_name then
      On_ast.Let(id, new_e1, e2)
    else
      let new_e2 = recurse e2 in
      On_ast.Let(id, new_e1, new_e2)
  | On_ast.LetRecFun (f_sigs, e') ->
    let function_names =
      f_sigs
      |> List.enum
      |> Enum.map (fun (On_ast.Funsig(name,_,_)) -> name)
      |> On_ast.Ident_set.of_enum
    in
    let f_sigs' =
      if On_ast.Ident_set.mem old_name function_names then
        f_sigs
      else
        f_sigs
        |> List.map
          (fun (On_ast.Funsig(name,params,body)) ->
             if List.exists (On_ast.Ident.equal old_name) params then
               On_ast.Funsig(name,params,body)
             else
               On_ast.Funsig(name,params,recurse body)
          )
    in
    let e'' =
      if On_ast.Ident_set.mem old_name function_names then
        e'
      else
        recurse e'
    in
    On_ast.LetRecFun(f_sigs', e'')
  | On_ast.LetFun (f_sig, e') ->
    let (On_ast.Funsig(id, id_list, fun_e)) = f_sig in
    (* If the old_name is same as the function name, then we don't want
       to change anything. *)
    if id = old_name then
      e
    else
      (
        (* If the old_name is same as one of the names of the params, then
           we only want to change the code outside of the function.
        *)
        if List.exists (On_ast.Ident.equal old_name) id_list then
          (
            let new_e' = recurse e' in
            On_ast.LetFun (f_sig, new_e')
          )
        else (* change both the inside and the outside expressions *)
          (
            let new_inner_e = recurse fun_e in
            let new_outer_e = recurse e' in
            let new_funsig = On_ast.Funsig(id, id_list, new_inner_e) in
            On_ast.LetFun(new_funsig, new_outer_e)
          )
      )
  | On_ast.Plus (e1, e2) -> On_ast.Plus(recurse e1, recurse e2)
  | On_ast.Minus (e1, e2) -> On_ast.Minus(recurse e1, recurse e2)
  | On_ast.Times (e1, e2) -> On_ast.Times(recurse e1, recurse e2)
  | On_ast.Divide (e1, e2) -> On_ast.Divide(recurse e1, recurse e2)
  | On_ast.Modulus (e1, e2) -> On_ast.Modulus(recurse e1, recurse e2)
  | On_ast.Equal (e1, e2) -> On_ast.Equal(recurse e1, recurse e2)
  | On_ast.LessThan (e1, e2) -> On_ast.LessThan(recurse e1, recurse e2)
  | On_ast.Leq (e1, e2) -> On_ast.Leq(recurse e1, recurse e2)
  | On_ast.And (e1, e2) -> On_ast.And(recurse e1, recurse e2)
  | On_ast.Or (e1, e2) -> On_ast.Or(recurse e1, recurse e2)
  | On_ast.Not e1 -> On_ast.Not(recurse e1)
  | On_ast.If (e1, e2, e3) -> On_ast.If(recurse e1, recurse e2, recurse e3)
  | On_ast.Int _
  | On_ast.Bool _ -> e
  | On_ast.Record m -> On_ast.Record (On_ast.Ident_map.map recurse m)
  | On_ast.RecordProj (e1, lbl) -> On_ast.RecordProj(recurse e1, lbl)
  | On_ast.Match (e0, cases) ->
    let e0' = recurse e0 in
    let cases' =
      cases
      |> List.map
        (fun (pattern, body) ->
           if On_ast.Ident_set.mem old_name (pat_vars pattern) then
             (pattern, body)
           else
             (pattern, recurse body)
        )
    in
    On_ast.Match(e0', cases')
  | On_ast.VariantExpr (lbl, e1) -> On_ast.VariantExpr(lbl, recurse e1)
  | On_ast.List es -> On_ast.List(List.map recurse es)
  | On_ast.ListCons (e1, e2) -> On_ast.ListCons(recurse e1, recurse e2)
;;

(** This function alphatizes an entire expression.  If a variable is defined
    more than once in the given expression, all but one of the declarations will
    be alpha-renamed to a fresh name.
*)
let alphatize (e : On_ast.expr) : On_ast.expr m =
  let open TranslationMonad in
  let open On_ast in
  (* Given a list of identifiers, a list of expressions, and a list of
     previously declared identifiers, this helper routine renames all previously
     declared identifiers which appear in the list within all of the
     expressions.  The returned values are the renamed list of identifiers,
     the renamed expressions, the new set of declared identifiers, and a
     dictionary mapping the identifiers which were renamed onto their new
     values. *)
  let rec ensure_exprs_unique_names
      (names : Ident.t list)
      (exprs : expr list)
      (previously_declared : Ident_set.t)
    : (Ident.t list * expr list * Ident_set.t * Ident.t Ident_map.t) m =
    match names with
    | [] ->
      return ([], exprs, previously_declared, Ident_map.empty)
    | name::more_names ->
      let%bind (more_names', exprs', previously_declared', renaming') =
        ensure_exprs_unique_names more_names exprs previously_declared
      in
      if Ident_set.mem name previously_declared' then begin
        let Ident(s) = name in
        let%bind new_s = fresh_name s in
        let new_name = Ident(new_s) in
        let exprs'' = List.map (rename_variable name new_name) exprs' in
        let previously_declared'' =
          Ident_set.add new_name previously_declared'
        in
        let renaming'' = Ident_map.add name new_name renaming' in
        return
          (new_name::more_names', exprs'', previously_declared'', renaming'')
      end else
        let previously_declared'' = Ident_set.add name previously_declared' in
        return (name::more_names', exprs', previously_declared'', renaming')
  in
  let ensure_expr_unique_names names expr seen =
    let%bind (names',exprs',seen',renaming') =
      ensure_exprs_unique_names names [expr] seen
    in
    return (names',List.hd exprs',seen',renaming')
  in
  let rec walk (expr : expr) (seen_declared : Ident_set.t)
    : (expr * Ident_set.t) m =
    let zero () =
      raise @@ Jhupllib_utils.Invariant_failure "list changed size"
    in
    match expr with
    (* In leaf cases, no new variables are defined and so we have no work to
       do. *)
    | Var _
    | Input
    | Int _
    | Bool _ ->
      return (expr, seen_declared)
    | Function (params, body) ->
      let%bind body', seen_declared' = walk body seen_declared in
      (* FIXME?: assuming that parameters in functions are not duplicated;
                 probably should verify that somewhere *)
      let%bind (params', body'', seen_declared'', _) =
        ensure_expr_unique_names params body' seen_declared'
      in
      return (Function(params', body''), seen_declared'')
    | Appl (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return @@ (Appl (e1', e2'), seen_declared'')
    | Let (x, e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      let%bind (xs,es,seen_declared''',_) =
        ensure_exprs_unique_names [x] [e1';e2'] seen_declared''
      in
      let%orzero ([x'],[e1'';e2'']) = (xs,es) in
      return (Let(x', e1'', e2''), seen_declared''')
    | LetRecFun (funsigs, expr) ->
      let%bind funsigs'rev, seen_declared' =
        list_fold_left_m
          (fun (acc, seen) (Funsig(name,params,body)) ->
             let%bind body', seen' = walk body seen in
             return ((Funsig(name,params,body'))::acc, seen')
          )
          ([], seen_declared)
          funsigs
      in
      let funsigs' = List.rev funsigs'rev in
      (* FIXME?: assuming that parameters in functions are not duplicated;
                 probably should verify that somewhere *)
      (* FIXME?: assuming that function names in recursive groups are not
                 duplicated; probably should verify that somewhere *)
      (* First, make sure that all of the function *names* are unique. *)
      let function_names, function_bodies =
        List.split @@ List.map (fun (Funsig(name,_,body)) -> name,body) funsigs'
      in
      let%bind function_names', out_exprs, seen_declared'', _ =
        ensure_exprs_unique_names
          function_names
          (expr :: function_bodies)
          seen_declared'
      in
      let%orzero (expr' :: function_bodies') = out_exprs in
      let funsigs'' =
        List.combine function_names' function_bodies'
        |> List.combine funsigs'
        |> List.map
          (fun ((Funsig(_,params,_)),(name,body)) -> Funsig(name,params,body))
      in
      (* Now, for each function, make sure that the *parameters* are unique. *)
      let%bind funsigs'''_rev, seen_declared''' =
        funsigs''
        |> list_fold_left_m
          (fun (out_funsigs, seen) (Funsig(name,params,body)) ->
             let%bind (params', body', seen', _) =
               ensure_expr_unique_names params body seen
             in
             return ((Funsig(name, params', body'))::out_funsigs, seen')
          )
          ([], seen_declared'')
      in
      return (LetRecFun(List.rev funsigs'''_rev, expr'), seen_declared''')
    | LetFun (funsig, expr) ->
      (* FIXME?: assuming that parameters in functions are not duplicated;
                 probably should verify that somewhere *)
      (* Unpack signature *)
      let Funsig(name, params, body) = funsig in
      (* Recurse on the second expression to ensure that it is internally
         alphatized. *)
      let%bind (expr', seen_declared') = walk expr seen_declared in
      (* Perform renamings on any names which we have already seen from the
         outside. *)
      let%bind names', expr'', seen_declared'', _ =
        ensure_expr_unique_names [name] expr' seen_declared'
      in
      let%orzero [name'] = names' in
      (* Recurse on the body expression to ensure that it is internally
         alphatized. *)
      let%bind (body', seen_declared''') = walk body seen_declared'' in
      (* Perform renamings on any names which we have already seen from the
         outside. *)
      let%bind params', body'', seen_declared'''', _ =
        ensure_expr_unique_names params body' seen_declared'''
      in
      return (LetFun(Funsig(name', params', body''), expr''), seen_declared'''')
    | Plus (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (Plus(e1', e2'), seen_declared'')
    | Minus (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (Minus(e1', e2'), seen_declared'')
    | Times (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (Times(e1', e2'), seen_declared'')
    | Divide (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (Divide(e1', e2'), seen_declared'')
    | Modulus (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (Modulus(e1', e2'), seen_declared'')
    | Equal (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (Equal(e1', e2'), seen_declared'')
    | LessThan (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (LessThan(e1', e2'), seen_declared'')
    | Leq (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (Leq(e1', e2'), seen_declared'')
    | And (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (And(e1', e2'), seen_declared'')
    | Or (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (Or(e1', e2'), seen_declared'')
    | Not e1 ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      return (Not e1', seen_declared')
    | If (e1, e2, e3) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      let%bind e3', seen_declared''' = walk e3 seen_declared'' in
      return (If(e1', e2', e3'), seen_declared''')
    | Record mapping ->
      let%bind mapping', seen_declared' =
        mapping
        |> Ident_map.enum
        |> List.of_enum
        |> list_fold_left_m
          (fun (acc,seen) (lbl,expr) ->
             let%bind expr', seen' = walk expr seen in
             return ((lbl,expr')::acc, seen')
          )
          ([], seen_declared)
        |> lift1
          (fun (acc,seen) -> (Ident_map.of_enum @@ List.enum acc, seen))
      in
      return (Record mapping', seen_declared')
    | RecordProj (e1, lbl) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      return (RecordProj(e1', lbl), seen_declared')
    | Match (e0, cases) ->
      let%bind e0', seen_declared' = walk e0 seen_declared in
      let%bind cases_rev, seen_declared'' =
        cases
        |> list_fold_left_m
          (fun (acc, seen) (pat, body) ->
             (* FIXME?: assuming that patterns contain unique variables.  Should
                        probably verify that somewhere. *)
             let vars = pat_vars pat in
             let%bind renaming =
               vars
               |> Ident_set.enum
               |> Enum.map
                 (fun ((Ident s) as i) ->
                    let%bind s' = fresh_name s in
                    return (i, Ident s')
                 )
               |> List.of_enum
               |> sequence
               |> lift1 List.enum
               |> lift1 Ident_map.of_enum
             in
             let pat' = pat_rename_vars renaming pat in
             let body' =
               Ident_map.enum renaming
               |> Enum.fold
                 (fun body_expr (from_ident,to_ident) ->
                    rename_variable from_ident to_ident body_expr
                 )
                 body
             in
             let seen' =
               Ident_set.union seen @@
               (renaming |> Ident_map.values |> Ident_set.of_enum)
             in
             return ((pat', body')::acc, seen')
          )
          ([], seen_declared')
      in
      let cases' = List.rev cases_rev in
      return (Match(e0', cases'), seen_declared'')
    | VariantExpr (lbl, e1) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      return (VariantExpr(lbl, e1'), seen_declared')
    | List es ->
      let%bind (es'rev, seen_declared') =
        es
        |> list_fold_left_m
          (fun (ret, seen) e ->
             let%bind e', seen' = walk e seen in
             return (e'::ret, seen')
          )
          ([], seen_declared)
      in
      return (List(List.rev es'rev), seen_declared')
    | ListCons (e1, e2) ->
      let%bind e1', seen_declared' = walk e1 seen_declared in
      let%bind e2', seen_declared'' = walk e2 seen_declared' in
      return (ListCons(e1', e2'), seen_declared'')
  in
  lift1 fst @@ walk e Ident_set.empty
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

  flatten_expr
    (e : On_ast.expr)
  : (Ast.clause list * Ast.var) m =
  match e with
  | Var (id) ->
    let%bind return_var = fresh_var "var" in
    let Ident(i_string) = id in
    let id_var = Ast.Var(Ast.Ident(i_string), None) in
    return ([Ast.Clause(return_var, Ast.Var_body(id_var))], return_var)
  | Input ->
    let%bind input_var = fresh_var "input" in
    return ([Ast.Clause(input_var, Ast.Input_body)], input_var)
  | Function (id_list, e) ->
    let%bind (fun_c_list, _) = nonempty_body @@@ flatten_expr e in
    let body_expr = Ast.Expr(fun_c_list) in
    let%bind (Expr(fun_clause), return_var) = flatten_fun  id_list body_expr in
    return (fun_clause, return_var)
  | Appl (e1, e2) ->
    let%bind (e1_clist, e1_var) = flatten_expr e1 in
    let%bind (e2_clist, e2_var) = flatten_expr e2 in
    let%bind new_var = fresh_var "appl" in
    let new_clause =
      Ast.Clause (
        new_var,
        Ast.Appl_body(e1_var, e2_var)
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
      flatten_fun ~binding_name:(Some fun_name) id_list (Expr(body_clist))
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
    let%bind (e_clist, e_var) = flatten_expr e in
    let%bind true_var = fresh_var "true" in
    let true_clause = Ast.Clause(true_var, Ast.Value_body(Value_bool true)) in
    let%bind new_var = fresh_var "binop" in
    let new_clause =
      Ast.Clause(new_var,
                 Ast.Binary_operation_body(
                   e_var, Ast.Binary_operator_xor, true_var))
    in
    return (e_clist @ [true_clause; new_clause], new_var)
  | If (e1, e2, e3) ->
    (* TODO: there will be another version of a conditional where we can
       do pattern matching. *)
    (* NOTE: this is translation from an if statement. Thus e1 will be always
       matched with true. *)
    let%bind (e1_clist, e1_var) = flatten_expr e1 in
    let%bind (e2_clist, _) = nonempty_body @@@ flatten_expr e2 in
    let%bind (e3_clist, _) = nonempty_body @@@ flatten_expr e3 in
    let%bind new_clausevar = fresh_var "if" in
    let new_clause =
      Ast.Clause(new_clausevar,
                 Ast.Conditional_body(e1_var,
                                      Expr(e2_clist),
                                      Expr(e3_clist)))
    in
    return (e1_clist @ [new_clause], new_clausevar)
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
  | Match (subject, pat_expr_list) ->
    (* We need to convert the subject first *)
    let%bind (subject_clause_list, subject_var) = flatten_expr subject in
    (* List.fold_right routine that deeply nests the contents of the match
       into a series of odefa conditionals *)
    (* the type of the accumulator would be the entire expression that goes into
       the "else" case of the next conditional *)
    let match_converter curr acc =
      (
        let (curr_pat, curr_pat_expr) = curr in
        let%bind cond_var = fresh_var "match_cond" in
        let rec pat_conversion = fun pat ->
          (match pat with
           | On_ast.AnyPat -> Ast.Any_pattern
           | On_ast.IntPat -> Ast.Int_pattern
           | On_ast.TruePat -> Ast.Bool_pattern(true)
           | On_ast.FalsePat -> Ast.Bool_pattern(false)
           | On_ast.FunPat -> Ast.Fun_pattern
           | On_ast.RecPat (patmap) ->
             let rec_conversion =
               fun key -> fun entry -> fun acc ->
                 let (On_ast.Ident key_str) = key in
                 let new_key = Ast.Ident key_str in
                 let new_entry = pat_conversion entry in
                 Ast.Ident_map.add new_key new_entry acc
             in
             let new_pat_map =
               On_ast.Ident_map.fold rec_conversion patmap Ast.Ident_map.empty
             in (Record_pattern new_pat_map)
           | On_ast.VariantPat (_) ->
             raise @@ Utils.Invariant_failure
               "match_converter: Variants patterns should have been encoded!"
           | On_ast.VarPat (_) ->
             raise @@ Utils.Invariant_failure
               "match_converter: Var patterns should have been encoded!"
           | On_ast.EmptyLstPat | On_ast.LstDestructPat _ ->
             raise @@ Utils.Invariant_failure
               "match_converter: List patterns should have been encoded!"
          )
        in
        let ast_pat = pat_conversion curr_pat in
        let%bind (flat_pat_expr, _) = flatten_expr curr_pat_expr in
        let%bind match_var = fresh_var "match" in
        let match_clause =
          Ast.Clause(match_var, Ast.Match_body(subject_var, ast_pat))
        in
        let if_clause =
          Ast.Clause(cond_var,
                     Ast.Conditional_body(match_var, Expr flat_pat_expr, acc)
                    )
        in
        return @@ Ast.Expr([match_clause; if_clause])
      )
    in
    (* The base case is our EXPLODING clause *)
    let%bind explode_expr =
      let%bind zero_var = fresh_var "zero" in
      let zero_clause = Ast.Clause(zero_var, Ast.Value_body(Ast.Value_int(0))) in
      let%bind zero_appl_var = fresh_var "explode" in
      let zero_appl_clause =
        (* TODO: consider: perhaps annotate this exploding clause to indicate
           that it's artificial and not user-written? *)
        Ast.Clause(
          zero_appl_var,
          Ast.Appl_body(zero_var, zero_var))
      in
      return @@ Ast.Expr([zero_clause; zero_appl_clause])
    in
    let%bind match_expr =
      list_fold_right_m match_converter pat_expr_list explode_expr
    in
    let Ast.Expr(match_clauses) = match_expr in
    let match_last_clause = List.last match_clauses in
    let Ast.Clause(match_last_clause_var, _) = match_last_clause in
    let all_clauses = subject_clause_list @ match_clauses in
    return (all_clauses, match_last_clause_var)
  | VariantExpr (_, _) ->
    raise @@ Utils.Invariant_failure
      "flatten_expr: VariantExpr expressions should have been desugared."
  | List _ | ListCons _ ->
    raise @@ Utils.Invariant_failure
      "flatten_expr: List expressions should have been handled!"
;;

let debug_transform
    (name : string)
    (transform : On_ast.expr -> On_ast.expr m)
    (e : On_ast.expr)
  : On_ast.expr m =
  lazy_logger `trace @@ (fun () ->
      Printf.sprintf "%s on:\n%s" name (On_ast.show_expr e));
  let%bind answer = transform e in
  lazy_logger `trace @@ (fun () ->
      Printf.sprintf "%s on:\n%s\nproduces\n%s"
        name (On_ast.show_expr e) (On_ast.show_expr answer));
  return answer
;;

let translate
    ?translation_context:(translation_context=None)
    (e : On_ast.expr)
  : Odefa_ast.Ast.expr =
  let e_m =
    let%bind transformed_e =
      return e
      >>= debug_transform "pre-alphatize" alphatize
      >>= debug_transform "encode recursion" rec_transform
      >>= debug_transform "encode lists" list_transform
      >>= debug_transform "encode variants" encode_variant
      >>= debug_transform "encode variable patterns" eliminate_var_pat
      >>= debug_transform "post-alphatize" alphatize
    in
    let%bind (c_list, _) = flatten_expr transformed_e in
    let Clause(last_var, _) = List.last c_list in
    let%bind fresh_str = freshness_string in
    let res_var = Ast.Var(Ast.Ident(fresh_str ^ "result"), None) in
    let res_clause = Ast.Clause(res_var, Ast.Var_body(last_var)) in
    return @@ Ast.Expr(c_list @ [res_clause])
  in
  let context =
    match translation_context with
    | None -> new_translation_context ()
    | Some ctx -> ctx
  in
  run context e_m
  (* NOTE: commenting this out for DDSE because it has a tendency to eliminate
     unnecessary variables and we use those as targets *)
  (* |> eliminate_aliases *)
;;
