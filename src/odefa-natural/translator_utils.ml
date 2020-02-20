open Batteries;;

open Odefa_ast;;

type translation_context =
  { mutable tc_fresh_name_counter : int;
    tc_fresh_suffix_separator : string;
    tc_contextual_recursion : bool;
  }
[@@deriving eq, ord, show]
;;

let new_translation_context
    ?suffix:(suffix=("~"))
    ?contextual_recursion:(contextual_recursion=(true))
    ()
  : translation_context =
  { tc_fresh_name_counter = 0;
    tc_fresh_suffix_separator = suffix;
    tc_contextual_recursion = contextual_recursion;
  }
;;

module TranslationMonad :
sig
  include Monad.Monad;;
  val run : translation_context -> 'a m -> 'a
  val fresh_name : string -> string m
  val fresh_var : string -> Ast.var m
  val freshness_string : string m
  val acontextual_recursion : bool m
  val sequence : 'a m list -> 'a list m
  val list_fold_left_m : ('acc -> 'el -> 'acc m) -> 'acc -> 'el list -> 'acc m
  val list_fold_right_m : ('el -> 'acc -> 'acc m) -> 'el list -> 'acc -> 'acc m
  val (@@@) : ('a -> 'b m) -> 'a m -> 'b m
end =
struct
  include Monad.Make(
    struct
      type 'a m = translation_context -> 'a;;
      let return (x : 'a) : 'a m = (fun _ -> x);;
      let bind (x : 'a m) (f : 'a -> 'b m) : 'b m =
        fun ctx -> f (x ctx) ctx
      ;;
    end
    );;
  let run ctx m =
    m ctx
  ;;
  let fresh_name name ctx =
    let n = ctx.tc_fresh_name_counter in
    ctx.tc_fresh_name_counter <- n + 1;
    name ^ ctx.tc_fresh_suffix_separator ^ string_of_int n
  ;;
  let fresh_var name ctx =
    let name' = fresh_name name ctx in
    Ast.Var(Ast.Ident name', None)
  ;;
  let freshness_string ctx = ctx.tc_fresh_suffix_separator;;
  let acontextual_recursion ctx = not ctx.tc_contextual_recursion;;
  let rec sequence ms =
    match ms with
    | [] -> return []
    | h::t ->
      let%bind h' = h in
      let%bind t' = sequence t in
      return @@ h' :: t'
  ;;
  let rec list_fold_left_m fn acc els =
    match els with
    | [] -> return acc
    | h :: t ->
      let%bind acc' = fn acc h in
      list_fold_left_m fn acc' t
  ;;
  let rec list_fold_right_m fn els acc =
    match els with
    | [] -> return acc
    | h :: t ->
      let%bind acc' = list_fold_right_m fn t acc in
      fn h acc'
  ;;
  let (@@@) f x = bind x f;;
end;;

let ident_map_map_m
    (fn : 'a -> 'b TranslationMonad.m)
    (m : 'a On_ast.Ident_map.t)
  : 'b On_ast.Ident_map.t TranslationMonad.m =
  let open TranslationMonad in
  m
  |> On_ast.Ident_map.enum
  |> Enum.map (fun (k,v) -> let%bind v' = fn v in return (k,v'))
  |> List.of_enum
  |> sequence
  |> lift1 List.enum
  |> lift1 On_ast.Ident_map.of_enum
;;

(* *** Generalized transformations for expressions with reader and writer
   support. *** *)

type ('env,'out) env_out_expr_transformer =
  ('env -> On_ast.expr -> (On_ast.expr * 'out)) ->
  'env ->
  On_ast.expr ->
  On_ast.expr * 'out
;;

let rec env_out_transform_expr
    (transformer : ('env,'out) env_out_expr_transformer)
    (combiner : 'out -> 'out -> 'out)
    (default : 'out)
    (env : 'env)
    (e : On_ast.expr)
  : On_ast.expr * 'out =
  let recurse : 'env -> On_ast.expr -> On_ast.expr * 'out =
    env_out_transform_expr transformer combiner default
  in
  let transform_funsig (On_ast.Funsig(name,args,body)) =
    let (body',out') = recurse env body in
    let (body'',out'') = transformer recurse env body' in
    (On_ast.Funsig(name,args,body''), combiner out' out'')
  in
  let (e' : On_ast.expr), (out' : 'out) =
    match e with
    | On_ast.Var x ->
      (On_ast.Var x, default)
    | On_ast.Input ->
      (On_ast.Input, default)
    | On_ast.Function (x, e1) ->
      let (e1', out1) = recurse env e1 in
      (On_ast.Function(x, e1'), out1)
    | On_ast.Appl (e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Appl(e1', e2'), combiner out1 out2)
    | On_ast.Let (x, e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Let(x, e1', e2'), combiner out1 out2)
    | On_ast.LetRecFun (funsigs, e1) ->
      let (e1', out1) = recurse env e1 in
      let (funsigs', outs) = List.split @@ List.map transform_funsig funsigs in
      let out = List.fold_left combiner out1 outs in
      (On_ast.LetRecFun(funsigs', e1'), out)
    | On_ast.LetFun (funsig, e1) ->
      let (e1', out1) = recurse env e1 in
      let (funsig', out2) = transform_funsig funsig in
      (On_ast.LetFun(funsig', e1'), combiner out1 out2)
    | On_ast.Plus (e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Plus(e1', e2'), combiner out1 out2)
    | On_ast.Minus (e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Minus(e1', e2'), combiner out1 out2)
    | On_ast.Times (e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Times(e1', e2'), combiner out1 out2)
    | On_ast.Divide (e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Divide(e1', e2'), combiner out1 out2)
    | On_ast.Modulus (e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Modulus(e1', e2'), combiner out1 out2)
    | On_ast.Equal(e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Equal(e1', e2'), combiner out1 out2)
    | On_ast.LessThan(e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.LessThan(e1', e2'), combiner out1 out2)
    | On_ast.Leq(e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Leq(e1', e2'), combiner out1 out2)
    | On_ast.And(e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.And(e1', e2'), combiner out1 out2)
    | On_ast.Or(e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.Or(e1', e2'), combiner out1 out2)
    | On_ast.Not e1 ->
      let (e1', out1) = recurse env e1 in
      (On_ast.Not(e1'), out1)
    | On_ast.If (e1, e2, e3) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      let (e3', out3) = recurse env e3 in
      (On_ast.If(e1', e2', e3'), combiner (combiner out1 out2) out3)
    | On_ast.Int n -> (On_ast.Int n, default)
    | On_ast.Bool b -> (On_ast.Bool b, default)
    | On_ast.Record r ->
      let kvpairs, outs =
        On_ast.Ident_map.enum r
        |> Enum.map
          (fun (k,v) ->
             let (v',out) = recurse env v in
             ((k,v'), out)
          )
        |> Enum.uncombine
      in
      let r' = On_ast.Ident_map.of_enum kvpairs in
      let out = Enum.fold combiner default outs in
      (On_ast.Record r', out)
    | On_ast.RecordProj (e1, l) ->
      let (e1', out1) = recurse env e1 in
      (On_ast.RecordProj(e1', l), out1)
    | On_ast.Match (e0, branches) ->
      let (e0', out0) = recurse env e0 in
      let (branches', outs) =
        List.split @@
        List.map
          (fun (pat,expr) ->
             let (expr',out) = recurse env expr in
             ((pat, expr'), out)
          )
          branches
      in
      let out = List.fold_left combiner out0 outs in
      (On_ast.Match(e0', branches'), out)
    | On_ast.VariantExpr (l, e1) ->
      let (e1', out1) = recurse env e1 in
      (On_ast.VariantExpr(l, e1'), out1)
    | On_ast.List es ->
      let (es', outs) = List.split @@ List.map (recurse env) es in
      let out = List.fold_left combiner default outs in
      (On_ast.List es', out)
    | On_ast.ListCons (e1, e2) ->
      let (e1', out1) = recurse env e1 in
      let (e2', out2) = recurse env e2 in
      (On_ast.ListCons(e1', e2'), combiner out1 out2)
  in
  let (e'', out'') = transformer recurse env e' in
  (e'', combiner out' out'')
;;

type 'env env_expr_transformer =
  ('env -> On_ast.expr -> On_ast.expr) -> 'env -> On_ast.expr -> On_ast.expr
;;

let env_transform_expr
    (transformer : 'env env_expr_transformer)
    (env : 'env)
    (e : On_ast.expr)
  : On_ast.expr =
  let transformer'
      (recurse : 'env -> On_ast.expr -> (On_ast.expr * unit))
      env
      (e : On_ast.expr)
    : (On_ast.expr * unit) =
    let recurse' env e =
      let (e'', ()) = recurse env e in e''
    in
    (transformer recurse' env e, ())
  in
  let (e', ()) = env_out_transform_expr transformer' (fun _ _ -> ()) () env e in
  e'
;;

type expr_transformer =
  (On_ast.expr -> On_ast.expr) -> On_ast.expr -> On_ast.expr
;;

let transform_expr (transformer : expr_transformer) (e : On_ast.expr)
  : On_ast.expr =
  let transformer'
      (recurse : unit -> On_ast.expr -> On_ast.expr) () (e : On_ast.expr)
    : On_ast.expr =
    let recurse' e = recurse () e in
    transformer recurse' e
  in
  env_transform_expr transformer' () e
;;

(* *** Generalized monadic transformations for expressions with reader and
   writer support. *** *)

type ('env, 'out) m_env_out_expr_transformer =
  ('env -> On_ast.expr -> (On_ast.expr * 'out) TranslationMonad.m) ->
  'env -> On_ast.expr -> (On_ast.expr * 'out) TranslationMonad.m
;;

let rec m_env_out_transform_expr
    (transformer : ('env, 'out) m_env_out_expr_transformer)
    (combiner : 'out -> 'out -> 'out)
    (default : 'out)
    (env : 'env)
    (e : On_ast.expr)
  : (On_ast.expr * 'out) TranslationMonad.m =
  let recurse = m_env_out_transform_expr transformer combiner default in
  let open TranslationMonad in
  let transform_funsig (On_ast.Funsig(name,args,body)) =
    let%bind (body', out') = recurse env body in
    let%bind (body'', out'') = transformer recurse env body' in
    return @@ (On_ast.Funsig(name,args,body''), combiner out' out'')
  in
  let%bind ((e' : On_ast.expr), (out' : 'out)) =
    match e with
    | On_ast.Var x -> return @@ (On_ast.Var x, default)
    | On_ast.Input -> return @@ (On_ast.Input, default)
    | On_ast.Function (x, e1) ->
      let%bind (e1', out1) = recurse env e1 in
      return @@ (On_ast.Function(x, e1'), out1)
    | On_ast.Appl (e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Appl(e1', e2'), combiner out1 out2)
    | On_ast.Let (x, e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Let(x, e1', e2'), combiner out1 out2)
    | On_ast.LetRecFun (funsigs, e1) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (funsigs', outs) =
        lift1 List.split @@ sequence @@ List.map transform_funsig funsigs
      in
      let out = List.fold_left combiner out1 outs in
      return @@ (On_ast.LetRecFun(funsigs', e1'), out)
    | On_ast.LetFun (funsig, e1) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (funsig', out2) = transform_funsig funsig in
      return @@ (On_ast.LetFun(funsig', e1'), combiner out1 out2)
    | On_ast.Plus (e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Plus(e1', e2'), combiner out1 out2)
    | On_ast.Minus (e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Minus(e1', e2'), combiner out1 out2)
    | On_ast.Times (e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Times(e1', e2'), combiner out1 out2)
    | On_ast.Divide (e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Divide(e1', e2'), combiner out1 out2)
    | On_ast.Modulus (e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Modulus(e1', e2'), combiner out1 out2)
    | On_ast.Equal(e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Equal(e1', e2'), combiner out1 out2)
    | On_ast.LessThan(e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.LessThan(e1', e2'), combiner out1 out2)
    | On_ast.Leq(e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Leq(e1', e2'), combiner out1 out2)
    | On_ast.And(e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.And(e1', e2'), combiner out1 out2)
    | On_ast.Or(e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.Or(e1', e2'), combiner out1 out2)
    | On_ast.Not e1 ->
      let%bind (e1', out1) = recurse env e1 in
      return @@ (On_ast.Not(e1'), out1)
    | On_ast.If (e1, e2, e3) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      let%bind (e3', out3) = recurse env e3 in
      return @@ (On_ast.If(e1', e2', e3'), combiner (combiner out1 out2) out3)
    | On_ast.Int n -> return @@ (On_ast.Int n, default)
    | On_ast.Bool b -> return @@ (On_ast.Bool b, default)
    | On_ast.Record r ->
      let%bind (mappings, outs) =
        r
        |> On_ast.Ident_map.enum
        |> Enum.map
          (fun (k,v) ->
             let%bind (v',out') = recurse env v in
             return ((k,v'), out')
          )
        |> List.of_enum
        |> sequence
        |> lift1 List.enum
        |> lift1 Enum.uncombine
      in
      let r' = On_ast.Ident_map.of_enum mappings in
      let out = Enum.fold combiner default outs in
      return @@ (On_ast.Record r', out)
    | On_ast.RecordProj (e1, l) ->
      let%bind (e1', out) = recurse env e1 in
      return @@ (On_ast.RecordProj(e1', l), out)
    | On_ast.Match (e0, branches) ->
      let%bind (e0', out0) = recurse env e0 in
      let%bind (branches', outs) =
        lift1 List.split @@
        sequence @@
        List.map
          (fun (pat,expr) ->
             let%bind (expr',out') = recurse env expr in
             return ((pat, expr'), out')
          )
          branches
      in
      let out = List.fold_left combiner out0 outs in
      return @@ (On_ast.Match(e0', branches'), out)
    | On_ast.VariantExpr (l, e1) ->
      let%bind (e1', out1) = recurse env e1 in
      return @@ (On_ast.VariantExpr(l, e1'), out1)
    | On_ast.List es ->
      let%bind (es', outs) =
        lift1 List.split @@ sequence @@ List.map (recurse env) es
      in
      let out = List.fold_left combiner default outs in
      return @@ (On_ast.List es', out)
    | On_ast.ListCons (e1, e2) ->
      let%bind (e1', out1) = recurse env e1 in
      let%bind (e2', out2) = recurse env e2 in
      return @@ (On_ast.ListCons(e1', e2'), combiner out1 out2)
  in
  let%bind (e'', out'') = transformer recurse env e' in
  return (e'', combiner out' out'')
;;

type 'env m_env_expr_transformer =
  ('env -> On_ast.expr -> On_ast.expr TranslationMonad.m) ->
  'env -> On_ast.expr -> On_ast.expr TranslationMonad.m
;;

let m_env_transform_expr
    (transformer : 'env m_env_expr_transformer)
    (env : 'env)
    (e : On_ast.expr)
  : On_ast.expr TranslationMonad.m =
  let open TranslationMonad in
  let transformer'
      (recurse : 'env -> On_ast.expr -> (On_ast.expr * unit) m)
      env
      (e : On_ast.expr)
    : (On_ast.expr * unit) m =
    let recurse' env e =
      let%bind (e'', ()) = recurse env e in return e''
    in
    let%bind e' = transformer recurse' env e in
    return (e', ())
  in
  let%bind (e', ()) =
    m_env_out_transform_expr transformer' (fun _ _ -> ()) () env e
  in
  return e'
;;

type m_expr_transformer =
  (On_ast.expr -> On_ast.expr TranslationMonad.m) -> On_ast.expr ->
  On_ast.expr TranslationMonad.m
;;

let m_transform_expr (transformer : m_expr_transformer) (e : On_ast.expr)
  : On_ast.expr TranslationMonad.m =
  let open TranslationMonad in
  let transformer'
      (recurse : unit -> On_ast.expr -> On_ast.expr m) () (e : On_ast.expr)
    : On_ast.expr TranslationMonad.m =
    let recurse' e = recurse () e in
    transformer recurse' e
  in
  m_env_transform_expr transformer' () e
;;
