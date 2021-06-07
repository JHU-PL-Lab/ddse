open Core

module T = struct
  type value =
    | Int of int [@printer Fmt.int]
    | Bool of bool [@printer Fmt.bool]
    | Fun of Id.t
    | Record
  [@@deriving sexp, compare, equal, show { with_path = false }]

  type binop =
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | Le
    | Leq
    | Eq
    | And
    | Or
    (* | Not *)
    | Xor
  [@@deriving sexp, compare, equal, show { with_path = false }]

  type fc_out = {
    xs_out : Id.t list;
    site : Id.t;
    stk_out : Relative_stack.t;
    f_out : Id.t;
  }
  [@@deriving sexp, compare, equal, show { with_path = false }]

  type fc = {
    xs_in : Id.t list;
    stk_in : Relative_stack.t;
    fun_in : Id.t;
    outs : fc_out list;
  }
  [@@deriving sexp, compare, equal, show { with_path = false }]

  type cf_in = { xs_in : Id.t list; stk_in : Relative_stack.t; fun_in : Id.t }
  [@@deriving sexp, compare, equal, show { with_path = false }]

  type cf = {
    xs_out : Id.t list;
    stk_out : Relative_stack.t;
    site : Id.t;
    f_out : Id.t;
    ins : cf_in list;
  }
  [@@deriving sexp, compare, equal, show { with_path = false }]

  type t =
    | Eq_v of Symbol.t * value
    | Eq_x of Symbol.t * Symbol.t
    | Eq_lookup of
        Lookup_stack.t * Relative_stack.t * Lookup_stack.t * Relative_stack.t
    | Eq_binop of Symbol.t * Symbol.t * binop * Symbol.t
    | Eq_projection of Symbol.t * Symbol.t * Id.t
    | Target_stack of Concrete_stack.t
    | C_and of t * t
    | C_cond_bottom of Id.t * Relative_stack.t * t list
    | Fbody_to_callsite of fc
    | Callsite_to_fbody of cf
  [@@deriving sexp, compare, equal, show { with_path = false }]
end

include T
include Comparator.Make (T)

let mk_cvar_core ~from_id ~to_id ~site rel_stk =
  Fmt.str "%a_%s$%a_to_%a" Relative_stack.pp rel_stk
    (match site with None -> "" | Some s -> Id.show s)
    Id.pp to_id Id.pp from_id

let mk_cvar_cond_core ~site ~beta rel_stk =
  Fmt.str "%a_%a$%B" Relative_stack.pp rel_stk Id.pp site beta

let mk_cvar_complete core = Fmt.str "$%s_cc" core

let mk_cvar_picked core = Fmt.str "$%s_pp" core

let cvars_of_condsite x r_stk =
  List.map [ true; false ] ~f:(fun beta ->
      mk_cvar_cond_core ~site:x ~beta r_stk)

let cvars_of_fc fc =
  List.map fc.outs ~f:(fun out ->
      mk_cvar_core ~from_id:fc.fun_in ~to_id:out.f_out ~site:(Some out.site)
        fc.stk_in)

let cvars_of_cf cf =
  List.map cf.ins ~f:(fun in_ ->
      mk_cvar_core ~from_id:cf.f_out ~to_id:in_.fun_in ~site:(Some cf.site)
        cf.stk_out)

let derive_complete_and_picked cvars =
  (List.map ~f:mk_cvar_complete cvars, List.map ~f:mk_cvar_picked cvars)

let show_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Le -> "<"
  | Leq -> "<="
  | Eq -> "=="
  | And -> "&&"
  | Or -> "||"
  | Xor -> "!="
(* | Not *)

let pp_binop = Fmt.of_to_string show_binop

let rec pp oc t =
  let open Fmt in
  match t with
  | Eq_v (s, v) -> pf oc "@[<v 2>%a == %a@]" Symbol.pp s pp_value v
  | Eq_x (s1, s2) -> pf oc "@[<v 2>%a == %a@]" Symbol.pp s1 Symbol.pp s2
  | Eq_lookup (xs1, stk1, xs2, stk2) ->
      pf oc "@[<v 2>{%a}%a == {%a}%a@]"
        (list ~sep:(any "-> ") Id.pp)
        xs1 Relative_stack.pp stk1
        (list ~sep:(any "-> ") Id.pp)
        xs2 Relative_stack.pp stk2
  | Eq_binop (s1, s2, op, s3) ->
      pf oc "@[<v 2>%a := %a %a %a@]" Symbol.pp s1 Symbol.pp s2 pp_binop op
        Symbol.pp s3
  | Eq_projection (_, _, _) -> ()
  | Target_stack stk -> pf oc "@[<v 2>Top: %a@]" Concrete_stack.pp stk
  | C_and (t1, t2) -> pf oc "@[<v 2>%a@,%a@]" pp t1 pp t2
  | C_cond_bottom (site, _, ts) ->
      pf oc "@[<v 2>Cond_bottom(%a): @,%a@]" Id.pp site (list ~sep:sp pp) ts
  | Fbody_to_callsite fc ->
      pf oc "@[<v 2>Fbody_to_callsite: @,%a@]" (list ~sep:sp pp_fc_out) fc.outs
  | Callsite_to_fbody cf ->
      pf oc "@[<v 2>Callsite_to_fbody: @,%a@]" (list ~sep:sp pp_cf_in) cf.ins

let show = Fmt.to_to_string pp

let to_string c = c |> sexp_of_t |> Sexp.to_string_hum

let list_to_string cs = cs |> [%sexp_of: t list] |> Sexp.to_string_hum

let to_smt_v =
  let open Odefa_ast.Ast in
  function
  | Value_int i -> Int i
  | Value_bool b -> Bool b
  | _ -> failwith "to_smt_v: not supported yet"

let to_smt_op =
  let open Odefa_ast.Ast in
  function
  | Binary_operator_plus -> Add
  | Binary_operator_minus -> Sub
  | Binary_operator_times -> Mul
  | Binary_operator_divide -> Div
  | Binary_operator_modulus -> Mod
  | Binary_operator_less_than -> Le
  | Binary_operator_less_than_or_equal_to -> Leq
  | Binary_operator_equal_to -> Eq
  | Binary_operator_and -> And
  | Binary_operator_or -> Or
  | Binary_operator_xor -> Xor

let bind_v x v stk = Eq_v (Symbol.id x stk, to_smt_v v)

let bind_input x stk = Eq_x (Symbol.id x stk, Symbol.id x stk)

let eq_lookup xs1 stk1 xs2 stk2 = Eq_lookup (xs1, stk1, xs2, stk2)

let bind_binop x y1 op y2 stk =
  Eq_binop (Symbol.id x stk, Symbol.id y1 stk, to_smt_op op, Symbol.id y2 stk)

let bind_fun x stk f = Eq_v (Symbol.id x stk, Fun f)

let and_ c1 c2 = C_and (c1, c2)

let cond_bottom site rel_stack cs = C_cond_bottom (site, rel_stack, cs)

let name_of_lookup xs stk =
  match xs with
  | [ x ] -> Symbol.Id (x, stk) |> Symbol.show
  | _ :: _ ->
      let p1 = Lookup_stack.mk_name xs in
      let p2 = Relative_stack.show stk in
      p1 ^ p2
  | [] -> failwith "name_of_lookup empty"
