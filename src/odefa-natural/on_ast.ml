open Batteries;;
open Jhupllib;;

type label = Label of string

type ident = Ident of string [@@deriving eq, ord, show, to_yojson];;

module Ident =
struct
  type t = ident;;
  let equal = equal_ident;;
  let compare = compare_ident;;
  let pp = pp_ident;;
  let show = show_ident;;
  let to_yojson = ident_to_yojson;;
  let hash = Hashtbl.hash
end;;

module Ident_map = struct
  module M = Map.Make(Ident);;
  include M;;
  include Pp_utils.Map_pp(M)(Ident);;
  include Yojson_utils.Map_to_yojson(M)(Ident);;
end;;

type variant_label = Variant_label of string

type funsig = Funsig of ident * ident list * expr

and variant_content = Variant of variant_label * pattern

and pattern = AnyPat | IntPat | TruePat | FalsePat | RecPat of pattern Ident_map.t
            | VariantPat of variant_content | VarPat of ident
            | FunPat | StringPat | EmptyLstPat | LstDestructPat of pattern * pattern

and expr =
  | Var of ident | Function of ident list * expr | Appl of expr * expr
  | Let of ident * expr * expr | LetRecFun of funsig list * expr
  | LetFun of funsig * expr
  | Plus of expr * expr | Minus of expr * expr | Times of expr * expr
  | Divide of expr * expr | Modulus of expr * expr
  | Equal of expr * expr | LessThan of expr * expr | Leq of expr * expr
  | And of expr * expr| Or of expr * expr | Not of expr
  | If of expr * expr * expr | Int of int | Bool of bool
  | Record of expr Ident_map.t | RecordProj of expr * label
  | Input
