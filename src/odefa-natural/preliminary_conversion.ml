open Batteries;;
(* open Jhupllib; *)

open On_ast;;

(* This function encodes all list-related patterns with record patterns *)
let rec encode_list_pattern (pat : pattern) : pattern =
  match pat with
  | AnyPat | IntPat | TruePat | FalsePat | FunPat | StringPat | VarPat _ ->
    pat
  | RecPat (rec_map) ->
    RecPat (Ident_map.map (fun pat -> encode_list_pattern pat) rec_map)
  | VariantPat v_content ->
    let Variant (v_label, v_pat) = v_content in
    let new_v_content = Variant (v_label, encode_list_pattern v_pat) in
    VariantPat new_v_content
  | EmptyLstPat ->
    (* The empty list is encoded as {~empty = {}} *)
    let empty_rec =
      Ident_map.add (Ident "~empty") (RecPat (Ident_map.empty)) Ident_map.empty
    in
    RecPat (empty_rec)
  | LstDestructPat (hd_pat, tl_pat) ->
    let clean_hd_pat = encode_list_pattern hd_pat in
    let clean_tl_pat = encode_list_pattern tl_pat in
    let pat_rec_with_head =
      Ident_map.add (Ident "~head") (clean_hd_pat) (Ident_map.empty)
    in
    let pat_rec_with_tail =
      Ident_map.add (Ident "~tail") (clean_tl_pat) (pat_rec_with_head)
    in
    RecPat (pat_rec_with_tail)
;;

(* This function transforms all lists in the expression to records. *)
let rec list_transform (e : expr) : (expr) =
  match e with
  | Var _ | Int _ | Bool _ | Input -> e
  | Function (param_list, e') ->
    let new_e' = list_transform e' in
    Function (param_list, new_e')
  | Appl (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Appl (new_e1, new_e2)
  | Let (id, e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Let (id, new_e1, new_e2)
  | LetRecFun _ ->
    raise @@
    Failure "encode_variant: LetRecFun should have been desugared by now"
  | LetFun (f_sig, outer_e) ->
    let Funsig(f_name, param_list, inner_e) = f_sig in
    let new_inner_e = list_transform inner_e in
    let new_outer_e = list_transform outer_e in
    let new_funsig = Funsig(f_name, param_list, new_inner_e) in
    LetFun(new_funsig, new_outer_e)
  | Plus (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Plus (new_e1, new_e2)
  | Minus (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Minus (new_e1, new_e2)
  | Times (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Times (new_e1, new_e2)
  | Divide (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Divide (new_e1, new_e2)
  | Modulus (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Modulus (new_e1, new_e2)
  | Equal (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Equal (new_e1, new_e2)
  | LessThan (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    LessThan (new_e1, new_e2)
  | Leq (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Leq (new_e1, new_e2)
  | And (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    And (new_e1, new_e2)
  | Or (e1, e2) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    Or (new_e1, new_e2)
  | Not (e') ->
    let new_e' = list_transform e' in
    Not (new_e')
  | If (e1, e2, e3) ->
    let new_e1 = list_transform e1 in
    let new_e2 = list_transform e2 in
    let new_e3 = list_transform e3 in
    If (new_e1, new_e2, new_e3)
  | Record fields ->
    Record (Ident_map.map (fun e -> list_transform e) fields)
  | RecordProj (e, lab) ->
    RecordProj (list_transform e, lab)
;;

(* Sub-routine that replaces all of the vars that are in the map. *)
(* NOTE: Please don't ask why we wrote this. *)
(* let rec var_replacer
    (e : expr)
    (p_map : expr Ident_map.t)
   : expr =
   match e with
   | Var (id) ->
    (* HERE IS THE BASE CASE *)
    if (Ident_map.mem id p_map) then
      Ident_map.find id p_map
    else e
   | Function (id_list, e') ->
    let replaced_e' = var_replacer e' p_map in
    Function (id_list, replaced_e')
   | Appl (e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    Appl (replaced_e1, replaced_e2)
   | Let (id, e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    Let (id, replaced_e1, replaced_e2)
   | LetRecFun (_) ->
    raise @@ Failure "LetRecFun should have been desugared by now"
   | LetFun (f_sig, outer_expr) ->
    let Funsig(name, param_list, f_expr) = f_sig in
    let replaced_f_expr = var_replacer f_expr p_map in
    let replaced_outer_expr = var_replacer outer_expr p_map in
    LetFun(Funsig(name, param_list, replaced_f_expr), replaced_outer_expr)
   | Plus (e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    Plus (replaced_e1, replaced_e2)
   | Minus (e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    Minus (replaced_e1, replaced_e2)
   | Equal (e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    Equal (replaced_e1, replaced_e2)
   | LessThan (e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    LessThan (replaced_e1, replaced_e2)
   | Leq (e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    Leq (replaced_e1, replaced_e2)
   | And (e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    And (replaced_e1, replaced_e2)
   | Or (e1, e2) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    Or (replaced_e1, replaced_e2)
   | Not (e') ->
    let replaced_e' = var_replacer e' p_map in
    Not (replaced_e')
   | If (e1, e2, e3) ->
    let replaced_e1 = var_replacer e1 p_map in
    let replaced_e2 = var_replacer e2 p_map in
    let replaced_e3 = var_replacer e3 p_map in
    If (replaced_e1, replaced_e2, replaced_e3)
   | Record (recmap) ->
    let new_recmap = Ident_map.map (fun expr ->
        var_replacer expr p_map) recmap
    in
    Record (new_recmap)
   | RecordProj (e', lab) ->
    let replaced_e' = var_replacer e' p_map in
    RecordProj(replaced_e', lab)
   | Match (e1, p_e_list) ->
    let replaced_e1 = var_replacer e1 p_map in
    let new_p_e_list =
      List.map (fun curr_p_e_pair ->
          let (curr_pat, curr_expr) = curr_p_e_pair in
          let new_expr = var_replacer curr_expr p_map in
          (curr_pat, new_expr)
        ) p_e_list
    in
    Match (replaced_e1, new_p_e_list)
   | Int _ | Bool _ | String _ -> e
   ;; *)
