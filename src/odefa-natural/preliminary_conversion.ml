open Batteries;;
(* open Jhupllib; *)

open On_ast;;
open Translator_utils;;

open TranslationMonad;;

let _lbl_m name =
  let%bind freshness = freshness_string in
  return @@ Ident (freshness ^ name)
;;

let lbl_empty_m : Ident.t m = _lbl_m "empty";;
let lbl_head_m : Ident.t m = _lbl_m "head";;
let lbl_tail_m : Ident.t m = _lbl_m "tail";;
let lbl_variant_m (s : string) : Ident.t m = _lbl_m ("variant_" ^ s);;
let lbl_value_m : Ident.t m = _lbl_m "value";;

(* This function encodes all list-related patterns with record patterns *)
let rec encode_list_pattern (pat : pattern) : pattern m =
  match pat with
  | AnyPat | IntPat | TruePat | FalsePat | FunPat | VarPat _ ->
    return pat
  | RecPat (rec_map) ->
    let%bind rec_map' =
      rec_map
      |> ident_map_map_m
        (fun pat -> encode_list_pattern pat)
    in
    return @@ RecPat rec_map'
  | VariantPat(Variant(v_label, v_pat)) ->
    let%bind v_pat' = encode_list_pattern v_pat in
    return @@ VariantPat(Variant(v_label, v_pat'))
  | EmptyLstPat ->
    (* The empty list is encoded as {~empty = {}} *)
    let%bind lbl_empty = lbl_empty_m in
    let empty_rec =
      Ident_map.add lbl_empty (RecPat (Ident_map.empty)) Ident_map.empty
    in
    return @@ RecPat(empty_rec)
  | LstDestructPat (hd_pat, tl_pat) ->
    let%bind clean_hd_pat = encode_list_pattern hd_pat in
    let%bind clean_tl_pat = encode_list_pattern tl_pat in
    let%bind lbl_head = lbl_head_m in
    let%bind lbl_tail = lbl_tail_m in
    let pat_rec_with_head =
      Ident_map.add lbl_head (clean_hd_pat) (Ident_map.empty)
    in
    let pat_rec_with_tail =
      Ident_map.add lbl_tail (clean_tl_pat) (pat_rec_with_head)
    in
    return @@ RecPat (pat_rec_with_tail)
;;

(* This function transforms all lists in the expression to records. *)
let list_transform (e : expr) : expr m =
  let%bind lbl_empty = lbl_empty_m in
  let%bind lbl_head = lbl_head_m in
  let%bind lbl_tail = lbl_tail_m in
  let transformer recurse expr =
    match expr with
    | List (expr_list) ->
      let list_maker = fun element -> fun acc ->
        let%bind clean_elm = recurse element in
        let new_map =
          Ident_map.empty
          |> Ident_map.add lbl_head clean_elm
          |> Ident_map.add lbl_tail acc
        in
        return @@ Record new_map
      in
      let empty_rec =
        Record (Ident_map.add
                  lbl_empty (Record (Ident_map.empty)) Ident_map.empty)
      in
      let%bind record_equivalent =
        list_fold_right_m list_maker expr_list empty_rec
      in
      return record_equivalent
    | Match (match_e, pat_expr_list) ->
      let%bind new_match_e = recurse match_e in
      (* routine to pass into List.map... *)
      let pat_expr_list_changer pat_expr_tuple =
        let (curr_pat, curr_expr) = pat_expr_tuple in
        let%bind new_pat = encode_list_pattern curr_pat in
        let%bind new_expr = recurse curr_expr in
        return (new_pat, new_expr)
      in
      let%bind new_pat_expr_list =
        sequence @@ List.map pat_expr_list_changer pat_expr_list
      in
      return @@ Match(new_match_e, new_pat_expr_list)
    | _ ->
      return expr
  in
  m_transform_expr transformer e
;;

(* This function takes a Variant expression and converts it into a
   Record expression. *)
let variant_expr_to_record recurse (v_label : variant_label) (v_expr : expr)
  : expr m =
  let Variant_label v_name = v_label in
  let%bind variant_ident = lbl_variant_m v_name in
  let empty_rec = Record (Ident_map.empty) in
  let map_with_label =
    Ident_map.add variant_ident empty_rec Ident_map.empty
  in
  let%bind encoded_v_expr = recurse v_expr in
  let%bind lbl_value = lbl_value_m in
  let res_map = Ident_map.add lbl_value encoded_v_expr map_with_label in
  let res_record = Record (res_map) in
  return res_record
;;

(* This function takes a Variant pattern and converts it into a
   Record pattern. *)
let rec variant_pattern_to_record ((Variant(v_label, pat)) : variant_content)
  : pattern m =
  let Variant_label (v_name) = v_label in
  let%bind variant_ident = lbl_variant_m v_name in
  let empty_rec = RecPat (Ident_map.empty) in
  let map_with_label =
    Ident_map.add variant_ident empty_rec Ident_map.empty
  in
  let%bind encoded_v_expr = encode_variant_pattern pat in
  let%bind lbl_value = lbl_value_m in
  let res_map =
    Ident_map.add lbl_value encoded_v_expr map_with_label
  in
  let res_record = RecPat (res_map) in
  return res_record

(* Function that takes a pattern and converts all of the Variant patterns
   within it to Record patterns. *)
and encode_variant_pattern (p : pattern) : pattern m =
  match p with
  | AnyPat | IntPat | TruePat | FalsePat | FunPat | VarPat _ ->
    return p
  | RecPat (rec_map) ->
    let%bind rec_map' = ident_map_map_m encode_variant_pattern rec_map in
    return @@ RecPat rec_map'
  | VariantPat content ->
    variant_pattern_to_record content
  | EmptyLstPat | LstDestructPat _ ->
    raise @@ Failure "encode_variant: list patterns should be transformed by now"
;;

(* Overall Function that takes an expression and converts all of the Variant
   expressions and patterns within it to Record expressions and patterns. *)
let encode_variant (e : expr) : expr m =
  let transformer recurse e =
    match e with
    | VariantExpr (lbl, e') ->
      variant_expr_to_record recurse lbl e'
    | Match (match_e, pat_expr_list) ->
      let%bind new_match_e = recurse match_e in
      (* routine to pass into List.map to edit all of the pattern/expression
         tuples. *)
      let pat_expr_list_changer pat_expr_tuple =
        let (curr_pat, curr_expr) = pat_expr_tuple in
        let%bind new_pat = encode_variant_pattern curr_pat in
        let%bind new_expr = recurse curr_expr in
        return (new_pat, new_expr)
      in
      let%bind new_pat_expr_list =
        sequence @@ List.map pat_expr_list_changer pat_expr_list
      in
      return @@ Match (new_match_e, new_pat_expr_list)
    | _ ->
      return e
  in
  m_transform_expr transformer e
;;

(* Function that calculates and stores information about how to reach a certain
   variable pattern, and reconstructs the pattern to replace variable patterns
   with "any" patterns.

   Parameters:
    proj_subj: The expression needed to reach the current pattern
               (from a certain record that is in the bottommost layer of the
                expression.)
   pat:        The current pattern

   Return value:
   (pattern * ((ident * expr) list)) :
      The first portion of the tuple is the newly constructed pattern without
      variable patterns.
      The second portion of the tuple contains a tuple dictating a certain
      variable pattern, and the expression needed to access the variable
      (the expression will be used as a stand-in for the variable later.)
*)
let rec encode_var_pat
    (proj_subj : expr)
    (pat : pattern)
  : (pattern * ((ident * expr) list))
  =
  match pat with
  | AnyPat | IntPat | TruePat | FalsePat | FunPat ->
    (pat, [])
  | RecPat (pat_map) ->
    (* This routine accumulates the new map (that does not have any variable
       patterns), and the return list. *)
    let (res_pat_map, res_path_list) = Ident_map.fold
        (fun key -> fun pat -> fun acc ->
           let (old_pat_map, old_path_list) = acc in
           let (Ident key_str) = key in
           let cur_label = Label key_str in
           let (new_pat, res_list) = (encode_var_pat (RecordProj(proj_subj, cur_label)) pat)
           in
           let new_pat_map = Ident_map.add key new_pat old_pat_map in
           (new_pat_map, old_path_list @ res_list)
        ) pat_map (Ident_map.empty, [])
    in (RecPat(res_pat_map), res_path_list)
  | VariantPat (_) ->
    raise
    @@ Failure "encode_var_pat : Variant pattern should have been desugared"
  | VarPat (id) ->
    (AnyPat, [(id, proj_subj)])
  | EmptyLstPat | LstDestructPat _ ->
    raise @@ Failure "encode_var_pat: List patterns should have been transformed"
;;

(* Function that finds match statements and go into the patterns to replace
   any variable pattern.
*)
let eliminate_var_pat (e : expr) : expr m =
  let transformer recurse e =
    match e with
    | Match (subject, pat_expr_list) ->
      let%bind new_subj_name = fresh_name "match_subject" in
      let new_subj = Var(Ident new_subj_name) in
      let%bind clean_subject = recurse subject in
      (* routine to pass into List.map with the pat_expr_list *)
      let pat_expr_var_changer curr =
        let (curr_pat, curr_expr) = curr in
        (* NOTE: here we clean out the inner expression before we
           erase variable patterns. *)
        let%bind half_clean_expr = recurse curr_expr in
        let (res_pat, path_list) = encode_var_pat new_subj curr_pat in
        let path_enum = List.enum path_list in
        let path_map = Ident_map.of_enum path_enum in
        let new_expr =
          Ident_map.fold (fun curr_id -> fun curr_path ->
              fun acc_e -> Let (curr_id, curr_path, acc_e) )
            path_map half_clean_expr
        in
        return (res_pat, new_expr)
      in
      let%bind new_path_expr_list =
        sequence @@ List.map pat_expr_var_changer pat_expr_list
      in
      let let_e2 = Match(new_subj, new_path_expr_list) in
      return @@ Let(Ident new_subj_name, clean_subject, let_e2)
    | VariantExpr (_, _) ->
      raise @@ Failure
        "eliminate_var_pat: VariantExpr expressions should have been desugared."
    | List _ | ListCons _ ->
      raise @@ Failure
        "eliminate_var_pat: List expressions should have been handled!"
    | _ -> return e
  in
  m_transform_expr transformer e
;;
