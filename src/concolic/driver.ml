open Core

module CLog = Dj_common.Log.Export.CLog

module Test_result =
  struct
    type t =
      | Found_abort of Branch.t * Jil_input.t list (* Found an abort at this branch using these inputs *)
      | Type_mismatch of Jayil.Ast.Ident_new.t * Jil_input.t list (* Proposed addition for removing instrumentation *)
      | Exhausted               (* Ran all possible tree paths, and no paths were too deep *)
      | Exhausted_pruned_tree   (* Ran all possible tree paths up to the given max step *)
      | Timeout                 (* total evaluation timeout *)

    let to_string = function
    | Found_abort _ ->         "FOUND_ABORT"
    | Type_mismatch _ ->       "TYPE_MISMATCH"
    | Exhausted ->             "EXHAUSTED"
    | Exhausted_pruned_tree -> "EXHAUSTED_PRUNED_TREE"
    | Timeout ->               "TIMEOUT"

    let merge a b =
      match a, b with
      (* When abort and type mismatch are found, we can conclusively end *)
      | (Found_abort _ as x), _ | _, (Found_abort _ as x)
      | (Type_mismatch _ as x), _ | _, (Type_mismatch _ as x) -> x
      (* Similarly, if we exhausted a tree, then we tried literally everything, so can end *)
      | Exhausted,_  | _, Exhausted -> Exhausted
      (* For the following results, we want to keep the one with the least information to be conservative *)
      | Timeout, _ | _, Timeout -> Timeout
      | Exhausted_pruned_tree, Exhausted_pruned_tree -> Exhausted_pruned_tree

    let of_session_status = function
      | Session.Status.Found_abort (branch, inputs) -> Found_abort (branch, inputs)
      | Type_mismatch inputs -> Type_mismatch (Ident "placeholder branch name", inputs)
      | Exhausted { pruned = true } -> Exhausted_pruned_tree
      | Exhausted { pruned = false } -> Exhausted
      | In_progress _ -> failwith "session status unfinished"

  end

(*
  ----------------------
  TESTING BY EXPRESSIONS
  ----------------------
*)

let[@landmark] lwt_test_one : (Jayil.Ast.expr -> Test_result.t Lwt.t) Options.Fun.t =
  let open Lwt.Infix in
  Options.Fun.make
  @@ fun (r : Options.t) ->
      fun (e : Jayil.Ast.expr) ->
        let t0 = Caml_unix.gettimeofday () in
        Options.Fun.appl Evaluator.lwt_eval r e
        >|= function res_status ->
          CLog.app (fun m -> m "\nFinished concolic evaluation in %fs.\n" (Caml_unix.gettimeofday () -. t0));
          Test_result.of_session_status res_status

(* runs [lwt_test_one] and catches lwt timeout *)
let test_with_timeout : (Jayil.Ast.expr -> Test_result.t) Options.Fun.t =
  Options.Fun.make
  @@ fun (r : Options.t) ->
      fun (e : Jayil.Ast.expr) ->
        try
          Lwt_main.run
          @@ Options.Fun.appl lwt_test_one r e
        with
        | Lwt_unix.Timeout ->
          CLog.app (fun m -> m "Quit due to total run timeout in %0.3f seconds.\n" r.global_timeout_sec);
          Test_result.Timeout

let[@landmark] test_expr ?(print_result=true) : (Jayil.Ast.expr -> Test_result.t) Options.Fun.t =
  let f r =
    if print_result then Format.printf "\n%s\n" (Test_result.to_string r);
    r
  in
  Options.Fun.map test_with_timeout f

(*
  -------------------
  TESTING BY FILENAME
  -------------------
*)

let test_jil : (string -> Test_result.t) Options.Fun.t =
  let open Options.Fun in
  test_expr ~print_result:true
  @. Dj_common.File_utils.read_source

let test_bjy : (string -> Test_result.t) Options.Fun.t =
  let open Options.Fun in
  test_expr ~print_result:true
  @. (fun filename ->
    filename
    |> Dj_common.File_utils.read_source_full ~do_instrument:true ~do_wrap:true
    |> Dj_common.Convert.jil_ast_of_convert)

let test : (string -> Test_result.t) Options.Fun.t =
  Options.Fun.make
  @@ fun r ->
      fun filename ->
      match Core.Filename.split_extension filename with
      | _, Some "jil" -> Options.Fun.appl test_jil r filename
      | _, Some "bjy" -> Options.Fun.appl test_bjy r filename
      | _ -> failwith "expected jil or bjy file"