#!/usr/bin/env ocaml
;;
#use "topfind";;
#warnings "+a";;
#thread
(* #require "ppx_jane,core" *)
#require "shexp.process"
module List' = List
open Shexp_process
open Shexp_process.Infix

let ss = Printf.sprintf

let result_file = "bench/result.txt"

let test stack i : unit t =
  with_temp_file ~prefix:"test" ~suffix:".natodefa" 
    (fun t -> 
       echo @@ ss "\n[%s - %s - %d]" "input_loop.natodefa" stack i
       >> stdout_to t
       @@ run "m4" ["-D_LOOP_COUNT_=" ^ (string_of_int i); "bench/input_loop.natodefa.m4"]
       >> run "./test_generator" ["-e"; stack; "-m"; "100000"; "-t"; "target"; t]
       |- run "tee" ["-a"; result_file]
    )

(* run "./test_generator" ["-m"; "100000"; "-t"; "target"; "bench/input_loop.natodefa"]  *)

let main : unit t =
  rm result_file;

  List.iter ["bfs"; "relstack"]
    ~f:(fun stack -> 
        List.iter [0;1;2]
          ~f:(fun i ->
              test stack i))

let () =
  eval main