(* open Core *)
open Shexp_process
open Shexp_process.Infix
(* open Shexp_process.Logged *)

let testcases = [
  "input_eta.natodefa";
  "input_k_cfa_2.natodefa";
  "input_k_cfa_3.natodefa";
  "input_map.natodefa";
  "input_mj09.natodefa";
  (* "input_facehugger.natodefa"; *)
]

let repeat_n = 3

let working_path = "result/working/"


let make_result_file () = 
  (run "date" ["-u"; "+%Y-%m-%d-%H:%M:%SZ"])
  |- (run "xargs" ["-I"; "%"; "mkdir"; "-p";"result/%"])

let prepare : unit t = 

  run "rm" ["-rf"; working_path] >>
  run "mkdir" ["-p"; working_path]
(* make_result_file () *)

let benchmark test n : unit t = 
  (* let test = "input_map.natodefa" in *)
  let test_path = "benchmark-test-generation/cases/" ^ test
  and test_result = working_path ^ (test ^ "_" ^ (string_of_int n)) ^ ".txt" 
  and test_time_result = working_path ^ (test ^ "_" ^ (string_of_int n)) ^ ".time.txt" in
  print test
  (* time gtimeout --foreground 1m ls *)
  >> stdout_to ~append:() test_result (call [
      "/usr/bin/time"; "-o"; test_time_result;
      "/usr/bin/timeout"; "--foreground"; "1m" ;"./test_generator"; "-t"; "target"; "-r"; "1"; "-b"; "true"; test_path])
  >> echo @@ " done - " ^ (string_of_int n)
(* |- run "tee" ["-a"; result_file] *)

let collect_result : unit t =
  (run "date" ["-u"; "+%Y-%m-%d-%H:%M:%SZ"])
  |- (run "xargs" ["-I"; "%"; "mv"; working_path;"result/evaluate-%"])

let rec countdown n task : unit t =
  if n > 0 then
    task n
    >> countdown (n-1) task
  else
    echo "done"

let main  =
  ignore @@ 
  eval (
    prepare
    >> List.iter testcases ~f:(fun task -> countdown repeat_n (benchmark task))
    >> collect_result)

