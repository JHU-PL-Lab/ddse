(* open Core *)
open Shexp_process
open Shexp_process.Infix
(* open Shexp_process.Logged *)

let testcases = [
  "input_map.natodefa"
]

let repeat_n = 1

let working_path = "result/working/"


let make_result_file () = 
  (run "date" ["-u"; "+%Y-%m-%d-%H:%M:%SZ"])
  |- (run "xargs" ["-I"; "%"; "mkdir"; "-p";"result/%"])

(* result_path ^ "/result.txt" *)

let prepare : unit t = 

  run "rm" ["-rf"; working_path] >>
  run "mkdir" ["-p"; working_path]
(* make_result_file () *)

let benchmark n : unit t = 
  let test = "input_map.natodefa" in
  let test_path = "test-sources/" ^ test
  and test_result = working_path ^ (test ^ "_" ^ (string_of_int n)) ^ ".txt" in
  print test
  (* time gtimeout --foreground 1m ls *)
  >> outputs_to ~append:() test_result (call ["time"; "gtimeout"; "--foreground"; "1m" ;"./test_generator"; "-t"; "target"; test_path])
  >> echo @@ "done - " ^ (string_of_int n)
(* |- run "tee" ["-a"; result_file] *)

let collect_result : unit t =
  (run "date" ["-u"; "+%Y-%m-%d-%H:%M:%SZ"])
  |- (run "xargs" ["-I"; "%"; "mv"; working_path;"result/evaluate-%"])

let countdown n task : unit t =
  if n > 0 then
    task n
  else
    echo "done"

let main  =
  ignore @@ 
  eval (
    prepare
    >> (countdown repeat_n benchmark)
    >> collect_result)

