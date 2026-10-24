
let make_one fname =
  (* parse once *)
  let source =
    Dj_common.File_utils.read_source_full fname ~do_wrap:true ~do_instrument:true
  in
  let run source =
    match
      (* translate as part of the benchmark *)
      let pgm = Dj_common.Convert.jil_ast_of_convert source in
      Concolic.Driver.test_expr pgm
        ~global_timeout_sec:90.0 ~random:true ~print_result:false
    with
    | Found_abort _ | Type_mismatch _ -> ()
    | _ -> assert false (* we are only benchmarking erroring programs here! *)
  in
  (Filename.basename fname, run, source)

let bench_throughput ~sec tests =
  Benchmark.throughputN sec tests

let bench_trials ~trials tests =
  Benchmark.latencyN (Int64.of_int trials) tests

let ls_dir dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.map (Filename.concat dir)
  |> List.sort String.compare

let is_bluejay_file fname = Filename.check_suffix fname "bjy"

let find_bluejay_files ~(recpaths : bool) (init : string list) : string list =
  if not recpaths then
    List.concat_map (fun fname ->
      if Sys.is_directory fname then
        List.filter is_bluejay_file (ls_dir fname)
      else if is_bluejay_file fname then
        [ fname ]
      else
        []
    ) init
  else
    let rec go = function
      | [] -> []
      | dir :: worklist when Sys.is_directory dir ->
        go (ls_dir dir @ worklist)
      | fname :: worklist when is_bluejay_file fname ->
        fname :: go worklist
      | _ :: worklist ->
        go worklist
    in
    go init

let bench_main =
  Cmdliner.Cmd.v (Cmdliner.Cmd.info "bench") @@
  let open Cmdliner.Term.Syntax in
  let+ paths = Cmdliner.Arg.(
      non_empty & pos_all file [] &
      info [] ~docv:"PATH" ~doc:"Input files or directories"
    )
  and+ recpaths = Cmdliner.Arg.(
      value & flag &
      info ["recpaths"] ~doc:"Recursively search directories for files"
    )
  and+ sec = Cmdliner.Arg.(
      value & opt int 10
      & info ["sec"] ~docv:"SECONDS"
      ~doc:"Minumum benchmarking time, in seconds. Ignored if trials are given"
    )
  and+ trials = Cmdliner.Arg.(
      value & opt (some int) None
      & info ["trials"] ~docv:"TRIALS" ~doc:"Number of trials"
    )
  in
  let tests = find_bluejay_files ~recpaths paths |> List.map make_one in
  let _res =
    match trials with
    | Some n -> bench_trials ~trials:n tests
    | None -> bench_throughput ~sec tests
  in
  ()

let () =
  match Cmdliner.Cmd.eval_value' bench_main with
  | `Ok _ -> ()
  | `Exit i -> exit i
