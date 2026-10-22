(* bin/z180.ml -- the Z.180 scenario runner.

   parse -> elaborate -> run -> verdicts.  The exit code is the gate: 0 only
   when every scenario parsed, elaborated, and produced no FAIL and asserted
   something.  A scenario that asserts nothing is reported NOASSERT and is not
   a pass; that is the failure mode the superseded Python oracle actually had. *)

open Z180_model

let usage () =
  prerr_endline "usage: z180 [-v] [dir]    run the scenario corpus (default: scenarios)";
  exit 2

let args argv =
  let verbose = ref false in
  let dir = ref (if Sys.file_exists "scenarios" then "scenarios" else "../scenarios") in
  Array.iteri
    (fun i a ->
      match i, a with
      | 0, _ -> ()
      | _, ("-v" | "--verbose") -> verbose := true
      | _, ("-h" | "--help") -> usage ()
      | _, s -> dir := s)
    argv;
  (!verbose, !dir)

let scenario_file path =
  match Z180_syntax.Reader.parse_file path with
  | Error m -> [ `Parse (path, m) ]
  | Ok scs ->
      List.map
        (fun (sc : Z180_syntax.Ast.scenario) ->
          match Elaborator.names sc with
          | Error m -> `Elab (sc.name, m)
          | Ok (kss, names) -> `Run (Runner.run ~names sc.name kss))
        scs

let () =
  let verbose, dir = args Sys.argv in
  if not (Sys.file_exists dir) then (
    prerr_endline ("no such directory: " ^ dir);
    exit 2);
  let files = Z180_syntax.Reader.files dir in
  if files = [] then (
    prerr_endline ("no .z180 scenarios under " ^ dir);
    exit 1);
  let t = ref (0, 0, 0, 0, 0, 0) in
  (* scn, asserted, pass, fail, skip, bad-scenarios *)
  let add (a, b, c, d, e, f) (g, h, i, j, k, l) =
    (a + g, b + h, c + i, d + j, e + k, f + l)
  in
  List.iter
    (fun path ->
      Printf.printf "%s\n" path;
      List.iter
        (function
          | `Parse (_, m) ->
              Printf.printf "  PARSE ERROR %s\n" m;
              t := add !t (0, 0, 0, 0, 0, 1)
          | `Elab (n, m) ->
              Printf.printf "  ELABORATE ERROR %-30s %s\n" n m;
              t := add !t (0, 0, 0, 0, 0, 1)
          | `Run r ->
              let open Runner in
              if verbose then print_string (detail r);
              let bad = if r.failed > 0 || r.asserted = 0 then 1 else 0 in
              if bad = 1 then List.iter
                (fun (idx, src, msg) ->
                  Printf.printf "      %3d  %s\n           FAIL %s\n" idx src msg)
                (failures r);
              Printf.printf "  %-6s %s\n" (tag r) (summary r);
              t := add !t (1, r.asserted, r.passed, r.failed, r.skipped, bad))
        (scenario_file path))
    files;
  let scn, asserted, pass, fail, skip, bad = !t in
  Printf.printf "\n%d scenarios   asserted %d   pass %d  fail %d  skip %d   files %d\n"
    scn asserted pass fail skip (List.length files);
  Printf.printf "%s\n"
    (if bad = 0 then "GREEN: every scenario parsed, elaborated, asserted and held"
     else Printf.sprintf "RED: %d scenario(s) failed, asserted nothing, or did not elaborate" bad);
  exit (if bad = 0 then 0 else 1)
