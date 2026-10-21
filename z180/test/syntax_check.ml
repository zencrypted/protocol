(* Syntax gate for the Z.180 surface grammar.

   It answers exactly one question, and answers it loudly: does every
   scenario in ../scenarios parse?  It does not execute anything, so it
   stays green while the elaborator and kernel are being built, and it
   turns red the moment the grammar stops covering the corpus. *)

open Z180_syntax
open Ast

let die fmt = Printf.ksprintf (fun s -> prerr_endline s; exit 1) fmt

let parse_file path =
  let ic = open_in path in
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf path;
  let result =
    try Ok (Parser.program Lexer.token lexbuf)
    with
    | Parser.Error ->
        let p = Lexing.lexeme_start_p lexbuf in
        Error
          (Printf.sprintf "%s:%d:%d: unexpected %S" path p.Lexing.pos_lnum
             (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)
             (Lexing.lexeme lexbuf))
    | Lexer.Syntax_error m -> Error (path ^ ": " ^ m)
  in
  close_in ic;
  result

let rec list_files dir =
  let ents = Array.to_list (Sys.readdir dir) in
  List.concat_map
    (fun e ->
      let p = Filename.concat dir e in
      if Sys.is_directory p then list_files p
      else if Filename.check_suffix p ".z180" then [ p ]
      else [])
    ents

let stmt_count (sc : scenario) = List.length sc.Ast.stmts

let () =
  let root = (if Sys.file_exists "../scenarios" then "../scenarios"
              else "scenarios") in
  let files = List.sort String.compare (list_files root) in
  if files = [] then die "no .z180 scenarios found under %s" root;
  let total_scn = ref 0 and total_stmt = ref 0 in
  List.iter
    (fun f ->
      match parse_file f with
      | Error m -> die "PARSE FAILED %s" m
      | Ok scs ->
          let n = List.fold_left (fun a s -> a + stmt_count s) 0 scs in
          total_scn := !total_scn + List.length scs;
          total_stmt := !total_stmt + n;
          Printf.printf "%-34s %2d scenarios %4d stmts\n" f
            (List.length scs) n)
    files;
  Printf.printf "parsed %d scenarios, %d statements, 0 errors\n"
    !total_scn !total_stmt
