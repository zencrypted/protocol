(* syntax/reader.ml -- the single entry point to the surface grammar.

   Both the syntax gate and the runner go through here, so "does it parse"
   has exactly one answer in the tree.  Errors are located: a scenario file
   is read by people diffing it against a protocol text, and "unexpected
   token" without a line number is not a reviewable message.        *)

let locate lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  (p.Lexing.pos_lnum, p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)

let of_lexbuf path lexbuf =
  try Ok (Parser.program Lexer.token lexbuf)
  with
  | Parser.Error ->
      let l, c = locate lexbuf in
      Error
        (Printf.sprintf "%s:%d:%d: unexpected %S" path l c (Lexing.lexeme lexbuf))
  | Lexer.Syntax_error m -> Error (path ^ ": " ^ m)

let parse_file path =
  let ic = open_in path in
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf path;
  let r =
    try of_lexbuf path lexbuf
    with e -> close_in ic; raise e
  in
  close_in ic;
  r

let parse_string ?(name = "(string)") s =
  let lexbuf = Lexing.from_string s in
  Lexing.set_filename lexbuf name;
  of_lexbuf name lexbuf

(* Every .z180 file below a directory, in a deterministic order: the report
   must diff across runs, or it cannot be read as evidence. *)
let rec files dir =
  let ents = Array.to_list (Sys.readdir dir) in
  List.sort String.compare
    (List.concat_map
       (fun e ->
         let p = Filename.concat dir e in
         if Sys.is_directory p then files p
         else if Filename.check_suffix p ".z180" then [ p ]
         else [])
       ents)
