open Extracted
open Printf

let usage_message = "compiler <file>"
let input_file = ref ""
let entry_file file = input_file := file

let parse_file filename =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  let name, args, locals, ret, eqs =
    match Parser.node Lexer.token lexbuf with
    | v -> v
    | exception Lexer.Error msg ->
        eprintf "lexer error: %s" msg;
        exit 1
    | exception Lexer.Eof ->
        eprintf "end of file";
        exit 1
  in
  close_in inx;
  LustreAst.
    {
      n_name = name;
      n_in = args;
      n_out = ret;
      n_locals = locals;
      n_body = List.map (fun ((id, _) as arg) -> (id, EInput arg)) args @ eqs;
    }

let () =
  Arg.parse [] entry_file usage_message;

  let node = parse_file !input_file in

  let checked_node =
    match LustreAstToLustre.check_node_prop node with
    | Ok m -> m
    | Err x ->
        printf "Error when node properties have been checked: %s\n" x;
        exit 1
  in

  match LustreOrdering.translate_node checked_node with
  | Ok m -> Generation.pp_coq_method (LustreOrderedToImp.translate_node m)
  | Err x -> printf "Error lustre ordering translate: %s\n" x
