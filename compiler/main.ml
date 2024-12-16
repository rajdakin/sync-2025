open Parser
open Printf
open Arg

let usage_message = "compiler <file>"
let input_file = ref ""
let entry_file file = input_file := file

let parse_file filename =
  let tbool = snd Lustre.var_bool in
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  let name, locals, ret, eqs =
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
  Lustre.
    {
      n_name = name;
      n_in = [];
      n_out = (ret, tbool);
      n_locals = locals;
      n_body = eqs;
    }

let () =
  Arg.parse [] entry_file usage_message;

  let node = parse_file !input_file in

  match LustreOrdering.translate_node node with
  | Ok m -> Generation.pp_coq_method (LustreOrderedToImp.translate_node m)
  | Err x -> Printf.printf "Error lustre ordering translate: %s\n" x
