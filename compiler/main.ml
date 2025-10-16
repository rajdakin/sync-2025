open Extracted
open Format

let usage_message = Sys.argv.(0) ^ " <file>"
let input_file = ref ""
let entry_file file = input_file := file

let parse_file filename =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  
  let module MI = Parser.MenhirInterpreter in
  let checkpoint = Parser.Incremental.node lexbuf.lex_curr_p
  and supplier = MI.lexer_lexbuf_to_supplier Lexer.token lexbuf
  and succeed (name, args, locals, ret, eqs) =
    close_in inx;
    LustreAst.
      {
        n_name = name;
        n_in = args;
        n_out = ret;
        n_locals = locals;
        n_body =
          Stdlib.List.map (fun ((id, _) as arg) -> (id, EInput arg)) args @ eqs;
      }
  and fail checkpoint =
    close_in inx;
    (* let position = lexbuf.lex_start_p in *)
    try
      let error_msg =
        match checkpoint with
        | MI.HandlingError env -> env |> MI.current_state_number |> ParserMessages.message
        | _ -> assert false (* This should not happen. *)
      in
      (* Format.printf "%a: %s" pp_position (position_of_lexerpos position) error_msg; *)
      Format.printf "parser error: %s" error_msg;
      exit 1
    with Not_found ->
      (* Format.printf "%a: <unknown error message>" pp_position (position_of_lexerpos position); *)
      Format.printf "parser error: <unknown error message>";
      exit 1
  in
  try
    MI.loop_handle succeed fail supplier checkpoint
  with Lexer.Error msg ->
    close_in inx;
    eprintf "lexer error: %s" msg;
    exit 1
  | e ->
    Format.printf "%s@\n" (Printexc.to_string e);
    exit 1

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
