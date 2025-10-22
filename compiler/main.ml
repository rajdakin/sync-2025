open Extracted
open Format

let usage_message = Sys.argv.(0) ^ " <file>"
let input_file = ref ""
let entry_file file = input_file := file

let parse_file filename =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  Lexing.set_filename lexbuf filename;
  
  let module MI = Parser.MenhirInterpreter in
  let checkpoint = Parser.Incremental.file lexbuf.lex_curr_p
  and supplier = MI.lexer_lexbuf_to_supplier Lexer.token lexbuf
  and succeed (loc, name, args, locals, ret, eqs) =
    close_in inx;
    LustreAst.
      {
        n_loc = loc;
        n_name = name;
        n_in = args;
        n_out = ret;
        n_locals = locals;
        n_body = eqs;
      }
  and fail checkpoint =
    close_in inx;
    let position = lexbuf.lex_start_p in
    try
      let error_msg =
        match checkpoint with
        | MI.HandlingError env -> env |> MI.current_state_number |> ParserMessages.message
        | _ -> assert false (* This should not happen. *)
      in
      Format.printf "%a: %s" LocationInfo.pp_position (LocationInfo.position_of_lexerpos position) error_msg;
      exit 1
    with Not_found ->
      Format.printf "%a: <unknown error message>" LocationInfo.pp_position (LocationInfo.position_of_lexerpos position);
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

let pp_error fn (pp_type: _ -> 'a -> unit) fmt ((l, e): Extracted.Result.(location * 'a r)) =
  fprintf fmt "%a: " LocationInfo.pp_extent (LocationInfo.extent_of_loc fn l);
  let open Extracted.Result in
  match e with
  | BadType ([], got) -> fprintf fmt "untypeable expression, got type %a" pp_type got
  | BadType ([expected], got) -> fprintf fmt "expected expression with type %a, got %a" pp_type expected pp_type got
  | BadType (expected, got) ->
      fprintf fmt "expected expression with type in %a, got %a"
        (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pp_type) expected pp_type got
  | IncompatibleTypeAssignment (i, t1, t2) ->
      fprintf fmt "assigned expression with type %a to variable %d with type %a"
        pp_type t2 i pp_type t1
  | UndeclaredVariable i ->
      fprintf fmt "use of undeclared variable %d" i
  | NeverAssigned (i, t) ->
      fprintf fmt "variable %d with type %a is never assigned to" i pp_type t
  | MultipleDeclaration (n, l1, l2) when l1 = l2 ->
      fprintf fmt "variable %d is declared multiple times as %s" n
        (match l1 with DeclInput -> "inputs" | DeclOutput -> "outputs" | DeclLocal -> "locals")
  | MultipleDeclaration (n, l1, l2) ->
      fprintf fmt "variable %d is declared multiple times as %s and %s" n
        (match l1 with DeclInput -> "an input" | DeclOutput -> "an output" | DeclLocal -> "a local")
        (match l2 with DeclInput -> "an input" | DeclOutput -> "an output" | DeclLocal -> "a local")
  | InternalError e -> fprintf fmt "internal error: %s" e

let () =
  Arg.parse [] entry_file usage_message;

  let node = parse_file !input_file in

  let checked_node =
    match LustreAstToLustre.check_node_prop node with
    | Ok m -> m
    | Err x ->
        let pp_type fmt (t: Extracted.Lustre.coq_type) = match t with
          | TVoid -> fprintf fmt "void"
          | TBool -> fprintf fmt "bool"
          | TInt -> fprintf fmt "int"
        in
        printf "@[Error when node properties have been checked:@\n%a@]@."
          (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@\n") (pp_error !input_file pp_type)) x;
        exit 1
  in

  match LustreOrdering.translate_node checked_node with
  | Ok m -> Generation.pp_coq_method (LustreOrderedToImp.translate_node m)
  | Err x ->
      let pp_type fmt (t: Extracted.Lustre.coq_type) = match t with
        | TVoid -> fprintf fmt "void"
        | TBool -> fprintf fmt "bool"
        | TInt -> fprintf fmt "int"
      in
      printf "@[Error lustre ordering translate:@\n%a@]@."
        (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@\n") (pp_error !input_file pp_type)) x
