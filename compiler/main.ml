open Format

let parse_file filename : (Extracted.LustreAst.node, string) result =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  Lexing.set_filename lexbuf filename;
  
  let module MI = Parser.MenhirInterpreter in
  let checkpoint = Parser.Incremental.file lexbuf.lex_curr_p
  and supplier = MI.lexer_lexbuf_to_supplier Lexer.token lexbuf
  and succeed (loc, name, args, locals, ret, eqs) =
    close_in inx;
    Result.Ok Extracted.LustreAst.{
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
      Result.Error
        (Format.asprintf "%a: %s" LocationInfo.pp_position (LocationInfo.position_of_lexerpos position) error_msg)
    with Not_found ->
      Result.Error
        (Format.asprintf "%a: <unknown error message>" LocationInfo.pp_position (LocationInfo.position_of_lexerpos position))
  in
  try
    MI.loop_handle succeed fail supplier checkpoint
  with Lexer.Error msg ->
    close_in inx;
    eprintf "lexer error: %s" msg;
    exit 1
  | e ->
    Result.Error (Format.sprintf "%s@\n" (Printexc.to_string e))

let pp_type fmt (t: Extracted.Semantics.coq_type) = match t with
  | TBool -> fprintf fmt "bool"
  | TInt -> fprintf fmt "int"

let pp_error fn (namemap: (int, string) Hashtbl.t) fmt ((l, e): (Extracted.Result.location * 'a Extracted.Result.r)) =
  fprintf fmt "@[%a: " LocationInfo.pp_extent (LocationInfo.extent_of_loc fn l);
  let open Extracted.Result in
  match e with
  | BadType ([], got) -> fprintf fmt "untypeable expression, got type %a@]" pp_type got
  | BadType ([expected], got) -> fprintf fmt "expected expression with type %a, got %a@]" pp_type expected pp_type got
  | BadType (expected, got) ->
      fprintf fmt "expected expression with type in %a, got %a@]"
        (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pp_type) expected pp_type got
  | IncompatibleTypeAssignment (n, i, t1, t2) ->
      fprintf fmt "assigned expression with type %a to variable %s(%d) with type %a@]"
        pp_type t2 n i pp_type t1
  | UndeclaredVariable n ->
      fprintf fmt "use of undeclared variable %s@]" n
  | MultipleDeclaration (n, i, l1, l2) when l1 = l2 ->
      fprintf fmt "variable %s(%d) is declared multiple times as %s@]" n i
        (match l1 with DeclInput -> "inputs" | DeclOutput -> "outputs" | DeclLocal -> "locals")
  | MultipleDeclaration (n, i, l1, l2) ->
      fprintf fmt "variable %s(%d) is declared multiple times as %s and %s@]" n i
        (match l1 with DeclInput -> "an input" | DeclOutput -> "an output" | DeclLocal -> "a local")
        (match l2 with DeclInput -> "an input" | DeclOutput -> "an output" | DeclLocal -> "a local")
  | MissingAssignment (n, i, t) ->
      fprintf fmt "variable %s(%d) with type %a is never assigned to@]" n i pp_type t
  | MultipleAssignment (n, i, t) ->
      fprintf fmt "variable %s(%d) with type %a is assigned more than once@]" n i pp_type t
  | AssignToInput (n, i, t) ->
      fprintf fmt "input %s(%d) with type %a is assigned@]" n i pp_type t
  | InvalidTiming (n, i, t) ->
      fprintf fmt "equation for %s(%d) with type %a has an invalid timing expectation@]" n i pp_type t
  | CyclicDependency [] ->
      fprintf fmt "internal error: empty cyclic dependency@]"
  | CyclicDependency vs ->
      fprintf fmt "there is a cyclic dependency:@ @[<hov>%a@]@]"
        (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " depends on@ ")
          (fun fmt i -> pp_print_string fmt (match Hashtbl.find_opt namemap i with Some v -> v | None -> "?(" ^ (string_of_int i) ^ ")")))
        vs
  | InternalError e -> fprintf fmt "internal error: %s@]" e

let () =
  let Config.{ test_mode; filename } = Config.parse Sys.argv in
  let exit code = if test_mode then exit 0 else exit code in
  let output mode =
    if test_mode then
      match Filename.chop_suffix_opt ~suffix:".mls" filename with
      | None ->
          Format.eprintf "%s: invalid test file name (does not ends with '.mls')" Sys.argv.(0);
          exit 1
      | Some fn ->
          let outf = open_out (fn ^ ".output") in
          let fmt = Format.formatter_of_out_channel outf in
          at_exit (fun () -> Format.pp_print_flush fmt ());
          let status = ref None in
          let ret1 : 'a. ('a, formatter, unit) format -> 'a = fun s ->
            if !status = None then begin
              status := Some false;
              Format.fprintf fmt "@[Test error@\n@]"
            end;
            Format.fprintf fmt s in
          let ret2 : 'a. ('a, formatter, unit) format -> 'a = fun s ->
            if !status = None then begin
              status := Some true;
              Format.fprintf fmt "@[Test success@\n@\n@]"
            end;
            Format.fprintf fmt s in
          if mode then ret1 else ret2
    else
      let ret1 : 'a. ('a, formatter, unit) format -> 'a = Format.eprintf in
      let ret2 : 'a. ('a, formatter, unit) format -> 'a = Format.printf in
      if mode then ret1 else ret2
  in
  let output_err = true in let output_out = false in

  let node =
    match parse_file filename with
    | Ok m -> m
    | Error s ->
        output output_err "%s" s;
        exit 1
    in

  let var_names, checked_node =
    match Extracted.LustreAstToLustre.check_node_prop node with
    | Ok m -> m
    | Err x ->
        output output_err "@[Error%s when node properties have been checked:@\n%a@]@."
          (match x with [] | [_] -> "" | _ :: _ :: _ -> "s")
          (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@\n") (pp_error filename (Hashtbl.create 0))) x;
        exit 1
  in

  let timed_node =
    match Extracted.LustreToTiming.translate_node checked_node with
    | Ok m -> m
    | Err x ->
        output output_err "@[Error%s when node is timed:@\n%a@]@."
          (match x with [] | [_] -> "" | _ :: _ :: _ -> "s")
          (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@\n") (pp_error filename (Hashtbl.create 0))) x;
        exit 1
  in

  match Extracted.LustreOrdering.translate_node timed_node with
  | Ok m ->
      let output f = output output_out f in
      Generation.pp_coq_method_pair Generation.{fprintf = output} (Extracted.LustreOrderedToImp.translate_node m)
  | Err x ->
      output output_err "@[Error lustre ordering translate:@\n%a@]@."
        (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@\n") (pp_error filename var_names)) x
