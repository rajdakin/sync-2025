type t = {
  filename: string;
  test_mode: bool;
}

type error =
  | Unknown of string
  | Wrong of string * string     (* option, actual *)
  | Duplicate of string * string (* kind, name *)

let parse (args: string array): t =
  let rec inner i test_mode filename =
    if i < Array.length args then
    begin
      let s = args.(i) in
      if String.starts_with ~prefix:"-" s then begin
        if s = "-test-mode" then begin
          inner (i + 1) true filename
        end else Result.Error (
          let split s =
            let i = String.index s '=' in
            let len = String.length s in
            String.sub s 0 i, String.sub s (i+1) (len-(i+1)) in
          let keyword, arg = split s in
          if keyword = "-test-mode" then Wrong (s, arg)
          else Unknown s
        )
      end
      else if filename = None then inner (i + 1) test_mode (Some s)
      else Result.Error (Duplicate ("file", "name"))
    end
    else Result.Ok (test_mode, filename) in
  let progname =
    if 0 < Array.length args then args.(0) else "(?)" in
  let usage_b buf =
    Buffer.add_string buf progname;
    Buffer.add_string buf "<file>\n";
    Buffer.add_string buf ("  -test-mode   Enable test mode\n" ^
                           "  -help        Display this list of options\n" ^
                           "  --help       Display this list of options\n")
  in
  match inner 1 false None with
  | Result.Ok (test_mode, Some filename) -> { filename; test_mode }
  | Result.Ok (_, None) ->
      let b = Buffer.create 200 in
      usage_b b;
      Printf.bprintf b "%s: missing input file.\n" progname;
      Printf.eprintf "%s" (Buffer.contents b);
      exit 2
  | Result.Error e ->
      let convert_error error =
        let b = Buffer.create 200 in
        let progname =
          if 0 < Array.length args then args.(0) else "(?)" in
        begin match error with
          | Unknown "-help" -> ()
          | Unknown "--help" -> ()
          | Unknown s ->
              Printf.bprintf b "%s: unknown option '%s'.\n" progname s
          | Wrong (opt, arg) ->
              Printf.bprintf b "%s: wrong argument '%s'; option '%s' expects no argument.\n" progname arg opt
          | Duplicate (k, o) -> Printf.bprintf b "%s: duplicate %s %s" progname k o
        end;
        usage_b b;
        if error = Unknown "-help" || error = Unknown "--help"
        then begin Printf.printf "%s" (Buffer.contents b); exit 0 end
        else begin Printf.eprintf "%s" (Buffer.contents b); exit 2 end
      in
      convert_error e
