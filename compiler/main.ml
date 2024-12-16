(*
  Example: in = [ a; b ], out = c
    y = x && (false || a)
    z = (b <> a) || (y && x)
    c = x && (b || z)
    x = true || a

  x -> 0
  y -> 1
  z -> 2
  a -> 3
  b -> 4
  c -> 5
*)

let () =
  let tbool = snd Lustre.var_bool in
  let node = {
     Lustre.n_name = 0;
     Lustre.n_in = [(* (3, tbool); (4, tbool) *)];
     Lustre.n_out = (5, tbool);
     Lustre.n_locals = [(0, tbool); (2, tbool); (1, tbool)];
     Lustre.n_body = [
      (1, Lustre.EBinop (Lustre.Bop_and, Lustre.EVar (0, tbool), Lustre.EBinop (Lustre.Bop_or, Lustre.EConst (Stream.from false), Lustre.EVar (0, tbool))));
      (2, Lustre.EBinop (Lustre.Bop_or, Lustre.EBinop (Lustre.Bop_xor, Lustre.EVar (1, tbool), Lustre.EVar (0, tbool)), Lustre.EBinop (Lustre.Bop_and, Lustre.EVar (1, tbool), Lustre.EVar (0, tbool))));
      (5, Lustre.EBinop (Lustre.Bop_and, Lustre.EVar (0, tbool), Lustre.EBinop (Lustre.Bop_or, Lustre.EVar (1, tbool), Lustre.EVar (2, tbool))));
      (0, Lustre.EBinop (Lustre.Bop_or, Lustre.EConst (Stream.from true), Lustre.EConst (Stream.from false)))
     ]
  } [@@ocamlformat "disable"] in
  match LustreOrdering.translate_node node with
  | Result.Ok _ -> Printf.printf "Success\n"
  | Result.Err x -> Printf.printf "Error: %s\n" x
