type position = string * int * int
let pp_position fmt ((f, l, c): position) =
  Format.fprintf fmt "%s:%i:%i" f l c
let position_of_lexerpos (p: Lexing.position): position = (p.pos_fname, p.pos_lnum, p.pos_cnum - p.pos_bol + 1)

type extent = position * position

let extent_of_len (len: int) (p: Lexing.position) =
  let ((f, l, c) as e) = position_of_lexerpos p in ((f, l, c - len), e)

let pp_extent fmt ((f1, l1, c1), (f2, l2, c2): extent) =
  if f1 = f2 then
    if l1 = l2 then
      if c1 = c2 then
        Format.fprintf fmt "%s:%i:%i" f1 l1 c1
      else
        Format.fprintf fmt "%s:%i:%i-%i" f1 l1 c1 c2
    else
      Format.fprintf fmt "%s:%i:%i-%i:%i" f1 l1 c1 l2 c2
  else
    Format.fprintf fmt "%s:%i:%i-%s:%i:%i" f1 l1 c1 f2 l2 c2

let extend_to_pos (e: extent) (p: Lexing.position): extent = (fst e, position_of_lexerpos p)
let extend_to_ext (e1: extent) (e2: extent): extent = (fst e1, snd e2)

let extent_of_loc (fn: string) (l: Extracted.Result.location): extent =
  ((fn, l.loc_start_line, l.loc_start_col), (fn, l.loc_end_line, l.loc_end_col))
