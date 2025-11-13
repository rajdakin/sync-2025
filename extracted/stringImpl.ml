let compare (s1 : string) (s2 : string) : Datatypes.comparison =
  let c = Stdlib.String.compare s1 s2 in
  if c < 0 then Lt
  else if c = 0 then Eq
  else Gt
