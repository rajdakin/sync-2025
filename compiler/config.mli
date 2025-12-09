type t = {
  filename: string;
  test_mode: bool;
}

val parse : string array -> t
