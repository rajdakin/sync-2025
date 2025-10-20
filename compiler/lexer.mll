{
    open Parser
    exception Error of string
}

rule token = parse
  | [ ' ' '\t' '\n' ] { token lexbuf }
  | "&&"        { AND }
  | "and"       { AND }
  | "||"        { OR }
  | "or"        { OR }
  | "->"        { ARROW }
  | '^'         { XOR }
  | '+'         { PLUS }
  | '-'         { MINUS }
  | '*'         { TIMES }
  | '/'         { DIV }
  | '~'         { NOT }
  | "not"       { NOT }
  | "<>"        { NEQ }
  | "!="        { NEQ }
  | "<="        { LE }
  | ">="        { GE }
  | '<'         { LT }
  | '>'         { GT }
  | "true"      { TRUE }
  | "false"     { FALSE }
  | "="         { EQ }
  | ","         { COMMA }
  | ";"         { SEMI_COLON }
  | ":"         { COLON }
  | "("         { LPAREN }
  | ")"         { RPAREN }
  | "pre"       { PRE }
  | "fby"       { FBY }
  | "node"      { NODE }
  | "var"       { VAR }
  | "returns"   { RETURNS }
  | "let"       { LET }
  | "tel"       { TEL }
  | "bool"      { BOOL }
  | "int"       { INT }
  | "void"      { VOID }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | eof         { EOF }
  | ['0'-'9' '_']+ as id { NUM (int_of_string id) }
  | ['A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* as id { IDENT id }
  | _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }
