{
    open Parser
    exception Eof
    exception Error of string
}

rule token = parse
  | [ ' ' '\t' '\n' ] {token lexbuf}
  | "&&"        {AND}
  | "||"        {OR}
  | '^'         {XOR}
  | "true"      {TRUE}
  | "false"     {FALSE}
  | "="         {EQ}
  | ","         {COMMA}
  | ";"         {SEMI_COLON}
  | ":"         {COLON}
  | "("         {LPAREN}
  | ")"         {RPAREN}
  | "node"      {NODE}
  | "var"       {VAR}
  | "return"    {RETURN}
  | "let"       {LET}
  | "tel"       {TEL}
  | "bool"      {BOOL}
  | eof         {EOF}
  | ['A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* as id {IDENT id}
  | _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }
