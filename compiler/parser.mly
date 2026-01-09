%{
    open Extracted.Semantics
    open Extracted.LustreAst
    open LocationInfo

    let loc_of_ext (((_, ls, cs), (_, le, ce)): extent): Extracted.Result.location = Extracted.Result.{
      loc_start_line = ls;
      loc_start_col = cs;
      loc_end_line = le;
      loc_end_col = ce;
    }
%}

%token<string> IDENT
%token<int> NUM
%token LPAREN RPAREN
%token EQ NEQ
%token AND OR XOR NOT
%token LE GE LT GT
%token PLUS MINUS
%token TIMES DIV
%token TRUE FALSE
%token SEMI_COLON COLON COMMA
%token NODE RETURNS VAR
%token BOOL INT
%token LET TEL EOF
%token IF THEN ELSE
%token PRE ARROW FBY

%left ELSE
%right ARROW
%left OR
%left AND
%left EQ NEQ LT GT GE LE
%left PLUS MINUS
%left TIMES DIV
%right FBY
%right PRE
%left XOR
%nonassoc NOT

(* (Node location) * (Node name) * (Node arguments) * (Local variables) * (Return) * (Equations) *)
%start<
  Extracted.Result.location *
  string *
  ((binder * coq_type) list) *
  ((binder * coq_type) list) *
  ((binder * coq_type) list) *
  ((Extracted.Result.location * (string * exp)) list)
> file

%on_error_reduce expr

%%

file:
  node = node { fst node }

typ:
  | BOOL { (TBool, (extent_of_len 4 $endpos)) }
  | INT  { (TInt, (extent_of_len 3 $endpos)) }

local_vars:
  | id=ident COLON typ=typ SEMI_COLON
    { ((fst id, fst typ) :: [], extend_to_pos (snd id) $endpos) }
  | id=ident COLON typ=typ SEMI_COLON vars=local_vars
    { ((fst id, fst typ) :: fst vars, extend_to_ext (snd id) (snd vars)) }

node:
  | NODE name=node_name LPAREN args=args RPAREN ret=returns
    VAR locals=local_vars
    LET
      eqs=equation_list
    TEL EOF (* TODO: support multiple nodes in a single file *)
    { let p = extend_to_pos (extent_of_len 4 $endpos($1)) $endpos in
      ((loc_of_ext p, fst name, fst args, fst locals, fst ret, fst eqs), p) }
  | NODE name=node_name LPAREN args=args RPAREN ret=returns
    LET
      eqs=equation_list
    TEL EOF
    { let p = extend_to_pos (extent_of_len 4 $endpos($1)) $endpos in
      ((loc_of_ext p, fst name, fst args, [], fst ret, fst eqs), p) }

returns:
  | RETURNS LPAREN ret=out_list RPAREN { ret }

out_list: (* TODO: last *)
  | id=ident COLON typ=typ COMMA args=args { ((fst id, fst typ) :: fst args, extend_to_ext (snd id) (snd args)) }
  | id=ident COLON typ=typ { ((fst id, fst typ) :: [], extend_to_ext (snd id) (snd typ)) }
  | { ([], extent_of_len 0 $endpos) }

args:
  | id=ident COLON typ=typ COMMA args=args { ((fst id, fst typ) :: fst args, extend_to_ext (snd id) (snd args)) }
  | id=ident COLON typ=typ { ((fst id, fst typ) :: [], extend_to_ext (snd id) (snd typ)) }
  | { ([], extent_of_len 0 $endpos) }


ident:
  | id=IDENT { (id, extent_of_len (String.length id) $endpos) }

node_name:
  | name=IDENT { (name, extent_of_len (String.length name) $endpos) }

equation_list:
  | id=ident EQ e=expr SEMI_COLON
    { ([loc_of_ext (extend_to_pos (snd id) $endpos($4)), (fst id, fst e)], extend_to_pos (snd id) $endpos) }
  | id=ident EQ e=expr SEMI_COLON eqs=equation_list
    { ((loc_of_ext (extend_to_pos (snd id) $endpos($4)), (fst id, fst e)) :: fst eqs, extend_to_ext (snd id) (snd eqs)) }

var:
  | id=ident { id }

const:
  | TRUE    { (CBool true, extent_of_len 4 $endpos) }
  | FALSE   { (CBool false, extent_of_len 5 $endpos) }
  | num=NUM { (CInt num, extent_of_len (String.length (string_of_int num)) $endpos) }

%inline unop:
  | NOT   { (Uop_not, extent_of_len 3 $endpos) }
  | MINUS { (Uop_neg, extent_of_len 5 $endpos) }
  | PRE   { (Uop_pre, extent_of_len 3 $endpos) }

%inline binop:
  | AND   { Bop_and }
  | OR    { Bop_or }
  | XOR   { Bop_xor }
  | PLUS  { Bop_plus }
  | MINUS { Bop_minus }
  | TIMES { Bop_mult }
  | DIV   { Bop_div }
  | GE    { Bop_ge }
  | LE    { Bop_le }
  | GT    { Bop_gt }
  | LT    { Bop_lt }
  | EQ    { Bop_eq }
  | NEQ   { Bop_neq }
  | ARROW { Bop_arrow }

expr:
  | LPAREN e=expr RPAREN    { (fst e, extend_to_pos (extent_of_len 1 $endpos($1)) $endpos) }
  | c=const                 { (EConst (loc_of_ext (snd c), fst c), snd c) }
  | v=var                   { (EVar (loc_of_ext (snd v), fst v), snd v) }
  | o=unop e1=expr          { let p = extend_to_ext (snd o) (snd e1) in (EUnop (loc_of_ext p, fst o, fst e1), p) }
  | e1=expr o=binop e2=expr { let p = extend_to_ext (snd e1) (snd e2) in (EBinop (loc_of_ext p, o, fst e1, fst e2), p) }
  | e1=expr FBY e2=expr     { let p = extend_to_ext (snd e1) (snd e2) in (EBinop (loc_of_ext p, Bop_arrow, fst e1, EUnop (loc_of_ext p, Uop_pre, fst e2)), p) }
  | IF cond=expr THEN e1=expr ELSE e2=expr { let p = extend_to_ext (extent_of_len 2 $endpos($1)) (snd e2) in (EIfte (loc_of_ext p, fst cond, fst e1, fst e2), p) }
;
