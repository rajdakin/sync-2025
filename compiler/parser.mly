%{
    open Extracted.LustreAst

    let ident_map = Hashtbl.create 19
    let gen_id =
      let i = ref 0 in
      fun () -> incr i; !i - 1
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
%token BOOL INT VOID
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

(* (Node name) * (Node arguments) * (Local variables) * (Return) * (Equations) *)
%start<string * ((binder * coq_type) list) * ((binder * coq_type) list) * ((binder * coq_type) list) * ((int * exp) list)> node

%on_error_reduce expr

%%

typ:
  | BOOL { TBool }
  | INT  { TInt }
  | VOID { TVoid }

local_vars:
  | id=ident COLON typ=typ SEMI_COLON
    { (id, typ) :: [] }
  | id=ident COLON typ=typ SEMI_COLON vars=local_vars
    { (id, typ) :: vars }

node:
  | NODE name=node_name LPAREN args=args RPAREN ret=returns
    VAR locals=local_vars
    LET
      eqs=equation_list
    TEL EOF (* TODO: support multiple nodes in a single file *)
    { (name, args, locals, ret, eqs) }
  | NODE name=node_name LPAREN args=args RPAREN ret=returns
    LET
      eqs=equation_list
    TEL EOF
    { (name, args, [], ret, eqs) }

returns:
  | RETURNS LPAREN ret=out_list RPAREN { ret }

out_list: (* TODO: last *)
  | id=ident COLON typ=typ COMMA args=args { (id, typ) :: args }
  | id=ident COLON typ=typ { (id, typ) :: [] }
  | { [] }

args:
  | id=ident COLON typ=typ COMMA args=args { (id, typ) :: args }
  | id=ident COLON typ=typ { (id, typ) :: [] }
  | { [] }


ident:
  | id=IDENT
    { match Hashtbl.find_opt ident_map id with
      | Some x -> x
      | None -> let new_id = gen_id () in
         Hashtbl.add ident_map id new_id;
         new_id }

node_name:
  | name=IDENT { name }

equation_list:
  | id=ident EQ e=expr SEMI_COLON
    { [(id, e)] }
  | id=ident EQ e=expr SEMI_COLON eqs=equation_list
    { (id, e) :: eqs }

var:
  | id=ident { id }

const:
  | TRUE    { CBool true }
  | FALSE   { CBool false }
  | num=NUM { CInt num }

%inline unop:
  | NOT   { Uop_not }
  | MINUS { Uop_minus }
  | PRE   { Uop_pre }

%inline binop:
  | AND   { Bop_and }
  | OR    { Bop_or }
  | XOR   { Bop_xor }
  | PLUS  { Bop_plus }
  | MINUS { Bop_minus }
  | TIMES { Bop_times }
  | DIV   { Bop_div }
  | GE    { Bop_ge }
  | LE    { Bop_le }
  | GT    { Bop_gt }
  | LT    { Bop_lt }
  | EQ    { Bop_eq }
  | NEQ   { Bop_neq }
  | FBY   { Bop_fby }
  | ARROW { Bop_arrow }

expr:
  | LPAREN e=expr RPAREN    { e }
  | c=const                 { EConst c }
  | v=var                   { EVar v }
  | o=unop e1=expr          { EUnop(o, e1) }
  | e1=expr o=binop e2=expr { EBinop(o, e1, e2) }
  | IF cond=expr THEN e1=expr ELSE e2=expr { EIfte(cond, e1, e2) }
;
