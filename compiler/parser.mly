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
%token EQ
%token AND OR XOR NOT
%token LE GE LT GT
%token PLUS MINUS
%token TIMES DIV
%token TRUE FALSE
%token SEMI_COLON COLON COMMA
%token NODE RETURN VAR
%token BOOL INT VOID
%token LET TEL EOF
%token IF THEN ELSE
%token PRE ARROW FBY

%left ELSE
%right ARROW
%left OR
%left AND
%left EQ LT GT GE LE
%left PLUS MINUS
%left TIMES DIV
%right FBY
%right PRE
%left XOR
%nonassoc NOT

(* (Node name) * (Node arguments) * (Local variables) * (Return) * (Equations) *)
%start<string * (binder list) * (binder list) * binder * ((int * exp) list)> node

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

returns: (* TODO: support multiple return values *)
  | RETURN ret=ident COLON typ=typ {(ret, typ)}

args:
  | id=ident COLON typ=typ COMMA args=args {(id,typ)::args}
  | id=ident COLON typ=typ {(id,typ)::[]}
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
  | TRUE { CBool true }
  | FALSE { CBool false }
  | num=NUM   { CInt num }

expr:
  | LPAREN e=expr RPAREN    { e }
  | c=const                 { EConst(c) }
  | v=var                   { EVar((v, TBool)) }
  | e1=expr AND e2=expr     { EBinop(Bop_and, e1, e2) }
  | e1=expr OR e2=expr      { EBinop(Bop_or, e1, e2) }
  | e1=expr XOR e2=expr     { EBinop(Bop_xor, e1, e2) }
  | e1=expr PLUS e2=expr    { EBinop(Bop_plus, e1, e2) }
  | e1=expr MINUS e2=expr   { EBinop(Bop_minus, e1, e2) }
  | e1=expr TIMES e2=expr   { EBinop(Bop_mult, e1, e2) }
  | e1=expr DIV e2=expr     { EBinop(Bop_div, e1, e2) }
  | e1=expr GE e2=expr      { EBinop(Bop_ge, e1, e2) }
  | e1=expr LE e2=expr      { EBinop(Bop_le, e1, e2) }
  | e1=expr GT e2=expr      { EBinop(Bop_gt, e1, e2) }
  | e1=expr LT e2=expr      { EBinop(Bop_lt, e1, e2) }
  | e1=expr EQ e2=expr      { EBinop(Bop_eq, e1, e2) }
  | e1=expr ARROW e2=expr   { Ebinop(Bop_arrow, e1, e2) }
  | e1=expr FBY e2=expr     { Ebinop(Bop_fby, e1, e2) }
  | PRE e1=expr             { EUnop(Uop_pre, e1) }
  | NOT e1=expr             { EUnop(Uop_not, e1) }
  | MINUS e1=expr           { EUnop(Uop_neg, e1) }
  | IF cond=expr THEN e1=expr ELSE e2=expr { EIfte(cond, e1, e2) }
;
