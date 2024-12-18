%{
    open Extracted.Lustre

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
%token TIMES
%token TRUE FALSE
%token SEMI_COLON COLON COMMA
%token NODE RETURN VAR
%token BOOL INT VOID
%token LET TEL EOF
%token IF THEN ELSE

%left AND OR XOR NOT
%left LT GT GE LE
%left PLUS MINUS TIMES
%left EQ
%left ELSE

%start<string * (binder list) *(binder list) * binder * ((int*exp) list)> node

%%

typ:
  | BOOL { TBool }
  | INT  { TInt }
  | VOID { TVoid }

local_vars:
  | id = ident COLON typ = typ SEMI_COLON
    { (id, typ) :: [] }
  | id = ident COLON typ = typ SEMI_COLON vars = local_vars
    { (id, typ) :: vars }

node:
  | NODE name=ident_node LPAREN args=args RPAREN  ret=returns
    VAR locals = local_vars
    LET
      eqs = equation_list
    TEL EOF
    { (name, args,locals, ret, eqs) }
  | NODE name=ident_node LPAREN args=args RPAREN ret=returns
    LET
      eqs = equation_list
    TEL EOF
    { (name, args,[], ret, eqs) }

returns:
  | RETURN ret = ident COLON typ=typ {(ret,typ)}

args:
  | id=ident COLON typ = typ COMMA args=args {(id,typ)::args}
  | id=ident COLON typ = typ {(id,typ)::[]}
  | { [] }


ident:
  | id = IDENT
    { match Hashtbl.find_opt ident_map id with
      | Some x -> x
      | None -> let new_id = gen_id () in
         Hashtbl.add ident_map id new_id;
         new_id }

ident_node:
  | id = IDENT { id }

equation_list:
  | id = ident EQ e = expr SEMI_COLON
    { [(id, e)] }
  | id = ident EQ e = expr SEMI_COLON eqs = equation_list
    { (id, e) :: eqs }

var:
  | id = ident { id }

const:
  | TRUE { CBool true }
  | FALSE { CBool false }
  | num=NUM   { CInt num}

expr:
  | LPAREN e = expr RPAREN    { e }
  | c = const                 { EConst(c) }
  | v = var                   { EVar((v, snd Extracted.Lustre.var_bool)) }
  | e1 = expr AND e2 = expr   { EBinop(Bop_and, e1, e2) }
  | e1 = expr OR e2 = expr    { EBinop(Bop_or, e1, e2) }
  | e1 = expr XOR e2 = expr   { EBinop(Bop_xor, e1, e2) }
  | e1 = expr PLUS e2 = expr  { EBinop(Bop_plus, e1, e2) }
  | e1 = expr MINUS e2 = expr { EBinop(Bop_minus, e1, e2) }
  | e1 = expr TIMES e2 = expr { EBinop(Bop_mult, e1, e2) }
  | e1 = expr GE e2 = expr { EBinop(Bop_ge, e1, e2) }
  | e1 = expr LE e2 = expr { EBinop(Bop_le, e1, e2) }
  | e1 = expr GT e2 = expr { EBinop(Bop_gt, e1, e2) }
  | e1 = expr LT e2 = expr { EBinop(Bop_lt, e1, e2) }
  | e1 = expr EQ e2 = expr { EBinop(Bop_eq, e1, e2) }
  | NOT e1 = expr             {EUnop(Uop_not,e1)}
  | MINUS e1 = expr           {EUnop(Uop_neg,e1)}
  | IF cond=expr THEN e1=expr ELSE e2=expr {EIfte(cond,e1,e2)}
;
