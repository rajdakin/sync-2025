%{
    open Extracted.Lustre

    let ident_map = Hashtbl.create 19
    let gen_id =
      let i = ref 0 in
      fun () -> incr i; !i - 1
%}

%token<string> IDENT
%token LPAREN RPAREN
%token AND OR XOR
%token TRUE FALSE
%token EQ SEMI_COLON COLON COMMA
%token NODE RETURN VAR
%token BOOL
%token LET TEL EOF

%left AND OR XOR

%start<string * (binder list) *(binder list) * int * ((int*exp) list)> node

%%

typ:
  | BOOL { snd Extracted.Lustre.var_bool }

local_vars:
  | id = ident COLON typ = typ SEMI_COLON
    { (id, typ) :: [] }
  | id = ident COLON typ = typ SEMI_COLON vars = local_vars
    { (id, typ) :: vars }

node:
  | NODE name=ident_node LPAREN args=args RPAREN RETURN ret = ident COLON typ
    VAR locals = local_vars
    LET
      eqs = equation_list
    TEL EOF
    { (name, args,locals, ret, eqs) }
  | NODE name=ident_node LPAREN args=args RPAREN RETURN ret = ident COLON typ
    LET
      eqs = equation_list
    TEL EOF
    { (name, args,[], ret, eqs) }

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

expr:
  | LPAREN e = expr RPAREN { e }
  | c = const { EConst(c) }
  | v = var { EVar((v, snd Extracted.Lustre.var_bool)) }
  | e1 = expr AND e2 = expr { EBinop(Bop_and, e1, e2) }
  | e1 = expr OR e2 = expr { EBinop(Bop_or, e1, e2) }
  | e1 = expr XOR e2 = expr { EBinop(Bop_xor, e1, e2) }
