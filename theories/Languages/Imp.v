From Reactive Require Import Base.


Inductive type :=
  | TBool.

Definition binder := prod ident type.

Inductive const :=
  | CBool: bool -> const.

Inductive binop :=
  | Bop_and : binop
  | Bop_or : binop
  | Bop_xor : binop.

Inductive exp :=
  | EConst : const -> exp
  | EInput : binder -> exp
  | EVar : binder -> exp
  | EBinop : binop -> exp -> exp -> exp.

Inductive stmt :=
  | SAssign: ident -> exp -> stmt
  | SSeq : stmt -> stmt -> stmt
  | SReturn : exp -> stmt
  | SNop : stmt.

Record method := mk_method {
  m_name: ident;

  m_in: list binder;
  m_out: type;
  m_vars: list binder;

  m_body: stmt;
}.
