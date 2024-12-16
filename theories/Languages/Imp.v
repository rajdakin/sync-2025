From Reactive Require Import Base.
From Reactive.Datatypes Require Dict.


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


(** ** Semantics *)

Inductive value :=
  | VConst : const -> value
  | VInput : binder -> value
  | VBinop : binop -> value -> value -> value.

Definition stack := Dict.t value.

Inductive sem_exp: stack -> exp -> value -> Prop :=
  | SeConst (s: stack) (c: const):
      sem_exp s (EConst c) (VConst c)

  | SeInput (s: stack) (b: binder):
      sem_exp s (EInput b) (VInput b)

  | SeVar (s: stack) (b: binder) (v: value):
      Dict.maps_to (fst b) v s ->
      sem_exp s (EVar b) v

  | SeBinop (s: stack) (op: binop) (e1 e2: exp) (v1 v2: value):
      sem_exp s e1 v1 ->
      sem_exp s e2 v2 ->
      sem_exp s (EBinop op e1 e2) (VBinop op v1 v2).

Inductive sem_stmt: stack -> stmt -> stack -> Prop :=
  | SeAssign (s: stack) (name: ident) (e: exp) (v: value):
      sem_exp s e v ->
      sem_stmt s (SAssign name e) (Dict.add name v s)

  | SeSeq (s1 s2 s3: stack) (st1 st2: stmt):
      sem_stmt s1 st1 s2 ->
      sem_stmt s2 st2 s3 ->
      sem_stmt s1 (SSeq st1 st2) s3

  | SeReturn (s: stack) (e: exp) (v: value):
      sem_exp s e v ->
      sem_stmt s (SReturn e) s

  | SeNop (s: stack):
      sem_stmt s SNop s.

Fixpoint eval_exp (e: exp) (s: stack): option value :=
  match e with
    | EConst c => Some (VConst c)
    | EInput b => Some (VInput b)
    | EVar (name, typ) => Dict.find name s
    | EBinop op e1 e2 => match eval_exp e1 s, eval_exp e2 s with
      | Some v1, Some v2 => Some (VBinop op v1 v2)
      | _, _ => None
    end
  end.

Definition is_evaluable (e: exp) (s: stack): Prop :=
  exists v: value, eval_exp e s = Some v.
