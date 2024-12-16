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
  | SNop : stmt.


(** ** Equalities *)

Definition type_eqb (t1 t2: type): bool :=
  match t1, t2 with
    | TBool, TBool => true
  end.

Definition const_eqb (c1 c2: const): bool :=
  match c1, c2 with
    | CBool b1, CBool b2 => Bool.eqb b1 b2
  end.

Definition binop_eqb (op1 op2: binop): bool :=
  match op1, op2 with
    | Bop_and, Bop_and => true
    | Bop_or, Bop_or => true
    | Bop_xor, Bop_xor => true
    | _, _ => false
  end.

Fixpoint exp_eqb (e1 e2: exp): bool :=
  match e1, e2 with
    | EConst c1, EConst c2 => const_eqb c1 c2
    | EInput (i1, t1), EInput (i2, t2) | EVar (i1, t1), EVar (i2, t2) =>
      PeanoNat.Nat.eqb i1 i2 && type_eqb t1 t2
    | EBinop op1 e11 e12, EBinop op2 e21 e22 => binop_eqb op1 op2 && exp_eqb e11 e21 && exp_eqb e12 e22
    | _, _ => false
  end.

Fixpoint stmt_eqb (s1 s2: stmt): bool :=
  match s1, s2 with
    | SAssign i1 e1, SAssign i2 e2 =>  PeanoNat.Nat.eqb i1 i2 && exp_eqb e1 e2
    | SSeq s11 s12, SSeq s21 s22 => stmt_eqb s11 s21 && stmt_eqb s12 s22
    | SNop, SNop => true
    | _, _ => false
  end.


(** ** Method *)

Fixpoint is_substmt (sub s: stmt): bool :=
  stmt_eqb sub s || match s with
    | SAssign _ _ | SNop => false
    | SSeq sl sr => is_substmt sub sl || is_substmt sub sr 
  end.

Record method := mk_method {
  m_name: ident;

  m_in: list binder;
  m_out: binder;
  m_vars: list binder;

  m_body: stmt;

  m_out_assign: exists (e: exp), is_substmt (SAssign (fst m_out) e) m_body = true
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

  | SeNop (s: stack):
      sem_stmt s SNop s.


(** ** Properties *)

Fixpoint has_var (e: exp): bool :=
  match e with
    | EConst _ => false
    | EInput _ => false
    | EVar _ => true
    | EBinop _ e1 e2 => has_var e1 || has_var e2
  end.

Fixpoint has_einput (e: exp): bool :=
  match e with
    | EInput _ => true
    | EConst _ | EVar _ => false
    | EBinop _ e1 e2 => has_einput e1 || has_einput e2
  end.

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


(** ** Lemmas *)

Lemma exp_no_var_is_const (e: exp):
  has_var e = false ->
  forall (s: stack), is_evaluable e s.
Proof.
  intros H.
  induction e as [ c | | | op e1 IHe1 e2 IHe2].
  - exists (VConst c).
    simpl.
    reflexivity.
  - exists (VInput b).
    reflexivity.
  - simpl in H.
    discriminate.
  - intros s.
    simpl in H.
    apply Bool.orb_false_iff in H.
    destruct H as [ H1 H2 ].
    apply IHe1 with (s := s) in H1.
    apply IHe2 with (s := s) in H2.
    destruct H1 as [ v1 H1 ].
    destruct H2 as [ v2 H2 ].
    exists (VBinop op v1 v2).
    simpl.
    rewrite H1, H2.
    reflexivity.
Qed.

Lemma const_eqb_refl (c: const):
  const_eqb c c = true.
Proof.
  destruct c.
  - simpl.
    rewrite Bool.eqb_reflx.
    reflexivity.
Qed.

Lemma type_eqb_refl (typ: type):
  type_eqb typ typ = true.
Proof.
  destruct typ.
  - reflexivity.
Qed.

Lemma binop_eqb_refl (op: binop):
  binop_eqb op op = true.
Proof.
  destruct op; reflexivity.
Qed.

Lemma exp_eqb_refl (e: exp):
  exp_eqb e e = true.
Proof.
  induction e as [ c | (i, t) | (i, t) | op e1 IHe1 e2 IHe2].
  - simpl.
    apply const_eqb_refl.
  - simpl.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite type_eqb_refl.
    reflexivity.
  - simpl.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite type_eqb_refl.
    reflexivity.
  - simpl.
    rewrite binop_eqb_refl, IHe1, IHe2.
    reflexivity.
Qed.
