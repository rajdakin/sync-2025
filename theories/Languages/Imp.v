From Reactive Require Import Base.
From Reactive.Datatypes Require Dict.


Inductive type :=
  | TVoid
  | TBool
  | TInt.

Definition binder := prod ident type.

Inductive const :=
  | CVoid: const
  | CBool: bool -> const
  | CInt: nat -> const.

Inductive unop: Type :=
  | Uop_not: unop
  | Uop_neg: unop.

Inductive binop: Type :=
  (** Boolean binop *)
  | Bop_and: binop
  | Bop_or: binop
  | Bop_xor: binop
 
  (** Arithmetic binop *)
  | Bop_plus: binop
  | Bop_minus: binop
  | Bop_mult: binop
  | Bop_div: binop
  
  (** Relational binop *)
  | Bop_eq: binop
  | Bop_le: binop
  | Bop_lt: binop
  | Bop_ge: binop
  | Bop_gt: binop.

Inductive exp: Type :=
  | EConst: const -> exp
  | EInput: binder -> exp
  | EVar: binder -> exp
  | EUnop: unop -> exp -> exp
  | EBinop: binop -> exp -> exp -> exp
  | EIfte: exp -> exp -> exp -> exp.

Inductive stmt :=
  | SAssign: ident -> exp -> stmt
  | SSeq : stmt -> stmt -> stmt
  | SNop : stmt.


(** ** Equalities *)

Definition type_eqb (x y: type): bool :=
  match x, y with
    | TVoid, TVoid => true
    | TBool, TBool => true
    | TInt, TInt => true
    | _, _ => false
  end.

Definition binder_eqb (x y: binder): bool :=
  andb (fst x =? fst y) (type_eqb (snd x) (snd y)).

Definition unop_eqb (x y: unop): bool :=
  match x, y with
    | Uop_not, Uop_not => true
    | Uop_neg, Uop_neg => true
    | _, _ => false
  end.

Definition binop_eqb (x y: binop): bool :=
  match x, y with
    | Bop_and, Bop_and => true
    | Bop_or, Bop_or => true
    | Bop_xor, Bop_xor => true
    | Bop_plus, Bop_plus => true
    | Bop_minus, Bop_minus => true
    | Bop_mult, Bop_mult => true
    | Bop_div, Bop_div => true
    | Bop_eq, Bop_eq => true
    | Bop_lt, Bop_lt => true
    | Bop_le, Bop_le => true
    | Bop_gt, Bop_gt => true
    | Bop_ge, Bop_ge => true
    | _, _ => false
  end.

Definition const_eqb (c1 c2: const): bool :=
  match c1, c2 with
    | CVoid, CVoid => true
    | CBool b1, CBool b2 => Bool.eqb b1 b2
    | CInt n1, CInt n2 => PeanoNat.Nat.eqb n1 n2
    | _, _ => false
  end.

Fixpoint exp_eqb (e1 e2: exp): bool :=
  match e1, e2 with
    | EConst c1, EConst c2 => const_eqb c1 c2
    | EInput b1, EInput b2 => binder_eqb b1 b2
    | EVar b1, EVar b2 => binder_eqb b1 b2
    | EUnop op1 e1, EUnop op2 e2 =>
      (unop_eqb op1 op2) && (exp_eqb e1 e2)
    | EBinop op1 e11 e12, EBinop op2 e21 e22 =>
      (binop_eqb op1 op2) && (exp_eqb e11 e21) && (exp_eqb e12 e22)
    | EIfte e11 e12 e13, EIfte e21 e22 e23 =>
      (exp_eqb e11 e21) && (exp_eqb e12 e22) && (exp_eqb e13 e23)
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
  m_name: string;

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
  | VUnop: unop -> value -> value
  | VBinop: binop -> value -> value -> value
  | VIfte: value -> value -> value -> value.

Definition stack := Dict.t value.

Inductive sem_exp: stack -> exp -> value -> Prop :=
  | SeConst (s: stack) (c: const):
      sem_exp s (EConst c) (VConst c)

  | SeInput (s: stack) (b: binder):
      sem_exp s (EInput b) (VInput b)

  | SeVar (s: stack) (b: binder) (v: value):
      Dict.maps_to (fst b) v s ->
      sem_exp s (EVar b) v

  | SeUnop (s: stack) (op: unop) (e: exp) (v: value):
      sem_exp s e v ->
      sem_exp s (EUnop op e) (VUnop op v)

  | SeBinop (s: stack) (op: binop) (e1 e2: exp) (v1 v2: value):
      sem_exp s e1 v1 ->
      sem_exp s e2 v2 ->
      sem_exp s (EBinop op e1 e2) (VBinop op v1 v2)

  | SeIfte (s: stack) (e1 e2 e3: exp) (v1 v2 v3: value):
      sem_exp s e1 v1 ->
      sem_exp s e2 v2 ->
      sem_exp s e3 v3 ->
      sem_exp s (EIfte e1 e2 e3) (VIfte v1 v2 v3).

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

Fixpoint eval_exp (e: exp) (s: stack): option value :=
  match e with
    | EConst c => Some (VConst c)
    | EInput b => Some (VInput b)
    | EVar (name, typ) => Dict.find name s
    | EUnop op e => match eval_exp e s with
      | Some v => Some (VUnop op v)
      | None => None
    end
    | EBinop op e1 e2 => match eval_exp e1 s, eval_exp e2 s with
      | Some v1, Some v2 => Some (VBinop op v1 v2)
      | _, _ => None
    end
    | EIfte e1 e2 e3 => match eval_exp e1 s, eval_exp e2 s, eval_exp e3 s with
      | Some v1, Some v2, Some v3 => Some (VIfte v1 v2 v3)
      | _, _, _ => None
    end
  end.


(** ** Lemmas *)

Lemma type_eqb_refl (t: type):
  type_eqb t t = true.
Proof.
  destruct t; reflexivity.
Qed.

Lemma binder_eqb_refl (b: binder):
  binder_eqb b b = true.
Proof.
  destruct b as (i, t).
  apply andb_true_intro.
  split.
  - apply PeanoNat.Nat.eqb_refl.
  - apply type_eqb_refl.
Qed.

Lemma binder_eqb_to_eq (x y : binder): binder_eqb x y = true -> x = y.
Proof.
  unfold binder_eqb, andb.
  destruct (fst x =? fst y) eqn:Heq; [| discriminate ].

  rewrite PeanoNat.Nat.eqb_eq in Heq.
  destruct x, y; simpl in Heq |- *.
  rewrite Heq.

  intros H.
  now destruct t, t0.
Qed.

Lemma unop_eqb_refl (op: unop):
  unop_eqb op op = true.
Proof.
  destruct op; reflexivity.
Qed.

Lemma unop_eqb_to_eq (op1 op2: unop):
  unop_eqb op1 op2 = true -> op1 = op2.
Proof.
  intros H.
  destruct op1, op2; (reflexivity || inversion H).
Qed.

Lemma binop_eqb_refl (op: binop):
  binop_eqb op op = true.
Proof.
  destruct op; reflexivity.
Qed.

Lemma binop_eqb_to_eq (op1 op2: binop):
  binop_eqb op1 op2 = true -> op1 = op2.
Proof.
  intros H.
  destruct op1, op2; reflexivity || inversion H.
Qed.

Lemma const_eqb_refl (c: const):
  const_eqb c c = true.
Proof.
  destruct c as [ | b | n ].
  - reflexivity.
  - apply Bool.eqb_true_iff.
    reflexivity.
  - apply PeanoNat.Nat.eqb_refl.
Qed.

Lemma const_eqb_to_eq (c1 c2: const):
  const_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros H.
  destruct c1.
  - destruct c2.
    + reflexivity.
    + inversion H.
    + inversion H.
  - destruct c2.
    + inversion H.
    + simpl in H.
      f_equal.
      apply Bool.eqb_true_iff.
      assumption.
    + inversion H.
  - destruct c2.
    + inversion H.
    + inversion H.
    + apply PeanoNat.Nat.eqb_eq in H.
      subst.
      reflexivity.
Qed.

Lemma exp_eqb_refl (e: exp):
  exp_eqb e e = true.
Proof.
  induction e.
  - apply const_eqb_refl.
  - apply binder_eqb_refl.
  - apply binder_eqb_refl.
  - apply andb_true_intro.
    split; [ | assumption ].
    apply unop_eqb_refl.
  - apply andb_true_intro.
    split; [ | assumption ].
    apply andb_true_intro.
    split; [ | assumption ].
    apply binop_eqb_refl.
  - simpl.
    rewrite IHe1, IHe2, IHe3.
    reflexivity.
Qed.

Lemma exp_eqb_to_eq (e1 e2: exp):
  exp_eqb e1 e2 = true -> e1 = e2.
Proof.
  intros H.
  revert e2 H.
  induction e1 as [ c1 | b1 | b1 | op1 e1 IH | op1 e11 IH1 e12 IH2 | e11 IH1 e12 IH2 e13 IH3 ]; intros e2 H.
  - destruct e2; try inversion H.
    apply const_eqb_to_eq in H1.
    subst.
    reflexivity.
  - destruct e2; try inversion H.
    apply binder_eqb_to_eq in H1.
    subst.
    reflexivity.
  - destruct e2; try inversion H.
    apply binder_eqb_to_eq in H1.
    subst.
    reflexivity.
  -  destruct e2; try inversion H.
    apply andb_prop in H1 as [ H1 H2 ].
    apply unop_eqb_to_eq in H1.
    apply IH in H2.
    f_equal; assumption.
  - destruct e2; try inversion H.
    apply andb_prop in H1 as [ H1 H2 ].
    apply andb_prop in H1 as [ H3 H1 ].
    apply IH1 in H1.
    apply IH2 in H2.
    apply binop_eqb_to_eq in H3.
    rewrite H1, H2, H3.
    reflexivity.
  - destruct e2; try inversion H.
    apply andb_prop in H1 as [ H1 H3 ].
    apply andb_prop in H1 as [ H1 H2 ].
    apply IH1 in H1.
    apply IH2 in H2.
    apply IH3 in H3.
    f_equal; assumption.
Qed.
