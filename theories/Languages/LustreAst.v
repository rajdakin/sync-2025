
From Reactive Require Import Base.
From Reactive.Datatypes Require Dict Stream.


From Coq Require Import Permutation String.

Inductive type: Type :=
  | TVoid
  | TBool
  | TInt.

Definition binder := prod ident type.

Inductive const: Type :=
  | CVoid: const
  | CBool: bool -> const
  | CInt: nat -> const.

(** A unary operator

  An operator of type [unop tyin tyout] takes an argument of type [tyin] and
  returns an expression of type [tyout].
*)
Inductive unop: Type :=
  | Uop_not: unop
  | Uop_neg: unop.

(** A binary operator

  An operator of type [binop ty1 ty2 tyout] takes two arguments of type [ty1]
  and [ty2] returns an expression of type [tyout].
*)
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

Fixpoint has_einput (e: exp): bool :=
  match e with
    | EInput _ => true
    | EConst _ | EVar _ => false
    | EUnop _ e => has_einput e
    | EBinop _ e1 e2 => has_einput e1 || has_einput e2
    | EIfte e1 e2 e3 => has_einput e1 || has_einput e2 || has_einput e3
  end.

Definition equation := prod ident exp.


Record node := mk_node {
  n_name: string;

  n_in: list binder;
  n_out: binder;
  n_locals: list binder;
  n_body: list equation;
}.


Definition node_eq (n1 n2: node) :=
  n_name n1 = n_name n2 /\
  Permutation (n_in n1) (n_in n2) /\
  n_out n1 = n_out n2 /\
  Permutation (n_locals n1) (n_locals n2) /\
  Permutation (n_body n1) (n_body n2).


Definition var_bool := (0, TBool).

Definition name_dec := String.string_dec.


Fixpoint var_of_exp_aux (e: exp) (acc: list ident): list ident :=
  match e with
    | EConst _ => acc
    | EInput _ => acc
    | EVar (name, _) => name :: acc
    | EUnop _ e => var_of_exp_aux e acc
    | EBinop _ e1 e2 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 acc)
    | EIfte e1 e2 e3 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 (var_of_exp_aux e3 acc))
  end.

Definition var_of_exp (e: exp): list ident :=
  var_of_exp_aux e [].


(** ** Equality of binders *)

Definition type_eqb (x y: type): bool :=
  match x, y with
    | TVoid, TVoid => true
    | TBool, TBool => true
    | TInt, TInt => true
    | _, _ => false
  end.

Lemma type_eqb_refl (t: type):
  type_eqb t t = true.
Proof.
  destruct t; reflexivity.
Qed.

Lemma type_dec (x y: type): {x = y} + {x <> y}.
Proof.
  destruct x, y.
  1, 5, 9: left; reflexivity.
  all: right; inversion 1.
Qed.

Definition binder_eqb (x y: binder): bool :=
  andb (fst x =? fst y) (type_eqb (snd x) (snd y)).

Lemma binder_dec (x y: binder): {x = y} + {x <> y}.
Proof.
  destruct x, y.

  pose proof (PeanoNat.Nat.eq_dec i i0).
  destruct H.
  2: {
    right.
    inversion 1.
    contradiction.
  }

  destruct (type_dec t t0).
  2: {
    right.
    inversion 1.
    contradiction.
  }

  subst.
  left.
  reflexivity.
Defined.

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

Lemma binder_eq_to_eqb (x y : binder): x = y -> binder_eqb x y = true.
Proof.
  unfold binder_eqb, andb.
  destruct x, y; simpl.

  inversion 1.

  rewrite PeanoNat.Nat.eqb_refl.
  now destruct t, t0.
Qed.


(** ** Equality of equations *)

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

Definition equation_eqb (eq1 eq2: equation): bool :=
  (fst eq1 =? fst eq2) && (exp_eqb (snd eq1) (snd eq2)).

Lemma equation_eqb_to_eq (eq1 eq2: equation):
  equation_eqb eq1 eq2 = true -> eq1 = eq2.
Proof.
  intros H.
  destruct eq1, eq2.
  apply andb_prop in H as [ H1 H2 ].
  apply PeanoNat.Nat.eqb_eq in H1.
  apply exp_eqb_to_eq in H2.
  simpl in H1, H2.
  rewrite H1, H2.
  reflexivity.
Qed.

Lemma equation_eqb_refl (eq: equation):
  equation_eqb eq eq = true.
Proof.
  destruct eq as (i, e).
  apply andb_true_intro.
  split.
  - apply PeanoNat.Nat.eqb_refl.
  - apply exp_eqb_refl.
Qed.

Lemma equation_eq_to_eqb (eq1 eq2: equation):
  eq1 = eq2 -> equation_eqb eq1 eq2 = true.
Proof.
  intros H.
  rewrite H.
  apply equation_eqb_refl.
Qed.

