
From Reactive Require Import Base.
From Reactive.Datatypes Require Dict Stream.


From Stdlib Require Import Permutation String.

Inductive type: Type :=
  | TVoid
  | TBool
  | TInt.

Definition binder := ident.

Inductive const: Type :=
  | CVoid: const
  | CBool: bool -> const
  | CInt: nat -> const.

(** A unary operator

  An operator of type [unop tyin tyout] takes an argument of type [tyin] and
  returns an expression of type [tyout].
*)
Inductive unop: Type :=
  (** Boolean unop *)
  | Uop_not: unop

  (** Arithmetic unop *)
  | Uop_neg: unop
  
  (** Timing unop *)
  | Uop_pre: unop
  .

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
  | Bop_neq: binop
  | Bop_le: binop
  | Bop_lt: binop
  | Bop_ge: binop
  | Bop_gt: binop

  (** Timing binop *)
  | Bop_arrow: binop
  | Bop_fby: binop
  .

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
  n_in: list (binder * type);
  n_out: (binder * type);
  n_locals: list (binder * type);
  n_body: list equation;
}.


Definition node_eq (n1 n2: node) :=
  n_name n1 = n_name n2 /\
  Permutation (n_in n1) (n_in n2) /\
  n_out n1 = n_out n2 /\
  Permutation (n_locals n1) (n_locals n2) /\
  Permutation (n_body n1) (n_body n2).

Definition name_dec := String.string_dec.


Fixpoint var_of_exp_aux (e: exp) (acc: list ident): list ident :=
  match e with
    | EConst _ => acc
    | EInput _ => acc
    | EVar name => name :: acc
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

Lemma type_eqb_eq (x y: type):
  type_eqb x y = true <-> x = y.
Proof.
  destruct x, y.
  all: firstorder.
  all: discriminate.
Qed.

Lemma type_eqb_refl (t: type):
  type_eqb t t = true.
Proof.
  destruct t; reflexivity.
Qed.

Lemma type_dec (x y: type): {x = y} + {x <> y}.
Proof.
  destruct x, y.
  all: try (left; reflexivity).
  all: right; inversion 1.
Defined.

Definition binder_eqb (x y: binder): bool := (x =? y).

Lemma binder_eqb_eq (x y: binder):
  binder_eqb x y = true <-> x = y.
Proof.
  apply PeanoNat.Nat.eqb_eq.
Qed.

Lemma binder_dec (x y: binder): {x = y} + {x <> y}.
Proof.
  exact (PeanoNat.Nat.eq_dec x y).
Defined.

Lemma binder_eqb_refl (b: binder):
  binder_eqb b b = true.
Proof.
  apply PeanoNat.Nat.eqb_refl.
Qed.

Lemma binder_eqb_to_eq (x y : binder): binder_eqb x y = true -> x = y.
Proof.
  unfold binder_eqb, andb.
  destruct (x =? y) eqn:Heq; [| discriminate ].

  now rewrite PeanoNat.Nat.eqb_eq in Heq.
Qed.

Lemma binder_eq_to_eqb (x y : binder): x = y -> binder_eqb x y = true.
Proof.
  unfold binder_eqb.
  intros ->.
  apply PeanoNat.Nat.eqb_refl.
Qed.


(** ** Equality of equations *)

Definition unop_eqb (x y: unop): bool :=
  match x, y with
    | Uop_not, Uop_not => true
    | Uop_neg, Uop_neg => true
    | Uop_pre, Uop_pre => true
    | _, _ => false
  end.

Lemma unop_eqb_eq (x y: unop):
  unop_eqb x y = true <-> x = y.
Proof.
  destruct x, y.
  all: firstorder.
  all: discriminate.
Qed.

Lemma unop_eqb_refl (op: unop):
  unop_eqb op op = true.
Proof.
  destruct op; reflexivity.
Qed.

Lemma unop_dec (x y: unop) : {x = y} + {x <> y}.
Proof.
  destruct x, y.
  all: try (right; discriminate).
  all: left; reflexivity.
Defined.

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
    | Bop_neq, Bop_neq => true
    | Bop_lt, Bop_lt => true
    | Bop_le, Bop_le => true
    | Bop_gt, Bop_gt => true
    | Bop_ge, Bop_ge => true
    | Bop_arrow, Bop_arrow => true
    | Bop_fby, Bop_fby => true
    | _, _ => false
  end.

Lemma binop_eqb_eq (x y: binop):
  binop_eqb x y = true <-> x = y.
Proof.
  destruct x, y.
  all: firstorder.
  all: discriminate.
Qed.

Lemma binop_eqb_refl (op: binop):
  binop_eqb op op = true.
Proof.
  destruct op; reflexivity.
Qed.

Lemma binop_dec (x y: binop) : {x = y} + {x <> y}.
Proof.
  destruct x, y.
  all: try (right; discriminate).
  all: left; reflexivity.
Defined.

Definition const_eqb (c1 c2: const): bool :=
  match c1, c2 with
    | CVoid, CVoid => true
    | CBool b1, CBool b2 => Bool.eqb b1 b2
    | CInt n1, CInt n2 => PeanoNat.Nat.eqb n1 n2
    | _, _ => false
  end.

Lemma const_eqb_eq (c1 c2: const):
  const_eqb c1 c2 = true <-> c1 = c2.
Proof.
  unfold const_eqb.
  destruct c1, c2.
  all: firstorder.
  all: try discriminate.
  - apply Bool.eqb_prop in H.
    subst.
    reflexivity.
  - inversion H.
    subst.
    apply Bool.Is_true_eq_true.
    apply Bool.eqb_refl.
  - apply PeanoNat.Nat.eqb_eq in H.
    subst.
    reflexivity.
  - inversion H.
    subst.
    apply PeanoNat.Nat.eqb_refl.
Qed.

Lemma const_eqb_refl (c: const):
  const_eqb c c = true.
Proof.
  apply const_eqb_eq.
  reflexivity.
Qed.

Lemma const_dec (c1 c2: const) : {c1 = c2} + {c1 <> c2}.
Proof.
  destruct c1,c2.
  all: try (right; discriminate).
  - left; reflexivity.
  - destruct (Bool.bool_dec b b0).
    + left. rewrite e. reflexivity.
    + right. inversion 1. contradiction.
  - destruct (PeanoNat.Nat.eq_dec n n0).
    + left. rewrite e. reflexivity.
    + right. inversion 1. contradiction.
Defined.

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

Lemma exp_dec (e1 e2: exp) : {e1 = e2} + {e1 <> e2}.
Proof.
  revert e2.
  induction e1, e2.
  all: try (right; discriminate).
  - destruct (const_dec c c0) as [c_c0 |].
    + left.
      rewrite c_c0.
      reflexivity.
    + right.
      inversion 1.
      contradiction.
  - destruct (binder_dec b b0) as [b_b0 |].
    + left.
      rewrite b_b0.
      reflexivity.
    + right.
      inversion 1.
      contradiction.
  - destruct (binder_dec b b0) as [b_b0 |].
    + left.
      rewrite b_b0.
      reflexivity.
    + right.
      inversion 1.
      contradiction.
  - destruct (unop_dec u u0) as [u_u0 |].
    2: {
      right.
      inversion 1.
      contradiction.
    }
    destruct (IHe1 e2) as [e1_e2 |].
    2: {
      right.
      inversion 1.
      contradiction.
    }
    left.
    rewrite u_u0, e1_e2.
    reflexivity.
  - destruct (binop_dec b b0) as [b_b0 |].
    2: {
      right.
      inversion 1.
      contradiction.
    }
    destruct (IHe1_1 e2_1) as [e11_e21 |].
    2: {
      right.
      inversion 1.
      contradiction.
    }
    destruct (IHe1_2 e2_2) as [e12_e22 |].
    2: {
      right.
      inversion 1.
      contradiction.
    }
    left.
    rewrite b_b0, e11_e21, e12_e22.
    reflexivity.
  - destruct (IHe1_1 e2_1) as [e11_e21 |].
    2: {
      right.
      inversion 1.
      contradiction.
    }
    destruct (IHe1_2 e2_2) as [e12_e22 |].
    2: {
      right.
      inversion 1.
      contradiction.
    }
    destruct (IHe1_3 e2_3) as [e13_e23 |].
    2: {
      right.
      inversion 1.
      contradiction.
    }
    left.
    rewrite e11_e21, e12_e22, e13_e23.
    reflexivity.
Defined.

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

Lemma exp_eqb_eq (e1 e2: exp):
  exp_eqb e1 e2 = true <-> e1 = e2.
Proof.
  split.
  - intro H.
    revert e2 H.
    induction e1 as [ c1 | b1 | b1 | op1 e1 IH | op1 e11 IH1 e12 IH2 | e11 IH1 e12 IH2 e13 IH3 ]; intros e2 H.
    all: destruct e2; try inversion H.
    + apply const_eqb_eq in H1.
      subst.
      reflexivity.
    + apply binder_eqb_eq in H1.
      subst.
      reflexivity.
    + apply binder_eqb_eq in H1.
      subst.
      reflexivity.
    + apply andb_prop in H1 as [ H1 H2 ].
      apply unop_eqb_eq in H1.
      apply IH in H2.
      rewrite H1, H2.
      reflexivity.
    + apply andb_prop in H1 as [ H1 H2 ].
      apply andb_prop in H1 as [ H3 H1 ].
      apply IH1 in H1.
      apply IH2 in H2.
      apply binop_eqb_eq in H3.
      rewrite H1, H2, H3.
      reflexivity.
    + apply andb_prop in H1 as [ H1 H3 ].
      apply andb_prop in H1 as [ H1 H2 ].
      apply IH1 in H1.
      apply IH2 in H2.
      apply IH3 in H3.
      rewrite H1, H2, H3.
      reflexivity.
  - intro.
    subst.
    apply exp_eqb_refl.
Qed.

Definition equation_eqb (eq1 eq2: equation): bool :=
  (fst eq1 =? fst eq2) && (exp_eqb (snd eq1) (snd eq2)).

Lemma equation_dec (e1 e2: equation) : { e1 = e2 } + {e1 <> e2}.
Proof.
  destruct e1 as [ e1_name e1_exp].
  destruct e2 as [e2_name e2_exp ].
  pose proof (PeanoNat.Nat.eq_dec e1_name e2_name) as H.
  destruct H.
  2: {
    right.
    inversion 1.
    contradiction.
  }

  destruct (exp_dec e1_exp e2_exp).
  2: {
    right.
    inversion 1.
    contradiction.
  }

  left.
  subst.
  reflexivity.
Defined.

Lemma equation_eqb_refl (eq: equation):
  equation_eqb eq eq = true.
Proof.
  destruct eq as (i, e).
  apply andb_true_intro.
  split.
  - apply PeanoNat.Nat.eqb_refl.
  - apply exp_eqb_refl.
Qed.

Lemma equation_eqb_eq (eq1 eq2: equation):
  equation_eqb eq1 eq2 = true <-> eq1 = eq2.
Proof.
  split.
  - intro H.
    destruct eq1, eq2.
    apply andb_prop in H as [ H1 H2 ].
    apply PeanoNat.Nat.eqb_eq in H1.
    apply exp_eqb_eq in H2.
    simpl in H1, H2.
    rewrite H1, H2.
    reflexivity.
  - intro.
    subst.
    apply equation_eqb_refl.
Qed.

Lemma equation_eqb_to_eq (eq1 eq2: equation):
  equation_eqb eq1 eq2 = true -> eq1 = eq2.
Proof.
  apply equation_eqb_eq.
Qed.

Lemma equation_eq_to_eqb (eq1 eq2: equation):
  eq1 = eq2 -> equation_eqb eq1 eq2 = true.
Proof.
  intros H.
  rewrite H.
  apply equation_eqb_refl.
Qed.
