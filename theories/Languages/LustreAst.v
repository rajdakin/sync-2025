Set Default Goal Selector "!".

From Reactive.Datatypes Require Dict Result Stream.
From Reactive.Languages Require Import Semantics.

From Stdlib Require Import Permutation String ZArith.

Definition binder := string.

Inductive const: Type :=
  | CBool: bool -> const
  | CInt: Z -> const.

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
  | EConst: Result.location -> const -> exp
  | EVar: Result.location -> binder -> exp
  | EUnop: Result.location -> unop -> exp -> exp
  | EBinop: Result.location -> binop -> exp -> exp -> exp
  | EIfte: Result.location -> exp -> exp -> exp -> exp.

Definition equation: Set := binder * exp.


Record node := mk_node {
  n_loc: Result.location;
  n_name: string;
  n_in: list (binder * type);
  n_out: list (binder * type);
  n_locals: list (binder * type);
  n_body: list (Result.location * equation);
}.


Definition node_eq (n1 n2: node) :=
  n_name n1 = n_name n2 /\
  Permutation (n_in n1) (n_in n2) /\
  Permutation (n_out n1) (n_out n2) /\
  Permutation (n_locals n1) (n_locals n2) /\
  Permutation (n_body n1) (n_body n2).

Definition name_dec := String.string_dec.


(** ** Equality of binders *)
Definition binder_eqb (x y: binder): bool := (x =? y)%string.

Lemma binder_eqb_eq (x y: binder):
  binder_eqb x y = true <-> x = y.
Proof.
  apply String.eqb_eq.
Qed.

Lemma binder_dec (x y: binder): {x = y} + {x <> y}.
Proof.
  exact (string_dec x y).
Defined.

Lemma binder_eqb_refl (b: binder):
  binder_eqb b b = true.
Proof.
  apply String.eqb_refl.
Qed.

Lemma binder_eqb_to_eq (x y : binder): binder_eqb x y = true -> x = y.
Proof.
  unfold binder_eqb, andb.
  destruct (x =? y)%string eqn:Heq; [| discriminate ].

  now rewrite String.eqb_eq in Heq.
Qed.

Lemma binder_eq_to_eqb (x y : binder): x = y -> binder_eqb x y = true.
Proof.
  unfold binder_eqb.
  intros ->.
  apply String.eqb_refl.
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
    | CBool b1, CBool b2 => Bool.eqb b1 b2
    | CInt n1, CInt n2 => Z.eqb n1 n2
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
  - apply Z.eqb_eq in H.
    subst.
    reflexivity.
  - inversion H.
    subst.
    apply Z.eqb_refl.
Qed.

Lemma const_eqb_refl (c: const):
  const_eqb c c = true.
Proof.
  apply const_eqb_eq.
  reflexivity.
Qed.

Lemma const_dec (c1 c2: const) : {c1 = c2} + {c1 <> c2}.
Proof.
  destruct c1, c2.
  all: try (right; discriminate).
  - destruct (Bool.bool_dec b b0).
    + left. rewrite e. reflexivity.
    + right. inversion 1. contradiction.
  - destruct (Z.eq_dec z z0).
    + left. rewrite e. reflexivity.
    + right. inversion 1. contradiction.
Defined.

Fixpoint exp_eqb (e1 e2: exp): bool :=
  match e1, e2 with
    | EConst _ c1, EConst _ c2 => const_eqb c1 c2
    | EVar _ b1, EVar _ b2 => binder_eqb b1 b2
    | EUnop _ op1 e1, EUnop _ op2 e2 =>
      (unop_eqb op1 op2) && (exp_eqb e1 e2)
    | EBinop _ op1 e11 e12, EBinop _ op2 e21 e22 =>
      (binop_eqb op1 op2) && (exp_eqb e11 e21) && (exp_eqb e12 e22)
    | EIfte _ e11 e12 e13, EIfte _ e21 e22 e23 =>
      (exp_eqb e11 e21) && (exp_eqb e12 e22) && (exp_eqb e13 e23)
    | _, _ => false
  end.

Inductive exp_eq : exp -> exp -> Prop :=
  | EeqConst : forall {l1 l2 c}, exp_eq (EConst l1 c) (EConst l2 c)
  | EeqVar : forall {l1 l2 b}, exp_eq (EVar l1 b) (EVar l2 b)
  | EeqUnop : forall {l1 l2 op e1 e2}, exp_eq e1 e2 -> exp_eq (EUnop l1 op e1) (EUnop l2 op e2)
  | EeqBinop : forall {l1 l2 op e11 e12 e21 e22}, exp_eq e11 e21 -> exp_eq e12 e22 -> exp_eq (EBinop l1 op e11 e12) (EBinop l2 op e21 e22)
  | EeqIfte : forall {l1 l2 e11 e12 e13 e21 e22 e23},
      exp_eq e11 e21 -> exp_eq e12 e22 -> exp_eq e13 e23 -> exp_eq (EIfte l1 e11 e12 e13) (EIfte l2 e21 e22 e23)
.

Lemma exp_eq_refl : forall e, exp_eq e e.
Proof using.
  intros e; induction e; constructor; assumption.
Qed.

Lemma exp_dec (e1 e2: exp) : {exp_eq e1 e2} + {~ exp_eq e1 e2}.
Proof.
  revert e2.
  induction e1, e2.
  all: try solve [right; inversion 1].
  - destruct (const_dec c c0) as [c_c0 |].
    + left.
      rewrite c_c0.
      constructor.
    + right.
      inversion 1.
      contradiction.
  - destruct (binder_dec b b0) as [b_b0 |].
    + left.
      rewrite b_b0.
      constructor.
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
    rewrite u_u0.
    constructor.
    assumption.
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
    rewrite b_b0.
    constructor; assumption.
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
    constructor; assumption.
Defined.

Lemma exp_eqb_refl (e: exp):
  exp_eqb e e = true.
Proof.
  induction e.
  - apply const_eqb_refl.
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
  exp_eqb e1 e2 = true <-> exp_eq e1 e2.
Proof.
  split.
  - intro H.
    revert e2 H.
    induction e1 as [ l1 c1 | l1 b1 | l1 op1 e1 IH | l1 op1 e11 IH1 e12 IH2 | l1 e11 IH1 e12 IH2 e13 IH3 ]; intros e2 H.
    all: destruct e2; try inversion H.
    + apply const_eqb_eq in H1.
      subst.
      constructor.
    + apply binder_eqb_eq in H1.
      subst.
      constructor.
    + apply andb_prop in H1 as [ H1 H2 ].
      apply unop_eqb_eq in H1.
      apply IH in H2.
      rewrite H1.
      constructor; assumption.
    + apply andb_prop in H1 as [ H1 H2 ].
      apply andb_prop in H1 as [ H3 H1 ].
      apply IH1 in H1.
      apply IH2 in H2.
      apply binop_eqb_eq in H3.
      rewrite H3.
      constructor; assumption.
    + apply andb_prop in H1 as [ H1 H3 ].
      apply andb_prop in H1 as [ H1 H2 ].
      apply IH1 in H1.
      apply IH2 in H2.
      apply IH3 in H3.
      constructor; assumption.
  - intros H.
    induction H.
    1: exact (const_eqb_refl _).
    1: exact (binder_eqb_refl _).
    1: cbn; rewrite IHexp_eq, Bool.andb_true_r; exact (unop_eqb_refl _).
    1: cbn; rewrite IHexp_eq1, IHexp_eq2, !Bool.andb_true_r; exact (binop_eqb_refl _).
    cbn; rewrite IHexp_eq1, IHexp_eq2; exact IHexp_eq3.
Qed.

Definition equation_eqb (eq1 eq2: equation): bool :=
  (fst eq1 =? fst eq2)%string && (exp_eqb (snd eq1) (snd eq2)).

Definition equation_eq : equation -> equation -> Prop := fun eq1 eq2 => (fst eq1 = fst eq2) /\ (exp_eq (snd eq1) (snd eq2)).

Lemma equation_dec (e1 e2: equation) : { equation_eq e1 e2 } + { ~ equation_eq e1 e2 }.
Proof.
  destruct e1 as [ e1_name e1_exp ].
  destruct e2 as [ e2_name e2_exp ].
  pose proof (string_dec e1_name e2_name) as H.
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
  split; [reflexivity|assumption].
Defined.

Lemma equation_eqb_refl (eq: equation):
  equation_eqb eq eq = true.
Proof.
  destruct eq as (i, e).
  apply andb_true_intro.
  split.
  - apply String.eqb_refl.
  - apply exp_eqb_refl.
Qed.

Lemma equation_eqb_eq (eq1 eq2: equation):
  equation_eqb eq1 eq2 = true <-> equation_eq eq1 eq2.
Proof.
  split.
  - intro H.
    destruct eq1, eq2.
    apply andb_prop in H as [ H1 H2 ].
    apply String.eqb_eq in H1.
    apply exp_eqb_eq in H2.
    simpl in H1, H2.
    rewrite H1.
    split; [reflexivity|assumption].
  - destruct eq1 as [i e1], eq2 as [i' e2].
    intros [eq H]; cbn in eq, H; subst i'.
    apply andb_true_intro.
    split.
    1: exact (String.eqb_refl _).
    apply exp_eqb_eq in H.
    exact H.
Qed.

Lemma equation_eqb_to_eq (eq1 eq2: equation):
  equation_eqb eq1 eq2 = true -> equation_eq eq1 eq2.
Proof.
  apply equation_eqb_eq.
Qed.

Lemma equation_eq_to_eqb (eq1 eq2: equation):
  equation_eq eq1 eq2 -> equation_eqb eq1 eq2 = true.
Proof.
  intros H.
  apply equation_eqb_eq.
  exact H.
Qed.
