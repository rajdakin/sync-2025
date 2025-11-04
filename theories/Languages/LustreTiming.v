From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require Lustre.

From Stdlib Require Import Permutation.
From Stdlib.Arith Require Import PeanoNat.

Module Lustre := Lustre.

Definition type := Lustre.type.
Definition TBool := Lustre.TBool.
Definition TInt := Lustre.TInt.
Definition const := Lustre.const.
Definition binder := Lustre.binder.
Definition value := Lustre.value.
Definition binder_ty := Lustre.binder_ty.

Inductive unop: type -> type -> Set :=
  | Uop_not: unop TInt TInt
  | Uop_neg: unop TInt TInt
.

Inductive binop: type -> type -> type -> Set :=
  (** Boolean binop *)
  | Bop_and: binop TBool TBool TBool
  | Bop_or: binop TBool TBool TBool
  | Bop_xor: binop TBool TBool TBool

  (** Arithmetic binop *)
  | Bop_plus: binop TInt TInt TInt
  | Bop_minus: binop TInt TInt TInt
  | Bop_mult: binop TInt TInt TInt
  | Bop_div: binop TInt TInt TInt

  (** Relational binop *)
  | Bop_eq: binop TInt TInt TBool
  | Bop_neq: binop TInt TInt TBool
  | Bop_le: binop TInt TInt TBool
  | Bop_lt: binop TInt TInt TBool
  | Bop_ge: binop TInt TInt TBool
  | Bop_gt: binop TInt TInt TBool
.

Inductive raw_exp : type -> Set :=
  | Raw_EConst: forall {ty}, const ty -> raw_exp ty
  | Raw_EVar: forall (b: binder), raw_exp (binder_ty b)
  | Raw_EUnop: forall {tin tout}, unop tin tout -> raw_exp tin -> raw_exp tout
  | Raw_EBinop: forall {ty1 ty2 tout}, binop ty1 ty2 tout -> raw_exp ty1 -> raw_exp ty2 -> raw_exp tout
  | Raw_EIfte: forall {t}, raw_exp TBool -> raw_exp t -> raw_exp t -> raw_exp t
  | Raw_EPre: forall {ty}, raw_exp ty -> raw_exp ty
  | Raw_EArrow: forall {ty}, raw_exp ty -> raw_exp ty -> raw_exp ty
.

Inductive comb_exp : type -> Set :=
  | EConst: forall {ty}, const ty -> comb_exp ty
  | EVar: forall (b: binder), comb_exp (binder_ty b)
  | EUnop: forall {tin tout}, unop tin tout -> comb_exp tin -> comb_exp tout
  | EBinop: forall {ty1 ty2 tout}, binop ty1 ty2 tout -> comb_exp ty1 -> comb_exp ty2 -> comb_exp tout
  | EIfte: forall {t}, comb_exp TBool -> comb_exp t -> comb_exp t -> comb_exp t
.

Definition equation : Type := ident * { ty : type & comb_exp ty }.
Definition equation_dest (eq : equation) : ident * type := (fst eq, projT1 (snd eq)).

Record node := mk_node {
  n_loc: Result.location;
  n_name: string;

  n_in: list binder;
  n_out: list binder;
  n_locals: list binder; (* Also includes additionally created binders for pre *)
  n_pre: list equation; (* Happens before n_init and n_step *)
  n_init: list equation;
  n_step: list equation;

  n_vars: list binder := n_in ++ n_out ++ n_locals;
  n_assigned_vars_init: list binder := map equation_dest n_init;
  n_assigned_vars_pre: list binder := map equation_dest n_pre;
  n_assigned_vars_step: list binder := map equation_dest n_step;

  n_init_vars_all_assigned: Permutation (n_assigned_vars_pre ++ n_assigned_vars_init) (n_out ++ n_locals);
  n_step_vars_all_assigned: Permutation (n_assigned_vars_pre ++ n_assigned_vars_step) (n_out ++ n_locals);

  n_vars_unique: NoDup (map fst n_vars);

  n_seed: ident;
  n_seed_always_fresh: forall n, ~In (iter n next_ident n_seed) (map fst n_vars);
}.

Definition freshness (seed: ident) (vars: list binder) := forall n, ~In (iter n next_ident seed) (map fst vars).


(* Translation from raw expressions to combinatorial expressions, extracting pre and arrow *)

Fixpoint raw_to_comb {ty} (exp: raw_exp ty) (seed: ident): (
    comb_exp ty (* init *)
    * comb_exp ty (* step *)
    * ident (* New identifier origin *)
    * (list binder) (* Variables created for pre *)
    * (list equation) (* pre equations *)
    (* Equations to merge with the regular equations *)
    (* for init: 
      prex = undef (a variable initialised later)

      for step:
      prex = eqx (eqx being updated later with the current values)
    *)
    (* Equations NOT to be merged, but can be ordered separately *)
    * (list equation) (* init_post equations *)
    * (list equation) (* step_post equations *)
  ) :=
  match exp with
    | Raw_EConst c => (EConst c, EConst c, seed, [], [], [], [])
    | Raw_EVar v => (EVar v, EVar v, seed, [], [], [], [])
    | Raw_EUnop u e => let '(ei, es, orig, binders, eqs_pre, init_post, step_post) := raw_to_comb e seed in
      (EUnop u ei, EUnop u es, orig, binders, eqs_pre, init_post, step_post)
    | Raw_EBinop b e1 e2 => let '(ei1, es1, orig1, binders1, eqs_pre1, init_post1, step_post1) := raw_to_comb e1 seed in
      let '(e2i, e2s, orig2, binders2, eqs_pre2, init_post2, step_post2) := raw_to_comb e2 orig1 in
        (EBinop b ei1 e2i, EBinop b es1 e2s, orig2, binders1 ++ binders2, eqs_pre1 ++ eqs_pre2, init_post1 ++ init_post2, step_post1 ++ step_post2)
    | Raw_EIfte e1 e2 e3 => let '(ei1, es1, orig1, binders1, eqs_pre1, init_post1, step_post1) := raw_to_comb e1 seed in
      let '(e2i, e2s, orig2, binders2, eqs_pre2, init_post2, step_post2) := raw_to_comb e2 orig1 in
        let '(e3i, e3s, orig3, binders3, eqs_pre3, init_post3, step_post3) := raw_to_comb e3 orig2 in
        (EIfte ei1 e2i e3i, EIfte es1 e2s e3s, orig3, binders1 ++ binders2 ++ binders3, eqs_pre1 ++ eqs_pre2 ++ eqs_pre3, init_post1 ++ init_post2 ++ init_post3, step_post1 ++ step_post2 ++ step_post3)
    | @Raw_EPre t e => let '(ei, es, ident_pre, binders, eqs_pre, init_post, step_post) := raw_to_comb e seed in
      let ident_eq := next_ident ident_pre in
        let next_orig := next_ident ident_eq in
          let pre_var := (ident_pre, t) in
            let eq_var := (ident_eq, t) in
              (
                EVar pre_var,
                EVar pre_var,
                next_orig,
                pre_var::eq_var::binders,
                (ident_pre, existT comb_exp t (EVar eq_var))::eqs_pre,
                (ident_eq, existT _ t ei)::init_post,
                (ident_eq, existT _ t es)::step_post
              )
    | Raw_EArrow e1 e2 => let '(ei1, es1, orig1, binders1, eqs_pre1, init_post1, step_post1) := raw_to_comb e1 seed in
      let '(e2i, e2s, orig2, binders2, eqs_pre2, init_post2, step_post2) := raw_to_comb e2 orig1 in
        (ei1, e2s, orig2, binders1 ++ binders2, eqs_pre1 ++ eqs_pre2, init_post1 ++ init_post2, step_post1 ++ step_post2)
  end.

(** Properties *)
Lemma freshness_fusion {seed: ident} {vars1 vars2: list binder}:
  freshness seed vars1 -> freshness seed vars2 -> freshness seed (vars1 ++ vars2).
Proof.
  intros fresh1 fresh2 n.
  specialize (fresh1 n).
  specialize (fresh2 n).
  rewrite map_app.
  intro isin.
  apply in_app_or in isin.
  tauto.
Qed.

Lemma freshness_later {seed1 seed2: ident} {n: nat} {vars: list binder}:
  seed2 = iter n next_ident seed1 -> freshness seed1 vars -> freshness seed2 vars.
Proof.
  intros fresh1 isiter.
  intro m.
  specialize (isiter (m + n)).
  rewrite Nat.iter_add in isiter.
  rewrite <- fresh1 in isiter.
  assumption.
Qed.

Lemma freshness_later_e {seed1 seed2: ident} {vars: list binder}:
  (exists n, seed2 = iter n next_ident seed1) -> freshness seed1 vars -> freshness seed2 vars.
Proof.
  intros [n isiter].
  apply (freshness_later isiter).
Qed.

Lemma raw_to_comb_nextseed {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post)
  -> exists n, seed' = iter n next_ident seed.
Proof.
  intro eqe.
  induction exp in ei, es, seed, seed', pre_binders, pre_eqs, init_post, step_post, eqe.
  - injection eqe as <- <- <- <- <- <- <-.
    exists 0.
    reflexivity.
  - injection eqe as <- <- <- <- <- <- <-.
    exists 0.
    reflexivity.
  - simpl in eqe.
    destruct (raw_to_comb exp seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    apply (IHexp _ _ _ _ _ _ _ _ unfold1).
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    destruct IHexp1 as [n1 IHexp1].
    destruct IHexp2 as [n2 IHexp2].
    rewrite IHexp1 in IHexp2.
    rewrite <- Nat.iter_add in IHexp2.
    exists (n2 + n1).
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    destruct (raw_to_comb exp3 seed2) as [[[[[[ei3 es3] seed3] binders3] pre_eqs3] init_post3] step_post3] eqn: unfold3.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    specialize (IHexp3 _ _ _ _ _ _ _ _ unfold3).
    destruct IHexp1 as [n1 IHexp1].
    destruct IHexp2 as [n2 IHexp2].
    destruct IHexp3 as [n3 IHexp3].
    rewrite IHexp1 in IHexp2.
    rewrite IHexp2 in IHexp3.
    do 2 rewrite <- Nat.iter_add in IHexp3.
    exists (n3 + n2 + n1).
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    destruct IHexp as [n IHexp].
    exists (S (S n)).
    simpl.
    do 2 f_equal.
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    destruct IHexp1 as [n1 IHexp1].
    destruct IHexp2 as [n2 IHexp2].
    rewrite IHexp1 in IHexp2.
    rewrite <- Nat.iter_add in IHexp2.
    exists (n2 + n1).
    assumption.
Qed.

Lemma freshness_raw_to_comb {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post)
  -> freshness seed' pre_binders.
Proof.
  intros eqe.
  induction exp in ei, es, seed, seed', pre_binders, pre_eqs, init_post, step_post, eqe.
  - injection eqe as <- <- <- <- <- <- <-.
    intro n.
    tauto.
  - injection eqe as <- <- <- <- <- <- <-.
    intro n.
    tauto.
  - simpl in eqe.
    destruct (raw_to_comb exp seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    apply (IHexp _ _ _ _ _ _ _ _ unfold1).
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    assert (nextseed := raw_to_comb_nextseed unfold2).
    apply (freshness_later_e nextseed) in IHexp1.
    apply (freshness_fusion IHexp1 IHexp2).
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    destruct (raw_to_comb exp3 seed2) as [[[[[[ei3 es3] seed3] binders3] pre_eqs3] init_post3] step_post3] eqn: unfold3.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    specialize (IHexp3 _ _ _ _ _ _ _ _ unfold3).
    assert (nextseed1 := raw_to_comb_nextseed unfold2).
    assert (nextseed2 := raw_to_comb_nextseed unfold3).
    apply (freshness_later_e nextseed1) in IHexp1.
    apply (freshness_later_e nextseed2) in IHexp1.
    apply (freshness_later_e nextseed2) in IHexp2.
    apply (freshness_fusion IHexp1 (freshness_fusion IHexp2 IHexp3)).
  - simpl in eqe.
    destruct (raw_to_comb exp) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    intros n isin.
    rewrite <- !PeanoNat.Nat.iter_succ_r in isin.
    rewrite !map_cons in isin.
    unfold fst at 1 2 in isin.
    destruct isin as [f | [f | isin]].
    + apply ident_diff in f.
      assumption.
    + rewrite Nat.iter_succ_r in f.
      apply ident_diff in f.
      assumption.
    + specialize (IHexp (S (S n))).
      contradiction.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    assert (nextseed := raw_to_comb_nextseed unfold2).
    apply (freshness_later_e nextseed) in IHexp1.
    apply (freshness_fusion IHexp1 IHexp2).
Qed.
