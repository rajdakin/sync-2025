From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require Lustre.

From Stdlib Require Import Permutation.

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

Fixpoint raw_to_comb {ty} (exp: raw_exp ty) (ident_origin: ident) (pre_binders: list binder) (pre_equations init_post_equations step_post_equations: list equation): (
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
    | Raw_EConst c => (EConst c, EConst c, ident_origin, pre_binders, pre_equations, init_post_equations, step_post_equations)
    | Raw_EVar v => (EVar v, EVar v, ident_origin, pre_binders, pre_equations, init_post_equations, step_post_equations)
    | Raw_EUnop u e => let '(ei, es, orig, binders, equations_pre, init_equations_post, step_equations_post) := raw_to_comb_aux e ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      (EUnop u ei, EUnop u es, orig, binders, equations_pre, init_equations_post, step_equations_post)
    | Raw_EBinop b e1 e2 => let '(e1i, e1s, orig1, binders1, equations_pre1, init_equations_post1, step_equations_post1) := raw_to_comb_aux e1 ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      let '(e2i, e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2) := raw_to_comb_aux e2 orig1 binders1 equations_pre1 init_equations_post1 step_equations_post1 in
        (EBinop b e1i e2i, EBinop b e1s e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2)
    | Raw_EIfte e1 e2 e3 => let '(e1i, e1s, orig1, binders1, equations_pre1, init_equations_post1, step_equations_post1) := raw_to_comb_aux e1 ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      let '(e2i, e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2) := raw_to_comb_aux e2 orig1 binders1 equations_pre1 init_equations_post1 step_equations_post1 in
        let '(e3i, e3s, orig3, binders3, equations_pre3, init_equations_post3, step_equations_post3) := raw_to_comb_aux e3 orig2 binders2 equations_pre2 init_equations_post2 step_equations_post2 in
        (EIfte e1i e2i e3i, EIfte e1s e2s e3s, orig3, binders3, equations_pre3, init_equations_post3, step_equations_post3)
    | @Raw_EPre t e => let '(ei, es, ident_pre, binders, equations_pre, init_equations_post, step_equations_post) := raw_to_comb_aux e ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      let ident_eq := next_ident ident_pre in
        let next_orig := next_ident ident_eq in
          let pre_var := (ident_pre, t) in
            let eq_var := (ident_eq, t) in
              (
                EVar pre_var,
                EVar pre_var,
                next_orig,
                pre_var::eq_var::binders,
                (ident_pre, existT comb_exp t (EVar eq_var))::equations_pre,
                (ident_eq, existT _ t ei)::init_equations_post,
                (ident_eq, existT _ t es)::step_equations_post
              )
    | Raw_EArrow e1 e2 => let '(e1i, e1s, orig1, binders1, equations_pre1, init_equations_post1, step_equations_post1) := raw_to_comb_aux e1 ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      let '(e2i, e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2) := raw_to_comb_aux e2 orig1 binders1 equations_pre1 init_equations_post1 step_equations_post1 in
        (e1i, e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2)
  end.

Definition raw_to_comb {ty} (exp: raw_exp ty) (ident_origin: ident): (
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
  raw_to_comb_aux exp ident_origin [] [] [] [].

(** Properties *)

Lemma freshness_raw_to_comb {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed0 seed1: ident} {binders pre_binders0 pre_binders1: list binder} {pre_eqs0 pre_eqs1 init_post0 init_post1 step_post0 step_post1: list equation}:
  raw_to_comb exp seed0 pre_binders0 pre_eqs0 init_post0 step_post0 = (ei, es, seed1, pre_binders1, pre_eqs1, init_post1, step_post1)
  -> freshness seed0 (pre_binders0 ++ binders)
  -> freshness seed1 (pre_binders1 ++ binders).
Proof.
  intros eqe isfresh.
  induction exp in ei, es, seed0, seed1, pre_binders0, pre_binders1, pre_eqs0, pre_eqs1, init_post0, init_post1, step_post0, step_post1, eqe, isfresh.
  - injection eqe as <- <- <- <- <- <- <-.
    assumption.
  - injection eqe as <- <- <- <- <- <- <-.
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp seed0 pre_binders0 pre_eqs0 init_post0 step_post0) as [[[[[[ei_1 es_1] seed_1] binders_1] pre_eqs_1] init_post_1] step_post_1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    apply (IHexp _ _ _ _ _ _ _ _ _ _ _ _ unfold1 isfresh).
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed0 pre_binders0 pre_eqs0 init_post0 step_post0) as [[[[[[ei_1 es_1] seed_1] binders_1] pre_eqs_1] init_post_1] step_post_1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed_1 binders_1 pre_eqs_1 init_post_1 step_post_1) as [[[[[[ei_2 es_2] seed_2] binders_2] pre_eqs_2] init_post_2] step_post_2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ _ _ _ _ unfold1 isfresh).
    specialize (IHexp2 _ _ _ _ _ _ _ _ _ _ _ _ unfold2 IHexp1).
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed0 pre_binders0 pre_eqs0 init_post0 step_post0) as [[[[[[ei_1 es_1] seed_1] binders_1] pre_eqs_1] init_post_1] step_post_1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed_1 binders_1 pre_eqs_1 init_post_1 step_post_1) as [[[[[[ei_2 es_2] seed_2] binders_2] pre_eqs_2] init_post_2] step_post_2] eqn: unfold2.
    destruct (raw_to_comb exp3 seed_2 binders_2 pre_eqs_2 init_post_2 step_post_2) as [[[[[[ei_3 es_3] seed_3] binders_3] pre_eqs_3] init_post_3] step_post_3] eqn: unfold3.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ _ _ _ _ unfold1 isfresh).
    specialize (IHexp2 _ _ _ _ _ _ _ _ _ _ _ _ unfold2 IHexp1).
    specialize (IHexp3 _ _ _ _ _ _ _ _ _ _ _ _ unfold3 IHexp2).
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp seed0 pre_binders0 pre_eqs0 init_post0 step_post0) as [[[[[[ei_1 es_1] seed_1] binders_1] pre_eqs_1] init_post_1] step_post_1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ _ _ _ _ unfold1 isfresh).
    intros n isin.
    rewrite map_app in isin.
    apply in_app_or in isin.
    specialize (IHexp (S (S n))).
    do 2 rewrite map_cons in isin.
    unfold fst at 1 2 in isin.
    rewrite map_app in IHexp.
    rewrite in_app_iff in IHexp.

    rewrite <- !PeanoNat.Nat.iter_succ_r in isin.
    destruct isin as [[is1 | [is2 | isin]] | isbinders].
    + symmetry in is1.
      apply ident_diff in is1.
      assumption.
    + symmetry in is2.
      unfold next_ident at 2 in is2.
      apply PeanoNat.Nat.succ_inj in is2.
      apply ident_diff in is2.
      assumption.
    + apply IHexp.
      left.
      assumption.
    + apply IHexp.
      right.
      assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed0 pre_binders0 pre_eqs0 init_post0 step_post0) as [[[[[[ei_1 es_1] seed_1] binders_1] pre_eqs_1] init_post_1] step_post_1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed_1 binders_1 pre_eqs_1 init_post_1 step_post_1) as [[[[[[ei_2 es_2] seed_2] binders_2] pre_eqs_2] init_post_2] step_post_2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ _ _ _ _ unfold1 isfresh).
    specialize (IHexp2 _ _ _ _ _ _ _ _ _ _ _ _ unfold2 IHexp1).
    intros n isin.
    specialize (IHexp2 n).
    contradiction.
Qed.
