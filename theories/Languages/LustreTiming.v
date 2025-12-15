Set Default Goal Selector "!".

From Reactive.Props Require Import Freshness Identifier.
From Reactive.Languages Require Lustre.
From Reactive.Languages Require Import Semantics.

From Stdlib Require Import Nat List Permutation String.
From Stdlib.Arith Require Import PeanoNat.

Import ListNotations.

Module Lustre := Lustre.

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
  | Raw_EConst: Result.location -> forall {ty}, const ty -> raw_exp ty
  | Raw_EVar: Result.location -> forall (b: binder), raw_exp (binder_ty b)
  | Raw_EUnop: Result.location -> forall {tin tout}, unop tin tout -> raw_exp tin -> raw_exp tout
  | Raw_EBinop: Result.location -> forall {ty1 ty2 tout}, binop ty1 ty2 tout -> raw_exp ty1 -> raw_exp ty2 -> raw_exp tout
  | Raw_EIfte: Result.location -> forall {t}, raw_exp TBool -> raw_exp t -> raw_exp t -> raw_exp t
  | Raw_EPre: Result.location -> forall {ty}, raw_exp ty -> raw_exp ty
  | Raw_EArrow: Result.location -> forall {ty}, raw_exp ty -> raw_exp ty -> raw_exp ty
.

Inductive comb_exp : type -> Set :=
  | EConst: Result.location -> forall {ty}, const ty -> comb_exp ty
  | EVar: Result.location -> forall (b: binder), comb_exp (binder_ty b)
  | EUnop: Result.location -> forall {tin tout}, unop tin tout -> comb_exp tin -> comb_exp tout
  | EBinop: Result.location -> forall {ty1 ty2 tout}, binop ty1 ty2 tout -> comb_exp ty1 -> comb_exp ty2 -> comb_exp tout
  | EIfte: Result.location -> forall {t}, comb_exp TBool -> comb_exp t -> comb_exp t -> comb_exp t
.

Inductive well_timed: nat -> forall {ty}, raw_exp ty -> Prop :=
  | TimedConst: forall l (n: nat) {ty} (c: const ty), well_timed n (Raw_EConst l c)
  | TimedVar: forall l (n: nat) (b: binder), well_timed n (Raw_EVar l b)
  | TimedUnop: forall l (n: nat) {tin tout} (u: unop tin tout) (e: raw_exp tin), well_timed n e -> well_timed n (Raw_EUnop l u e)
  | TimedBinop: forall l (n: nat) {ty1 ty2 tout} (b: binop ty1 ty2 tout) (e1: raw_exp ty1) (e2: raw_exp ty2), well_timed n e1 -> well_timed n e2 -> well_timed n (Raw_EBinop l b e1 e2)
  | TimedIfte: forall l (n: nat) {ty} (c: raw_exp TBool) (e1 e2: raw_exp ty), well_timed n c -> well_timed n e1 -> well_timed n e2 -> well_timed n (Raw_EIfte l c e1 e2)
  | TimedPre: forall l (n: nat) {ty} (e: raw_exp ty), well_timed n e -> well_timed (S n) (Raw_EPre l e)
  | TimedArrow_O: forall l {ty} (e1 e2: raw_exp ty), well_timed 0 e1 -> well_timed 0 (Raw_EArrow l e1 e2)
  | TimedArrow_S: forall l (n: nat) {ty} (e1 e2: raw_exp ty), well_timed (S n) e2 -> well_timed (S n) (Raw_EArrow l e1 e2)
.

Definition equation : Type := ident * { ty : type & comb_exp ty }.
Definition equation_dest (eq : equation) : ident * type := (fst eq, projT1 (snd eq)).

Lemma timed_exp {ty} (vname: string) (vid: ident) (loc: Result.location) (n: nat) (exp: raw_exp ty):
  Result.t type (well_timed n exp).
Proof.
  induction exp as [ l | l | l tin tout u exp IH | l ty1 ty2 tout b e1 IH1 e2 IH2 | l t ec IHc e1 IH1 e2 IH2 | l ty exp IH | l ty e1 IH1 e2 IH2] in n |- *.
  - constructor 1.
    constructor.
  - constructor 1.
    constructor.
  - specialize (IH n).
    destruct IH as [IH | err].
    2: constructor 2; exact err.
    constructor 1.
    constructor.
    apply IH.
  - specialize (IH1 n).
    specialize (IH2 n).
    destruct IH1 as [IH1 | err1].
    + destruct IH2 as [IH2 | err2].
      * constructor 1.
        constructor.
        all: assumption.
      * constructor 2.
        exact err2.
    + destruct IH2 as [_ | err2].
      all: constructor 2.
      * exact err1.
      * exact (err1 ++ err2).
  - specialize (IHc n).
    specialize (IH1 n).
    specialize (IH2 n).
    destruct IHc as [IHc | errc].
    + destruct IH1 as [IH1 | err1].
      * destruct IH2 as [IH2 | err2].
        -- constructor 1.
           constructor.
           all: assumption.
        -- constructor 2.
           exact err2.
      * destruct IH2 as [IH2 | err2].
        all: constructor 2.
        1: exact err1.
        exact (err1 ++ err2).
    + destruct IH1 as [IH1 | err1].
      * destruct IH2 as [IH2 | err2].
        all: constructor 2.
        1: exact errc.
        exact (errc ++ err2).
      * destruct IH2 as [IH2 | err2].
        all: constructor 2.
        1: exact (errc ++ err1).
        exact (errc ++ err1 ++ err2).
  - destruct n.
    + constructor 2.
      exact [(loc, (Result.InvalidTiming vname vid ty))].
    + specialize (IH n).
      destruct IH as [IH | err].
      2: constructor 2; exact err.
      constructor 1.
      constructor.
      apply IH.
  - destruct n.
    + specialize (IH1 0).
      destruct IH1 as [IH1 | err].
      * constructor 1.
        constructor.
        assumption.
      * constructor 2.
        exact err.
    + specialize (IH2 (S n)).
      destruct IH2 as [IH2 | err].
      * constructor 1.
        constructor.
        assumption.
      * constructor 2.
        exact err.
Defined.

Lemma timed_exp_gt {ty} (vname: string) (vid: ident) (loc: Result.location) (n: nat) (exp: raw_exp ty):
  Result.t type (forall n', n <= n' -> well_timed n' exp).
Proof.
  induction exp as [ l | l | l tin tout u exp IH | l ty1 ty2 tout b e1 IH1 e2 IH2 | l t ec IHc e1 IH1 e2 IH2 | l ty exp IH | l ty e1 IH1 e2 IH2] in n |- *.
  - constructor 1.
    intros.
    constructor.
  - constructor 1.
    intros.
    constructor.
  - specialize (IH n).
    destruct IH as [IH | err].
    2: constructor 2; exact err.
    constructor 1.
    intros n' isless.
    specialize (IH _ isless).
    constructor.
    apply IH.
  - specialize (IH1 n).
    specialize (IH2 n).
    destruct IH1 as [IH1 | err1].
    + destruct IH2 as [IH2 | err2].
      * constructor 1.
        intros n' isless.
        specialize (IH1 _ isless).
        specialize (IH2 _ isless).
        constructor.
        all: assumption.
      * constructor 2.
        exact err2.
    + destruct IH2 as [_ | err2].
      all: constructor 2.
      * exact err1.
      * exact (err1 ++ err2).
  - specialize (IHc n).
    specialize (IH1 n).
    specialize (IH2 n).
    destruct IHc as [IHc | errc].
    + destruct IH1 as [IH1 | err1].
      * destruct IH2 as [IH2 | err2].
        -- constructor 1.
           intros n' isless.
           specialize (IHc _ isless).
           specialize (IH1 _ isless).
           specialize (IH2 _ isless).
           constructor.
           all: assumption.
        -- constructor 2.
           exact err2.
      * destruct IH2 as [IH2 | err2].
        all: constructor 2.
        1: exact err1.
        exact (err1 ++ err2).
    + destruct IH1 as [IH1 | err1].
      * destruct IH2 as [IH2 | err2].
        all: constructor 2.
        1: exact errc.
        exact (errc ++ err2).
      * destruct IH2 as [IH2 | err2].
        all: constructor 2.
        1: exact (errc ++ err1).
        exact (errc ++ err1 ++ err2).
  - destruct n.
    + constructor 2.
      exact [(loc, (Result.InvalidTiming vname vid ty))].
    + specialize (IH n).
      destruct IH as [IH | err].
      2: constructor 2; exact err.
      constructor 1.
      intros n' isless.
      destruct n' as [|n'].
      1: inversion isless.
      apply le_S_n in isless.
      constructor.
      apply IH.
      assumption.
  - specialize (IH2 n).
    destruct n as [| n].
    + assert (timed_1 := timed_exp vname vid loc 0 e1).
      destruct timed_1 as [timed_1 | err1].
      * destruct IH2 as [IH2 | err2].
        2: constructor 2; exact err2.
        constructor 1.
        intros n' isless.
        specialize (IH2 _ isless).
        destruct n' as [| n'].
        all: constructor.
        all: assumption.
      * destruct IH2 as [IH2 | err2].
        all: constructor 2.
        1: exact err1.
        exact (err1 ++ err2).
    + destruct IH2 as [IH2 | err2].
      2: constructor 2; exact err2.
      constructor 1.
      intros n' isless.
      destruct n' as [|n'].
      1: inversion isless.
      constructor.
      apply IH2.
      assumption.
Defined.

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
    | Raw_EConst l c => (EConst l c, EConst l c, seed, [], [], [], [])
    | Raw_EVar l v => (EVar l v, EVar l v, seed, [], [], [], [])
    | Raw_EUnop l u e => let '(ei, es, orig, binders, eqs_pre, init_post, step_post) := raw_to_comb e seed in
      (EUnop l u ei, EUnop l u es, orig, binders, eqs_pre, init_post, step_post)
    | Raw_EBinop l b e1 e2 => let '(ei1, es1, orig1, binders1, eqs_pre1, init_post1, step_post1) := raw_to_comb e1 seed in
      let '(e2i, e2s, orig2, binders2, eqs_pre2, init_post2, step_post2) := raw_to_comb e2 orig1 in
        (EBinop l b ei1 e2i, EBinop l b es1 e2s, orig2, binders1 ++ binders2, eqs_pre1 ++ eqs_pre2, init_post1 ++ init_post2, step_post1 ++ step_post2)
    | Raw_EIfte l e1 e2 e3 => let '(ei1, es1, orig1, binders1, eqs_pre1, init_post1, step_post1) := raw_to_comb e1 seed in
      let '(e2i, e2s, orig2, binders2, eqs_pre2, init_post2, step_post2) := raw_to_comb e2 orig1 in
        let '(e3i, e3s, orig3, binders3, eqs_pre3, init_post3, step_post3) := raw_to_comb e3 orig2 in
        (EIfte l ei1 e2i e3i, EIfte l es1 e2s e3s, orig3, binders1 ++ binders2 ++ binders3, eqs_pre1 ++ eqs_pre2 ++ eqs_pre3, init_post1 ++ init_post2 ++ init_post3, step_post1 ++ step_post2 ++ step_post3)
    | @Raw_EPre l t e => let '(ei, es, ident_pre, binders, eqs_pre, init_post, step_post) := raw_to_comb e seed in
      let ident_eq := next_ident ident_pre in
        let next_orig := next_ident ident_eq in
          let pre_var := (ident_pre, t) in
            let eq_var := (ident_eq, t) in
              (
                EVar l pre_var,
                EVar l pre_var,
                next_orig,
                pre_var::eq_var::binders,
                (ident_pre, existT comb_exp t (EVar l eq_var))::eqs_pre,
                (ident_eq, existT _ t ei)::init_post,
                (ident_eq, existT _ t es)::step_post
              )
    | Raw_EArrow l e1 e2 => let '(ei1, es1, orig1, binders1, eqs_pre1, init_post1, step_post1) := raw_to_comb e1 seed in
      let '(e2i, e2s, orig2, binders2, eqs_pre2, init_post2, step_post2) := raw_to_comb e2 orig1 in
        (ei1, e2s, orig2, binders1 ++ binders2, eqs_pre1 ++ eqs_pre2, init_post1 ++ init_post2, step_post1 ++ step_post2)
  end.

Fixpoint var_of_exp_aux {ty} (e: comb_exp ty) (acc: list (ident * type)): list (ident * type) :=
  match e with
    | EConst _ _ => acc
    | EVar _ (name, ty) => (name, ty) :: acc
    | EUnop _ _ e => var_of_exp_aux e acc
    | EBinop _ _ e1 e2 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 acc)
    | EIfte _ e1 e2 e3 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 (var_of_exp_aux e3 acc))
  end.

Definition var_of_exp {ty} (e: comb_exp ty): list (ident * type) :=
  var_of_exp_aux e [].

(** Properties *)
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

Lemma isnext_raw_to_comb {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post)
  -> forall x, In x (map fst pre_binders) -> exists n, x = iter n next_ident seed.
Proof.
  intros eqe.
  induction exp in ei, es, seed, seed', pre_binders, pre_eqs, init_post, step_post, eqe.
  - injection eqe as <- <- <- <- <- <- <-.
    intros.
    contradiction.
  - injection eqe as <- <- <- <- <- <- <-.
    intros.
    contradiction.
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
    intros x isin.
    rewrite map_app in isin.
    apply in_app_or in isin.
    specialize (IHexp1 x).
    specialize (IHexp2 x).
    destruct isin as [isin | isin].
    1: tauto.
    specialize (IHexp2 isin).
    assert (nextseed := raw_to_comb_nextseed unfold1).
    destruct nextseed as [nseed nextseed].
    rewrite nextseed in IHexp2.
    destruct IHexp2 as [n2 IHexp2].
    rewrite <- Nat.iter_add in IHexp2.
    exists (n2 + nseed).
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    destruct (raw_to_comb exp3 seed2) as [[[[[[ei3 es3] seed3] binders3] pre_eqs3] init_post3] step_post3] eqn: unfold3.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    specialize (IHexp3 _ _ _ _ _ _ _ _ unfold3).

    assert (nextseed1 := raw_to_comb_nextseed unfold1).
    assert (nextseed2 := raw_to_comb_nextseed unfold2).

    intros x isin.
    specialize (IHexp1 x).
    specialize (IHexp2 x).
    specialize (IHexp3 x).
    destruct nextseed1 as [nseed1 nextseed1].
    destruct nextseed2 as [nseed2 nextseed2].
    rewrite nextseed1 in IHexp2.
    rewrite nextseed2 in IHexp3.
    rewrite nextseed1 in IHexp3.
    rewrite !map_app in isin.
    rewrite !in_app_iff in isin.
    destruct isin as [isin | [isin | isin]].
    + tauto.
    + specialize (IHexp2 isin).
      destruct IHexp2 as [n IH].
      rewrite <- Nat.iter_add in IH.
      exists (n + nseed1).
      assumption.
    + specialize (IHexp3 isin).
      destruct IHexp3 as [n IH].
      do 2 rewrite <- Nat.iter_add in IH.
      exists (n + nseed2 + nseed1).
      assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    intros x isin.
    specialize (IHexp x).
    assert (nextseed := raw_to_comb_nextseed unfold1).
    destruct nextseed as [nseed nextseed].
    rewrite !map_cons in isin.
    unfold fst at 1 2 in isin.
    destruct isin as [isseed | [isnext | isin]]; subst.
    + exists nseed.
      reflexivity.
    + exists (S nseed).
      reflexivity.
    + tauto.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    intros x isin.
    rewrite map_app in isin.
    apply in_app_or in isin.
    specialize (IHexp1 x).
    specialize (IHexp2 x).
    destruct isin as [isin | isin].
    1: tauto.
    specialize (IHexp2 isin).
    assert (nextseed := raw_to_comb_nextseed unfold1).
    destruct nextseed as [nseed nextseed].
    rewrite nextseed in IHexp2.
    destruct IHexp2 as [n2 IHexp2].
    rewrite <- Nat.iter_add in IHexp2.
    exists (n2 + nseed).
    assumption.
Qed.

Lemma nodup_raw_to_comb {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post)
  -> NoDup (map fst pre_binders).
Proof.
  intros eqe.
  induction exp in ei, es, seed, seed', pre_binders, pre_eqs, init_post, step_post, eqe.
  - injection eqe as <- <- <- <- <- <- <-.
    apply NoDup_nil.
  - injection eqe as <- <- <- <- <- <- <-.
    apply NoDup_nil.
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
    assert (freshness1 := freshness_raw_to_comb unfold1).
    rewrite map_app.
    apply NoDup_app.
    1, 2: assumption.
    intros x isin1 isin2.
    assert (isnext := isnext_raw_to_comb unfold2 x isin2).
    destruct isnext as [n isnext].
    apply (freshness1 n).
    rewrite <- isnext.
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    destruct (raw_to_comb exp3 seed2) as [[[[[[ei3 es3] seed3] binders3] pre_eqs3] init_post3] step_post3] eqn: unfold3.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    specialize (IHexp3 _ _ _ _ _ _ _ _ unfold3).
    assert (freshness1 := freshness_raw_to_comb unfold1).
    assert (freshness2 := freshness_raw_to_comb unfold2).
    assert (nextseed := raw_to_comb_nextseed unfold2).
    destruct nextseed as [nseed nextseed].
    rewrite !map_app.
    apply NoDup_app.
    + assumption.
    + apply NoDup_app.
      1,2: assumption.
      intros x isin2 isin3.
      assert (isnext := isnext_raw_to_comb unfold3 x isin3).
      destruct isnext as [n isnext].
      apply (freshness2 n).
      rewrite <- isnext.
      assumption.
    + intros x isin1 isin23.
      apply in_app_or in isin23.
      destruct isin23 as [isin2 | isin3].
      * assert (isnext := isnext_raw_to_comb unfold2 x isin2).
        destruct isnext as [n isnext].
        apply (freshness1 n).
        rewrite <- isnext.
        assumption.
      * assert (isnext := isnext_raw_to_comb unfold3 x isin3).
        destruct isnext as [n isnext].
        rewrite nextseed in isnext.
        rewrite <- Nat.iter_add in isnext.
        apply (freshness1 (n + nseed)).
        rewrite <- isnext.
        assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    assert (freshness := freshness_raw_to_comb unfold1).
    rewrite !map_cons.
    unfold fst at 1 2.
    apply NoDup_cons.
    + intro isin.
      destruct isin as [f|isin].
      * inversion f as [ff].
        symmetry in ff.
        apply (ident_diff _ 0) in ff.
        assumption.
      * apply (freshness 0).
        assumption.
    + apply NoDup_cons.
      2: assumption.
      intro isin.
      apply (freshness 1).
      assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    assert (freshness1 := freshness_raw_to_comb unfold1).
    rewrite map_app.
    apply NoDup_app.
    1, 2: assumption.
    intros x isin1 isin2.
    assert (isnext := isnext_raw_to_comb unfold2 x isin2).
    destruct isnext as [n isnext].
    apply (freshness1 n).
    rewrite <- isnext.
    assumption.
Qed.

Lemma raw_to_comb_assigned_init {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post)
  -> Permutation (map equation_dest (pre_eqs ++ init_post)) pre_binders.
Proof.
  intro eqe.
  induction exp in ei, es, seed, seed', pre_binders, pre_eqs, init_post, step_post, eqe.
  - injection eqe as <- <- <- <- <- <- <-.
    apply perm_nil.
  - injection eqe as <- <- <- <- <- <- <-.
    apply perm_nil.
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
    rewrite !map_app.
    rewrite map_app in IHexp1.
    rewrite map_app in IHexp2.
    rewrite (Permutation_app_comm (map equation_dest pre_eqs1)).
    rewrite <- app_assoc.
    rewrite Permutation_app_comm.
    rewrite <- !app_assoc.
    rewrite app_assoc.
    rewrite (Permutation_app_comm (map equation_dest init_post2)).
    apply Permutation_app.
    all: assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    destruct (raw_to_comb exp3 seed2) as [[[[[[ei3 es3] seed3] binders3] pre_eqs3] init_post3] step_post3] eqn: unfold3.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    specialize (IHexp3 _ _ _ _ _ _ _ _ unfold3).
    rewrite !map_app.
    rewrite map_app in IHexp1.
    rewrite map_app in IHexp2.
    rewrite map_app in IHexp3.
    rewrite (Permutation_app_comm (map equation_dest pre_eqs1)).
    rewrite (Permutation_app_comm (map equation_dest pre_eqs2)).
    rewrite <- !app_assoc.
    rewrite Permutation_app_comm.
    rewrite <- !app_assoc.
    rewrite !app_assoc.
    rewrite <- app_assoc.
    rewrite (Permutation_app_comm (map equation_dest init_post3)).
    rewrite IHexp3.
    rewrite (Permutation_app_comm _ (map equation_dest init_post2)).
    rewrite !app_assoc.
    rewrite (Permutation_app_comm (map equation_dest init_post2)).
    rewrite IHexp2.
    rewrite (Permutation_app_comm _ (map equation_dest init_post1)).
    rewrite (Permutation_app_comm binders2).
    rewrite !app_assoc.
    rewrite (Permutation_app_comm (map equation_dest init_post1)).
    rewrite IHexp1.
    apply Permutation_refl.
  - simpl in eqe.
    destruct (raw_to_comb exp) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    rewrite !map_app.
    rewrite map_app in IHexp.
    rewrite !map_cons.
    unfold equation_dest at 1 3, fst, snd, projT1.
    rewrite <- !Permutation_middle.
    simpl.
    rewrite perm_swap.
    do 2 apply perm_skip.
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    rewrite !map_app.
    rewrite map_app in IHexp1.
    rewrite map_app in IHexp2.
    rewrite (Permutation_app_comm (map equation_dest pre_eqs1)).
    rewrite <- app_assoc.
    rewrite Permutation_app_comm.
    rewrite <- !app_assoc.
    rewrite app_assoc.
    rewrite (Permutation_app_comm (map equation_dest init_post2)).
    apply Permutation_app.
    all: assumption.
Qed.

Lemma raw_to_comb_assigned_step {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post)
  -> Permutation (map equation_dest (pre_eqs ++ step_post)) pre_binders.
Proof.
  intro eqe.
  induction exp in ei, es, seed, seed', pre_binders, pre_eqs, init_post, step_post, eqe.
  - injection eqe as <- <- <- <- <- <- <-.
    apply perm_nil.
  - injection eqe as <- <- <- <- <- <- <-.
    apply perm_nil.
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
    rewrite !map_app.
    rewrite map_app in IHexp1.
    rewrite map_app in IHexp2.
    rewrite (Permutation_app_comm (map equation_dest pre_eqs1)).
    rewrite <- app_assoc.
    rewrite Permutation_app_comm.
    rewrite <- !app_assoc.
    rewrite app_assoc.
    rewrite (Permutation_app_comm (map equation_dest step_post2)).
    apply Permutation_app.
    all: assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    destruct (raw_to_comb exp3 seed2) as [[[[[[ei3 es3] seed3] binders3] pre_eqs3] init_post3] step_post3] eqn: unfold3.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    specialize (IHexp3 _ _ _ _ _ _ _ _ unfold3).
    rewrite !map_app.
    rewrite map_app in IHexp1.
    rewrite map_app in IHexp2.
    rewrite map_app in IHexp3.
    rewrite (Permutation_app_comm (map equation_dest pre_eqs1)).
    rewrite (Permutation_app_comm (map equation_dest pre_eqs2)).
    rewrite <- !app_assoc.
    rewrite Permutation_app_comm.
    rewrite <- !app_assoc.
    rewrite !app_assoc.
    rewrite <- app_assoc.
    rewrite (Permutation_app_comm (map equation_dest step_post3)).
    rewrite IHexp3.
    rewrite (Permutation_app_comm _ (map equation_dest step_post2)).
    rewrite !app_assoc.
    rewrite (Permutation_app_comm (map equation_dest step_post2)).
    rewrite IHexp2.
    rewrite (Permutation_app_comm _ (map equation_dest step_post1)).
    rewrite (Permutation_app_comm binders2).
    rewrite !app_assoc.
    rewrite (Permutation_app_comm (map equation_dest step_post1)).
    rewrite IHexp1.
    apply Permutation_refl.
  - simpl in eqe.
    destruct (raw_to_comb exp) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    rewrite !map_app.
    rewrite map_app in IHexp.
    rewrite !map_cons.
    unfold equation_dest at 1 3, fst, snd, projT1.
    rewrite <- !Permutation_middle.
    simpl.
    rewrite perm_swap.
    do 2 apply perm_skip.
    assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    rewrite !map_app.
    rewrite map_app in IHexp1.
    rewrite map_app in IHexp2.
    rewrite (Permutation_app_comm (map equation_dest pre_eqs1)).
    rewrite <- app_assoc.
    rewrite Permutation_app_comm.
    rewrite <- !app_assoc.
    rewrite app_assoc.
    rewrite (Permutation_app_comm (map equation_dest step_post2)).
    apply Permutation_app.
    all: assumption.
Qed.

(* Semantics *)
Inductive value: type -> Set :=
  | RVConst  : forall {ty}, const ty -> value ty
  | RVUnop   : forall {ty tout}, unop ty tout -> value ty -> value tout
  | RVBinop  : forall {ty1 ty2 tout}, binop ty1 ty2 tout -> value ty1 -> value ty2 -> value tout
  | RVIfte   : forall {ty}, value TBool -> value ty -> value ty -> value ty
.

Definition history := Dict.t {ty & Stream.t (value ty)}.
Definition in_history (h : history) '((v, ty) : nat * type) := match Dict.find v h with
  | Some (existT _ ty' _) => ty' = ty
  | None => False
end.
