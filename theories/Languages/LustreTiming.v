Set Default Goal Selector "!".

From Reactive.Props Require Import Freshness Identifier Inclusion.
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

Fixpoint var_of_raw_exp_aux {ty} (e: raw_exp ty) (acc: list (ident * type)): list (ident * type) :=
  match e with
    | Raw_EConst _ => acc
    | Raw_EVar (name, ty) => (name, ty) :: acc
    | Raw_EUnop _ e => var_of_raw_exp_aux e acc
    | Raw_EBinop _ e1 e2 =>
      var_of_raw_exp_aux e1 (var_of_raw_exp_aux e2 acc)
    | Raw_EIfte e1 e2 e3 =>
      var_of_raw_exp_aux e1 (var_of_raw_exp_aux e2 (var_of_raw_exp_aux e3 acc))
    | Raw_EPre e => var_of_raw_exp_aux e acc
    | Raw_EArrow e1 e2 =>
      var_of_raw_exp_aux e1 (var_of_raw_exp_aux e2 acc)
  end.

Definition var_of_raw_exp {ty} (e: raw_exp ty): list (ident * type) :=
  var_of_raw_exp_aux e [].

Inductive well_timed: nat -> forall {ty}, raw_exp ty -> Prop :=
  | TimedConst: forall (n: nat) {ty} (c: const ty), well_timed n (Raw_EConst c)
  | TimedVar: forall (n: nat) (b: binder), well_timed n (Raw_EVar b)
  | TimedUnop: forall (n: nat) {tin tout} (u: unop tin tout) (e: raw_exp tin), well_timed n e -> well_timed n (Raw_EUnop u e)
  | TimedBinop: forall (n: nat) {ty1 ty2 tout} (b: binop ty1 ty2 tout) (e1: raw_exp ty1) (e2: raw_exp ty2), well_timed n e1 -> well_timed n e2 -> well_timed n (Raw_EBinop b e1 e2)
  | TimedIfte: forall (n: nat) {ty} (c: raw_exp TBool) (e1 e2: raw_exp ty), well_timed n c -> well_timed n e1 -> well_timed n e2 -> well_timed n (Raw_EIfte c e1 e2)
  | TimedPre: forall (n: nat) {ty} (e: raw_exp ty), well_timed n e -> well_timed (S n) (Raw_EPre e)
  | TimedArrow_O: forall {ty} (e1 e2: raw_exp ty), well_timed 0 e1 -> well_timed 0 (Raw_EArrow e1 e2)
  | TimedArrow_S: forall (n: nat) {ty} (e1 e2: raw_exp ty), well_timed (S n) e2 -> well_timed (S n) (Raw_EArrow e1 e2)
.

Definition equation : Type := ident * { ty : type & comb_exp ty }.
Definition equation_dest (eq : equation) : ident * type := (fst eq, projT1 (snd eq)).

Definition raw_equation : Type := ident * { ty : type & raw_exp ty }.
Definition raw_equation_dest (eq : raw_equation) : ident * type := (fst eq, projT1 (snd eq)).

Lemma timed_exp {ty} (vname: string) (vid: ident) (loc: Result.location) (n: nat) (exp: raw_exp ty):
  Result.t type (well_timed n exp).
Proof.
  induction exp as [| | tin tout u exp IH | ty1 ty2 tout b e1 IH1 e2 IH2 | t ec IHc e1 IH1 e2 IH2 | ty exp IH | ty e1 IH1 e2 IH2] in n |- *.
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
  induction exp as [| | tin tout u exp IH | ty1 ty2 tout b e1 IH1 e2 IH2 | t ec IHc e1 IH1 e2 IH2 | ty exp IH | ty e1 IH1 e2 IH2] in n |- *.
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

Definition well_timed_eq (n: nat) (eq: raw_equation) : Prop := well_timed n (projT2 (snd eq)).

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
  n_seed_always_fresh: freshness n_seed n_vars;
}.

Record raw_node := mk_raw_node {
  rn_loc: Result.location;
  rn_name: string;

  rn_in: list binder;
  rn_out: list binder;
  rn_locals: list binder;
  rn_body: list raw_equation;

  rn_vars: list binder := rn_in ++ rn_out ++ rn_locals;
  rn_assigned_vars: list binder := map raw_equation_dest rn_body;
  rn_all_vars_exist: Forall (fun eq => incl (var_of_raw_exp (projT2 (snd eq))) rn_vars) rn_body;

  rn_vars_all_assigned: Permutation rn_assigned_vars (rn_out ++ rn_locals);
  rn_vars_unique: NoDup (map fst rn_vars);

  rn_seed: ident;
  rn_seed_always_fresh: freshness rn_seed rn_vars;
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

Fixpoint var_of_exp_aux {ty} (e: comb_exp ty) (acc: list (ident * type)): list (ident * type) :=
  match e with
    | EConst _ => acc
    | EVar (name, ty) => (name, ty) :: acc
    | EUnop _ e => var_of_exp_aux e acc
    | EBinop _ e1 e2 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 acc)
    | EIfte e1 e2 e3 =>
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
Inductive sem_unop : forall {tyin tyout : type}, unop tyin tyout -> value tyin -> value tyout -> Prop :=
  | SeNot (v: value TInt) : sem_unop Uop_not v (vnot v)
  | SeNeg (v: value TInt) : sem_unop Uop_neg v (vneg v).

Inductive sem_binop : forall {ty1 ty2 tyout : type}, binop ty1 ty2 tyout -> value ty1 -> value ty2 -> value tyout -> Prop :=
  | SeAnd (v1 v2: value TBool) : sem_binop Bop_and v1 v2 (vand v1 v2)
  | SeOr (v1 v2: value TBool) : sem_binop Bop_or v1 v2 (vor v1 v2)
  | SeXor (v1 v2: value TBool) : sem_binop Bop_xor v1 v2 (vxor v1 v2)
  | SePlus (v1 v2: value TInt) : sem_binop Bop_plus v1 v2 (vplus v1 v2)
  | SeMinus (v1 v2: value TInt) : sem_binop Bop_minus v1 v2 (vminus v1 v2)
  | SeMult (v1 v2: value TInt) : sem_binop Bop_mult v1 v2 (vmult v1 v2)
  | SeDiv (v1 v2: value TInt) : sem_binop Bop_div v1 v2 (vdiv v1 v2)
  | SeEq (v1 v2: value TInt) : sem_binop Bop_eq v1 v2 (veq v1 v2)
  | SeNeq (v1 v2: value TInt) : sem_binop Bop_neq v1 v2 (vneq v1 v2)
  | SeLe (v1 v2: value TInt) : sem_binop Bop_le v1 v2 (vle v1 v2)
  | SeLt (v1 v2: value TInt) : sem_binop Bop_lt v1 v2 (vlt v1 v2)
  | SeGe (v1 v2: value TInt) : sem_binop Bop_ge v1 v2 (vge v1 v2)
  | SeGt (v1 v2: value TInt) : sem_binop Bop_gt v1 v2 (vgt v1 v2).

Inductive sem_raw_exp (h: history) | : nat -> forall {ty}, raw_exp ty -> value ty -> Prop :=
  | Raw_SeConst (t: nat) {ty} (c: const ty):
    sem_raw_exp t (Raw_EConst c) (const_to_value c)
  
  | Raw_SeUnop (t: nat) {tyin tyout} (op: unop tyin tyout) (e: raw_exp _) (vin vout: value _):
    sem_raw_exp t e vin -> sem_unop op vin vout -> sem_raw_exp t (Raw_EUnop op e) vout
  
  | Raw_SeBinop (t: nat) {ty1 ty2 tyout} (op: binop ty1 ty2 tyout) (e1 e2: raw_exp _) (v1 v2 vout: value _):
    sem_raw_exp t e1 v1 -> sem_raw_exp t e2 v2 -> sem_binop op v1 v2 vout -> sem_raw_exp t (Raw_EBinop op e1 e2) vout

  | Raw_SeIfte (t: nat) {ty} (e1: raw_exp TBool) (e2 e3: raw_exp ty) (v1 v2 v3: value _):
    sem_raw_exp t e1 v1 ->
    sem_raw_exp t e2 v2 ->
    sem_raw_exp t e3 v3 ->
    sem_raw_exp t (Raw_EIfte e1 e2 e3) (vifte v1 v2 v3)

  | Raw_SeVar (t: nat) (b: binder) (v: Stream.t (value (binder_ty b))):
      Dict.maps_to (fst b) (existT _ _ v) h ->
      sem_raw_exp t (Raw_EVar b) (Stream.nth t v)

  | Raw_SePre {ty} (t: nat) (e: raw_exp ty) (v: value ty):
    sem_raw_exp t e v -> sem_raw_exp (S t) (Raw_EPre e) v

  | Raw_SeArrow0 {ty} (e1 e2: raw_exp ty) (v: value ty):
    sem_raw_exp O e1 v -> sem_raw_exp O (Raw_EArrow e1 e2) v

  | Raw_SeArrowS {ty} (t: nat) (e1 e2: raw_exp ty) (v: value ty):
    sem_raw_exp (S t) e2 v -> sem_raw_exp (S t) (Raw_EArrow e1 e2) v
.

Inductive sem_comb_exp (h: history) | : nat -> forall {ty}, comb_exp ty -> value ty -> Prop :=
  | SeConst (t: nat) {ty} (c: const ty):
      sem_comb_exp t (EConst c) (const_to_value c)
  
  | SeUnop (t: nat) {tyin tyout} (op: unop tyin tyout) (e: comb_exp _) (vin vout: value _):
    sem_comb_exp t e vin -> sem_unop op vin vout -> sem_comb_exp t (EUnop op e) vout
  
  | SeBinop (t: nat) {ty1 ty2 tyout} (op: binop ty1 ty2 tyout) (e1 e2: comb_exp _) (v1 v2 vout: value _):
    sem_comb_exp t e1 v1 -> sem_comb_exp t e2 v2 -> sem_binop op v1 v2 vout -> sem_comb_exp t (EBinop op e1 e2) vout

  | SeIfte (t: nat) {ty} (e1: comb_exp TBool) (e2 e3: comb_exp ty) (v1 v2 v3: value _):
    sem_comb_exp t e1 v1 ->
    sem_comb_exp t e2 v2 ->
    sem_comb_exp t e3 v3 ->
    sem_comb_exp t (EIfte e1 e2 e3) (vifte v1 v2 v3)

  | SeVar (t: nat) (b: binder) (v: Stream.t (value (binder_ty b))):
      Dict.maps_to (fst b) (existT _ _ v) h ->
      sem_comb_exp t (EVar b) (Stream.nth t v)
.

Definition sem_raw_eq (eq: raw_equation) (h: history) : Prop :=
  exists (s: Stream.t (value (projT1 (snd eq)))),
  h_maps_to (fst eq) s h /\ forall n, sem_raw_exp h n (projT2 (snd eq)) (Stream.nth n s).

Definition sem_node (n: node) (h: history) : Prop :=
  forall (i: ident) (ty: type),
  In (i, ty) n.(n_vars) ->
  exists (s: Stream.t (value ty)),
  h_maps_to i s h /\
  forall (e: comb_exp ty),
  (In (i, existT _ _ e) n.(n_init) -> sem_comb_exp h 0 e (Stream.hd s)) /\
  (In (i, existT _ _ e) (n.(n_step) ++ n.(n_pre)) -> forall n, sem_comb_exp h (S n) e (Stream.nth (S n) s))
  .
