Set Default Goal Selector "!".

From Reactive.Props Require Import Freshness Identifier Inclusion Permutations.
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

Fixpoint var_of_raw_exp_aux {ty} (e: raw_exp ty) (acc: list (ident * type)): list (ident * type) :=
  match e with
    | Raw_EConst _ _ => acc
    | Raw_EVar _ (name, ty) => (name, ty) :: acc
    | Raw_EUnop _ _ e => var_of_raw_exp_aux e acc
    | Raw_EBinop _ _ e1 e2 =>
      var_of_raw_exp_aux e1 (var_of_raw_exp_aux e2 acc)
    | Raw_EIfte _ e1 e2 e3 =>
      var_of_raw_exp_aux e1 (var_of_raw_exp_aux e2 (var_of_raw_exp_aux e3 acc))
    | Raw_EPre _ e => var_of_raw_exp_aux e acc
    | Raw_EArrow _ e1 e2 =>
      var_of_raw_exp_aux e1 (var_of_raw_exp_aux e2 acc)
  end.

Definition var_of_raw_exp {ty} (e: raw_exp ty): list (ident * type) :=
  var_of_raw_exp_aux e [].

Lemma var_of_raw_exp_aux_eq {ty} (e: raw_exp ty) (l: list (ident * type)):
  var_of_raw_exp_aux e l = var_of_raw_exp e ++ l.
Proof.
  revert l.
  induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 | loc ty e IH | loc ty e1 IH1 e2 IH2]; intros l.
  - reflexivity.
  - reflexivity.
  - apply IH.
  - unfold var_of_raw_exp.
    simpl.
    rewrite IH1, IH2, IH1, IH2.
    rewrite app_nil_r, app_assoc.
    reflexivity.
  - unfold var_of_raw_exp.
    simpl.
    rewrite IH1, IH2, IH3, IH1, IH2, IH3.
    rewrite app_nil_r, app_assoc, app_assoc, app_assoc.
    reflexivity.
  - apply IH.
  - unfold var_of_raw_exp.
    simpl.
    rewrite IH1, IH2, IH1, IH2.
    rewrite app_nil_r, app_assoc.
    reflexivity.
Qed.

Lemma var_of_raw_exp_aux_empty {ty} (e: raw_exp ty) (l: list (ident * type)):
  var_of_raw_exp_aux e l = [] -> l = [].
Proof.
  intros H.
  rewrite var_of_raw_exp_aux_eq in H.
  apply app_eq_nil in H as [ _ H ].
  assumption.
Qed.

Lemma var_of_raw_exp_aux_incl {ty} (e: raw_exp ty) (l1 l2: list (ident * type)):
  incl l1 l2 -> incl (var_of_raw_exp_aux e l1) (var_of_raw_exp_aux e l2).
Proof.
  intros H i Hi.
  rewrite var_of_raw_exp_aux_eq in Hi |- *.
  apply in_or_app.
  apply in_app_or in Hi as [ Hin | Hin ]; auto.
Qed.

Lemma var_of_raw_exp_aux_in_exp {ty tyv} (e: raw_exp ty) (l: list (ident * type)) (x: ident):
  In (x, tyv) (var_of_raw_exp e) -> In (x, tyv) (var_of_raw_exp_aux e l).
Proof.
  apply var_of_raw_exp_aux_incl with (l1 := []).
  intros a Hin.
  destruct Hin.
Qed.

Lemma var_of_raw_exp_aux_in_acc {ty tyv} (e: raw_exp ty) (l: list (ident * type)) (x: ident):
  In (x, tyv) l -> In (x, tyv) (var_of_raw_exp_aux e l).
Proof.
  intros H.
  rewrite var_of_raw_exp_aux_eq.
  apply in_or_app.
  auto.
Qed.

Lemma var_of_raw_exp_binop_eq {ty1 ty2 ty} (l: Result.location) (e1 e2: raw_exp _) (b: binop ty1 ty2 ty):
  var_of_raw_exp (Raw_EBinop l b e1 e2) = var_of_raw_exp e1 ++ var_of_raw_exp e2.
Proof.
  unfold var_of_raw_exp.
  simpl.
  rewrite var_of_raw_exp_aux_eq.
  reflexivity.
Qed.

Lemma var_of_raw_exp_ifte_eq {ty} (l: Result.location) (e1 : raw_exp TBool) (e2 e3: raw_exp ty):
  var_of_raw_exp (Raw_EIfte l e1 e2 e3) = var_of_raw_exp e1 ++ var_of_raw_exp e2 ++ var_of_raw_exp e3.
Proof.
  unfold var_of_raw_exp.
  simpl.
  do 2 rewrite var_of_raw_exp_aux_eq.
  reflexivity.
Qed.

Lemma var_of_raw_exp_not_in_binop {ty1 ty2 ty} (l: Result.location) (exp1 exp2: raw_exp _) (x: ident) (b: binop ty1 ty2 ty):
  (forall tyv, ~ In (x, tyv) (var_of_raw_exp (Raw_EBinop l b exp1 exp2))) ->
  forall tyv, (~ In (x, tyv) (var_of_raw_exp exp1) /\ ~ In (x, tyv) (var_of_raw_exp exp2)).
Proof.
  intros Hnin.
  split.
  - intros Hin1.
    apply (Hnin tyv).
    unfold var_of_raw_exp.
    simpl.
    apply var_of_raw_exp_aux_in_exp.
    assumption.
  - intros Hin1.
    apply (Hnin tyv).
    unfold var_of_raw_exp.
    simpl.
    apply var_of_raw_exp_aux_in_acc.
    assumption.
Qed.

Lemma var_of_raw_exp_not_in_ifte {ty} (l: Result.location) (e1: raw_exp TBool) (e2 e3: raw_exp ty) (x: ident):
  (forall tyv, ~ In (x, tyv) (var_of_raw_exp (Raw_EIfte l e1 e2 e3))) ->
  forall tyv, (~ In (x, tyv) (var_of_raw_exp e1) /\ ~ In (x, tyv) (var_of_raw_exp e2) /\ ~ In (x, tyv) (var_of_raw_exp e3)).
Proof.
  intros Hnin.
  split.
  - intros Hin.
    apply (Hnin tyv).
    unfold var_of_raw_exp.
    simpl.
    apply var_of_raw_exp_aux_in_exp.
    assumption.
  - split.
    + intros Hin.
      apply (Hnin tyv).
      unfold var_of_raw_exp.
      simpl.
      apply var_of_raw_exp_aux_in_acc.
      apply var_of_raw_exp_aux_in_exp.
      assumption.
    + intros Hin.
      apply (Hnin tyv).
      unfold var_of_raw_exp.
      simpl.
      apply var_of_raw_exp_aux_in_acc.
      apply var_of_raw_exp_aux_in_acc.
      assumption.
Qed.

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

Definition raw_equation : Type := ident * { ty : type & raw_exp ty }.
Definition raw_equation_dest (eq : raw_equation) : ident * type := (fst eq, projT1 (snd eq)).

Lemma timed_exp {ty} (vname: string) (vid: ident) (vty: type) (n: nat) (exp: raw_exp ty):
  Result.t type (well_timed n exp).
Proof.
  induction exp as [ l | l | l tin tout u exp IH | l ty1 ty2 tout b e1 IH1 e2 IH2 | l t ec IHc e1 IH1 e2 IH2 | l ty exp IH | l ty e1 IH1 e2 IH2] in n |- *.
  - apply Result.Ok.
    constructor.
  - apply Result.Ok.
    constructor.
  - refine (Result.bind (IH n) _); clear IH; intros IH.
    apply Result.Ok.
    constructor.
    apply IH.
  - refine (Result.bind (IH1 n) _); clear IH1; intros IH1.
    refine (Result.bind (IH2 n) _); clear IH2; intros IH2.
    apply Result.Ok.
    constructor.
    all: assumption.
  - refine (Result.bind (IHc n) _); clear IHc; intros IHc.
    refine (Result.bind (IH1 n) _); clear IH1; intros IH1.
    refine (Result.bind (IH2 n) _); clear IH2; intros IH2.
    apply Result.Ok.
    constructor.
    all: assumption.
  - destruct n.
    + exact (Result.Err [(l, (Result.InvalidTiming vname vid vty))]).
    + refine (Result.bind (IH n) _); clear IH; intros IH.
      apply Result.Ok.
      constructor.
      apply IH.
  - destruct n.
    + refine (Result.bind (IH1 O) _); clear IH1; intros IH1.
      apply Result.Ok.
      constructor.
      assumption.
    + refine (Result.bind (IH2 (S n)) _); clear IH2; intros IH2.
      apply Result.Ok.
      constructor.
      assumption.
Defined.

Lemma timed_exp_ge {ty} (vname: string) (vid: ident) (vty: type) (n: nat) (exp: raw_exp ty):
  Result.t type (forall n', n <= n' -> well_timed n' exp).
Proof.
  induction exp as [ l | l | l tin tout u exp IH | l ty1 ty2 tout b e1 IH1 e2 IH2 | l t ec IHc e1 IH1 e2 IH2 | l ty exp IH | l ty e1 IH1 e2 IH2] in n |- *.
  - apply Result.Ok.
    intros.
    constructor.
  - apply Result.Ok.
    intros.
    constructor.
  - refine (Result.bind (IH n) _); clear IH; intros IH.
    apply Result.Ok.
    intros n' isless.
    specialize (IH _ isless).
    constructor.
    apply IH.
  - refine (Result.bind (IH1 n) _); clear IH1; intros IH1.
    refine (Result.bind (IH2 n) _); clear IH2; intros IH2.
    apply Result.Ok.
    intros n' isless.
    specialize (IH1 _ isless).
    specialize (IH2 _ isless).
    constructor.
    all: assumption.
  - refine (Result.bind (IHc n) _); clear IHc; intros IHc.
    refine (Result.bind (IH1 n) _); clear IH1; intros IH1.
    refine (Result.bind (IH2 n) _); clear IH2; intros IH2.
    apply Result.Ok.
    intros n' isless.
    specialize (IHc _ isless).
    specialize (IH1 _ isless).
    specialize (IH2 _ isless).
    constructor.
    all: assumption.
  - destruct n.
    + exact (Result.Err [(l, (Result.InvalidTiming vname vid vty))]).
    + refine (Result.bind (IH n) _); clear IH; intros IH.
      apply Result.Ok.
      intros n' isless.
      destruct n' as [|n'].
      1: contradiction (Nat.nlt_0_r _ isless).
      apply le_S_n in isless.
      specialize (IH _ isless).
      constructor.
      assumption.
  - destruct n as [| n].
    + refine (Result.bind (timed_exp vname vid vty O e1) _); clear IH1; intros timed_1.
      refine (Result.bind (IH2 (S O)) _); clear IH2; intros IH2.
      apply Result.Ok.
      intros n' isless.
      destruct n' as [| n'].
      2: specialize (IH2 (S n') (le_n_S _ _ (le_0_n _))).
      all: constructor.
      all: assumption.
    + refine (Result.bind (IH2 (S n)) _); clear IH2; intros IH2.
      apply Result.Ok.
      intros n' isless.
      destruct n' as [|n'].
      1: contradiction (Nat.nlt_0_r _ isless).
      constructor.
      apply IH2.
      assumption.
Defined.

Definition well_timed_eq (eq: raw_equation) : Prop := forall n, well_timed n (projT2 (snd eq)).

Lemma timed_eq (eq: raw_equation) : Result.t type (well_timed_eq eq).
Proof.
  unfold well_timed_eq.
  destruct eq as [ident [ty e]].
  simpl.
  destruct (timed_exp_ge "<information lost>" ident ty 0 e) as [timed | err].
  2: right; exact err.
  left.
  intro n.
  apply (timed n).
  apply le_0_n.
Defined.

Lemma timed_list_eq (eqs: list raw_equation) : Result.t type (Forall well_timed_eq eqs).
Proof.
  refine (Result.list_map _ _).
  exact timed_eq.
Defined.

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

Record node := mk_node {
  n_loc: Result.location;
  n_name: string;

  n_in: list binder;
  n_out: list binder;
  n_locals: list binder; (* Also includes additionally created binders for pre *)
  n_pre: list (binder * ident); (* Happens before n_step *)
  n_init: list equation;
  n_step: list equation;

  n_vars: list binder := n_in ++ n_out ++ n_locals;
  n_assigned_vars_init: list binder := map equation_dest n_init;
  n_assigned_vars_step: list binder := map equation_dest n_step;

  n_init_vars_all_assigned: Permutation n_assigned_vars_init (n_out ++ n_locals);
  n_step_vars_all_assigned: Permutation n_assigned_vars_step (n_out ++ n_locals);
  n_all_init_vars_exist: Forall (fun eq => incl (var_of_exp (projT2 (snd eq))) n_vars) n_init;
  n_all_step_vars_exist: Forall (fun eq => incl (var_of_exp (projT2 (snd eq))) (n_vars ++ map fst n_pre)) n_step;
  n_all_pre_vars_exist: Forall (fun eq => In (snd eq, snd (fst eq)) n_vars) n_pre;

  n_vars_unique: NoDup (map fst n_vars ++ map (fun eq => fst (fst eq)) n_pre);

  n_seed: ident;
  n_seed_always_fresh: freshness n_seed (n_vars ++ map fst n_pre);
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

  rn_well_timed: Forall well_timed_eq rn_body;
}.


(* Translation from raw expressions to combinatorial expressions, extracting pre and arrow *)

Fixpoint raw_to_comb {ty} (exp: raw_exp ty) (seed: ident): (
    comb_exp ty (* init *)
    * comb_exp ty (* step *)
    * ident (* New identifier origin *)
    * list binder (* Variables created for pre *)
    * (list (binder * ident)) (* pre equations *)
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
                EVar l eq_var,
                EVar l pre_var,
                next_orig,
                eq_var::binders,
                (pre_var, ident_eq)::eqs_pre,
                (ident_eq, existT _ t ei)::init_post,
                (ident_eq, existT _ t es)::step_post
              )
    | Raw_EArrow _ e1 e2 =>
      let '(ei1, es1, orig1, binders1, eqs_pre1, init_post1, step_post1) := raw_to_comb e1 seed in
      let '(e2i, e2s, orig2, binders2, eqs_pre2, init_post2, step_post2) := raw_to_comb e2 orig1 in
      (ei1, e2s, orig2, binders1 ++ binders2,
       eqs_pre1 ++ eqs_pre2, init_post1 ++ init_post2, step_post1 ++ step_post2)
  end.

(** Properties *)
Lemma raw_to_comb_nextseed {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs} {init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post) ->
  exists n, seed' = iter n next_ident seed.
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

Lemma freshness_raw_to_comb {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs} {init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post) ->
  freshness seed' (pre_binders ++ map fst pre_eqs).
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
    refine (freshness_permutation (freshness_fusion IHexp1 IHexp2) _).
    rewrite map_app, !app_assoc.
    apply Permutation_app_tail; rewrite <-2!app_assoc; apply Permutation_app_head.
    exact (Permutation_app_comm _ _).
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
    refine (freshness_permutation (freshness_fusion IHexp1 (freshness_fusion IHexp2 IHexp3)) _).
    rewrite !map_app, !app_assoc.
    apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head.
    rewrite (Permutation_app_comm binders3), !app_assoc; apply Permutation_app_tail.
    rewrite (Permutation_app_comm binders2); apply Permutation_refl.
  - simpl in eqe.
    destruct (raw_to_comb exp) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    intros n isin.
    rewrite <- !PeanoNat.Nat.iter_succ_r in isin; simpl map in isin.
    rewrite map_app, map_cons in isin.
    destruct isin as [f | isin]; [|apply in_app_or in isin; destruct isin as [isin | [f | isin]]].
    1: rewrite Nat.iter_succ_r in f.
    1,3: apply ident_diff in f; exact f.
    1,2: refine (IHexp (S (S n)) _); rewrite map_app; apply in_or_app.
    1: left.
    2: right.
    1,2: exact isin.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    assert (nextseed := raw_to_comb_nextseed unfold2).
    apply (freshness_later_e nextseed) in IHexp1.
    refine (freshness_permutation (freshness_fusion IHexp1 IHexp2) _).
    rewrite map_app, !app_assoc.
    apply Permutation_app_tail; rewrite <-2!app_assoc; apply Permutation_app_head.
    exact (Permutation_app_comm _ _).
Qed.

Lemma isnext_raw_to_comb {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs} {init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post) ->
  forall x, In x (map fst pre_binders ++ map (fun eq => fst (fst eq)) pre_eqs) -> exists n, x = iter n next_ident seed.
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
    specialize (IHexp1 x).
    specialize (IHexp2 x).
    assert (isin' : In x (map fst binders1 ++ map (fun eq => fst (fst eq)) pre_eqs1) \/ In x (map fst binders2 ++ map (fun eq => fst (fst eq)) pre_eqs2))
     by (rewrite !map_app, !in_app_iff in isin; rewrite !in_app_iff; tauto).
    clear isin; rename isin' into isin.
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
    assert (isin' : In x (map fst binders1 ++ map (fun eq => fst (fst eq)) pre_eqs1) \/ In x (map fst binders2 ++ map (fun eq => fst (fst eq)) pre_eqs2) \/
                    In x (map fst binders3 ++ map (fun eq => fst (fst eq)) pre_eqs3))
     by (rewrite !map_app, !in_app_iff in isin; rewrite !in_app_iff; tauto).
    clear isin; rename isin' into isin.
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
    assert (isin' : In x (seed1 :: next_ident seed1 :: map fst binders1 ++ map (fun eq => fst (fst eq)) pre_eqs1))
     by (cbn in isin |- *; rewrite in_app_iff in isin; cbn in isin; rewrite in_app_iff; tauto).
    clear isin; rename isin' into isin.
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
    specialize (IHexp1 x).
    specialize (IHexp2 x).
    assert (isin' : In x (map fst binders1 ++ map (fun eq => fst (fst eq)) pre_eqs1) \/ In x (map fst binders2 ++ map (fun eq => fst (fst eq)) pre_eqs2))
     by (rewrite !map_app, !in_app_iff in isin; rewrite !in_app_iff; tauto).
    clear isin; rename isin' into isin.
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

Lemma nodup_raw_to_comb {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs} {init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post)
  -> NoDup (map fst pre_binders ++ map (fun eq => fst (fst eq)) pre_eqs).
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
    rewrite !map_app.
    refine (Permutation_NoDup _ (NoDup_app IHexp1 IHexp2 _)).
    1: rewrite !app_assoc; apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head, Permutation_app_comm.
    intros x isin1 isin2.
    assert (isnext := isnext_raw_to_comb unfold2 x isin2).
    destruct isnext as [n isnext].
    apply (freshness1 n).
    rewrite <- isnext, map_app, map_map.
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
    refine (Permutation_NoDup _ (NoDup_app IHexp1 (NoDup_app IHexp2 IHexp3 _) _)).
    + clear.
      rewrite !app_assoc; apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head.
      rewrite !app_assoc, (Permutation_app_comm _ (map _ binders2)), <-!app_assoc; apply Permutation_app_head.
      rewrite app_assoc, (Permutation_app_comm _ (map _ binders3)); apply Permutation_refl.
    + intros x isin2 isin3.
      assert (isnext := isnext_raw_to_comb unfold3 x isin3).
      destruct isnext as [n isnext].
      apply (freshness2 n).
      rewrite <- isnext, map_app, map_map.
      assumption.
    + intros x isin1 isin23.
      apply in_app_or in isin23.
      destruct isin23 as [isin2 | isin3].
      * assert (isnext := isnext_raw_to_comb unfold2 x isin2).
        destruct isnext as [n isnext].
        apply (freshness1 n).
        rewrite <- isnext, map_app, map_map.
        assumption.
      * assert (isnext := isnext_raw_to_comb unfold3 x isin3).
        destruct isnext as [n isnext].
        rewrite nextseed in isnext.
        rewrite <- Nat.iter_add in isnext.
        apply (freshness1 (n + nseed)).
        rewrite <- isnext, map_app, map_map.
        assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    assert (freshness := freshness_raw_to_comb unfold1).
    rewrite !map_cons.
    assert (Hperm : Permutation (seed1 :: next_ident seed1 :: map fst binders1 ++ map (fun eq => fst (fst eq)) pre_eqs1)
                                (next_ident seed1 :: map fst binders1 ++ seed1 :: map (fun eq => fst (fst eq)) pre_eqs1))
     by exact (Permutation_elt [] _ (_ :: _) _ _ (Permutation_refl _)).
    refine (Permutation_NoDup Hperm _); clear Hperm.
    apply NoDup_cons.
    + intro isin.
      destruct isin as [f|isin].
      * symmetry in f.
        apply (ident_diff _ 0) in f.
        assumption.
      * apply (freshness 0).
        rewrite map_app, map_map.
        assumption.
    + apply NoDup_cons.
      2: assumption.
      intro isin.
      apply (freshness 1).
      rewrite map_app, map_map.
      assumption.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    assert (freshness1 := freshness_raw_to_comb unfold1).
    rewrite !map_app.
    refine (Permutation_NoDup _ (NoDup_app IHexp1 IHexp2 _)).
    1: rewrite !app_assoc; apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head, Permutation_app_comm.
    intros x isin1 isin2.
    assert (isnext := isnext_raw_to_comb unfold2 x isin2).
    destruct isnext as [n isnext].
    apply (freshness1 n).
    rewrite <- isnext, map_app, map_map.
    assumption.
Qed.

Lemma raw_to_comb_assigned_init {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs} {init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post) ->
  Permutation (map equation_dest init_post) pre_binders.
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
    rewrite IHexp1, IHexp2, IHexp3.
    apply Permutation_refl.
  - simpl in eqe.
    destruct (raw_to_comb exp) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    cbn; rewrite IHexp; apply Permutation_refl.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    rewrite map_app, IHexp1, IHexp2; apply Permutation_refl.
Qed.

Lemma raw_to_comb_assigned_step {ty} {exp: raw_exp ty} {ei es: comb_exp ty} {seed seed': ident} {pre_binders: list binder} {pre_eqs} {init_post step_post: list equation}:
  raw_to_comb exp seed = (ei, es, seed', pre_binders, pre_eqs, init_post, step_post) ->
  Permutation (map equation_dest step_post) pre_binders.
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
    rewrite !map_app, IHexp1, IHexp2.
    apply Permutation_refl.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    destruct (raw_to_comb exp3 seed2) as [[[[[[ei3 es3] seed3] binders3] pre_eqs3] init_post3] step_post3] eqn: unfold3.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    specialize (IHexp3 _ _ _ _ _ _ _ _ unfold3).
    rewrite !map_app, IHexp1, IHexp2, IHexp3.
    apply Permutation_refl.
  - simpl in eqe.
    destruct (raw_to_comb exp) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp _ _ _ _ _ _ _ _ unfold1).
    cbn; rewrite IHexp; apply Permutation_refl.
  - simpl in eqe.
    destruct (raw_to_comb exp1 seed) as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: unfold1.
    destruct (raw_to_comb exp2 seed1) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2] eqn: unfold2.
    injection eqe as <- <- <- <- <- <- <-.
    specialize (IHexp1 _ _ _ _ _ _ _ _ unfold1).
    specialize (IHexp2 _ _ _ _ _ _ _ _ unfold2).
    rewrite !map_app, IHexp1, IHexp2.
    apply Permutation_refl.
Qed.

Lemma var_of_exp_aux_eq {ty} (e: comb_exp ty) (l: list (ident * type)):
  var_of_exp_aux e l = var_of_exp e ++ l.
Proof.
  revert l.
  induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros l.
  - reflexivity.
  - reflexivity.
  - apply IH.
  - unfold var_of_exp.
    simpl.
    rewrite IH1, IH2, IH1, IH2.
    rewrite app_nil_r, app_assoc.
    reflexivity.
  - unfold var_of_exp.
    simpl.
    rewrite IH1, IH2, IH3, IH1, IH2, IH3.
    rewrite app_nil_r, app_assoc, app_assoc, app_assoc.
    reflexivity.
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
    forall loc, sem_raw_exp t (Raw_EConst loc c) (const_to_value c)
  
  | Raw_SeUnop (t: nat) {tyin tyout} (op: unop tyin tyout) (e: raw_exp _) (vin vout: value _):
    sem_raw_exp t e vin -> sem_unop op vin vout -> forall loc, sem_raw_exp t (Raw_EUnop loc op e) vout
  
  | Raw_SeBinop (t: nat) {ty1 ty2 tyout} (op: binop ty1 ty2 tyout) (e1 e2: raw_exp _) (v1 v2 vout: value _):
    sem_raw_exp t e1 v1 -> sem_raw_exp t e2 v2 -> sem_binop op v1 v2 vout -> forall loc, sem_raw_exp t (Raw_EBinop loc op e1 e2) vout

  | Raw_SeIfte (t: nat) {ty} (e1: raw_exp TBool) (e2 e3: raw_exp ty) (v1 v2 v3: value _):
    sem_raw_exp t e1 v1 ->
    sem_raw_exp t e2 v2 ->
    sem_raw_exp t e3 v3 ->
    forall loc, sem_raw_exp t (Raw_EIfte loc e1 e2 e3) (vifte v1 v2 v3)

  | Raw_SeVar (t: nat) (b: binder) (v: Stream.t (value (binder_ty b))):
      Dict.maps_to (fst b) (existT _ _ v) h ->
      forall loc, sem_raw_exp t (Raw_EVar loc b) (Stream.nth t v)

  | Raw_SePre {ty} (t: nat) (e: raw_exp ty) (v: value ty):
    sem_raw_exp t e v -> forall loc, sem_raw_exp (S t) (Raw_EPre loc e) v

  | Raw_SeArrow0 {ty} (e1 e2: raw_exp ty) (v: value ty):
    sem_raw_exp O e1 v -> forall loc, sem_raw_exp O (Raw_EArrow loc e1 e2) v

  | Raw_SeArrowS {ty} (t: nat) (e1 e2: raw_exp ty) (v: value ty):
    sem_raw_exp (S t) e2 v -> forall loc, sem_raw_exp (S t) (Raw_EArrow loc e1 e2) v
.

Inductive sem_comb_exp (h: history) (t: nat) | : forall {ty}, comb_exp ty -> value ty -> Prop :=
  | SeConst {ty} (c: const ty):
      forall loc, sem_comb_exp (EConst loc c) (const_to_value c)
  
  | SeUnop {tyin tyout} (op: unop tyin tyout) (e: comb_exp _) (vin vout: value _):
    sem_comb_exp e vin -> sem_unop op vin vout -> forall loc, sem_comb_exp (EUnop loc op e) vout
  
  | SeBinop {ty1 ty2 tyout} (op: binop ty1 ty2 tyout) (e1 e2: comb_exp _) (v1 v2 vout: value _):
    sem_comb_exp e1 v1 -> sem_comb_exp e2 v2 -> sem_binop op v1 v2 vout -> forall loc, sem_comb_exp (EBinop loc op e1 e2) vout

  | SeIfte {ty} (e1: comb_exp TBool) (e2 e3: comb_exp ty) (v1 v2 v3: value _):
    sem_comb_exp e1 v1 ->
    sem_comb_exp e2 v2 ->
    sem_comb_exp e3 v3 ->
    forall loc, sem_comb_exp (EIfte loc e1 e2 e3) (vifte v1 v2 v3)

  | SeVar (b: binder) (v: Stream.t (value (binder_ty b))):
      Dict.maps_to (fst b) (existT _ _ v) h ->
      forall loc, sem_comb_exp (EVar loc b) (Stream.nth t v)
.

Definition sem_raw_eq (eq: raw_equation) (h: history) : Prop :=
  exists (s: Stream.t (value (projT1 (snd eq)))),
  h_maps_to (fst eq) s h /\ forall n, sem_raw_exp h n (projT2 (snd eq)) (Stream.nth n s).

Definition sem_raw_node (n: raw_node) (h: history) : Prop :=
  forall (i: ident) (ty: type),
  In (i, ty) n.(rn_vars) ->
   exists (s: Stream.t (value ty)),
   h_maps_to i s h /\
   (forall (e: raw_exp ty), In (i, existT _ _ e) n.(rn_body) -> forall n, sem_raw_exp h n e (Stream.nth n s))
  .

Definition sem_node (n: node) (h: history) : Prop :=
  forall (i: ident) (ty: type),
  (In (i, ty) n.(n_vars) ->
   exists (s: Stream.t (value ty)),
   h_maps_to i s h /\
   (forall (e: comb_exp ty), In (i, existT _ _ e) n.(n_init) -> sem_comb_exp h 0 e (Stream.hd s)) /\
   (forall (e: comb_exp ty), In (i, existT _ _ e) n.(n_step) -> forall n, sem_comb_exp h (S n) e (Stream.nth (S n) s))) /\
  (forall j, In ((i, ty), j) n.(n_pre) ->
   exists (s: Stream.t (value ty)),
   h_maps_to i s h /\
   forall n loc, sem_comb_exp h n (EVar loc (j, ty)) (Stream.nth (S n) s))
  .

Lemma timed_exp_complete : forall {ty} vname vid vty n e es, @timed_exp ty vname vid vty n e = Result.Err es ->
  ~ well_timed n e /\ exists l, es = [(l, Result.InvalidTiming vname vid vty)].
Proof using.
  intros ty vname vid vty n e es H.
  revert n es H; induction e as [| |l tin tout op e IH|l ty1 ty2 tout op e1 IH1 e2 IH2|l ty e1 IH1 e2 IH2 e3 IH3|l ty e IH|l ty e1 IH1 e2 IH2]; intros n es H.
  1,2: discriminate H.
  all: simpl timed_exp in H.
  - specialize (IH n); destruct (timed_exp vname vid vty n e); [discriminate H|injection H as ->].
    specialize (IH _ eq_refl) as [IH [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    intros f; inversion f; simpl_exist_type; subst; contradict IH; assumption.
  - specialize (IH1 n); destruct (timed_exp vname vid vty n e1) as [?|es1]; [|injection H as <-].
    2: specialize (IH1 _ eq_refl) as [IH1 [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    2: intros f; inversion f; subst; simpl_exist_type; subst; contradict IH1; assumption.
    specialize (IH2 n); destruct (timed_exp vname vid vty n e2) as [?|es2]; [discriminate H|injection H as <-].
    specialize (IH2 _ eq_refl) as [IH2 [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    intros f; inversion f; subst; simpl_exist_type; subst; contradict IH2; assumption.
  - specialize (IH1 n); destruct (timed_exp vname vid vty n e1) as [?|es1]; [|injection H as <-].
    2: specialize (IH1 _ eq_refl) as [IH1 [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    2: intros f; inversion f; subst; simpl_exist_type; subst; contradict IH1; assumption.
    specialize (IH2 n); destruct (timed_exp vname vid vty n e2) as [?|es2]; [|injection H as <-].
    2: specialize (IH2 _ eq_refl) as [IH2 [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    2: intros f; inversion f; subst; simpl_exist_type; subst; contradict IH2; assumption.
    specialize (IH3 n); destruct (timed_exp vname vid vty n e3) as [?|es3]; [discriminate H|injection H as <-].
    specialize (IH3 _ eq_refl) as [IH3 [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    intros f; inversion f; subst; simpl_exist_type; subst; contradict IH3; assumption.
  - destruct n as [|n].
    1: split; [intros f; inversion f|injection H as <-; exact (ex_intro _ _ eq_refl)].
    specialize (IH n); destruct (timed_exp vname vid vty n e); [discriminate H|injection H as <-].
    specialize (IH _ eq_refl) as [IH [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    intros f; inversion f; simpl_exist_type; subst; contradict IH; assumption.
  - destruct n as [|n].
    2: specialize (IH2 (S n)); destruct (timed_exp vname vid vty (S n) e2); [discriminate H|injection H as <-].
    2: specialize (IH2 _ eq_refl) as [IH2 [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    2: intros f; inversion f; simpl_exist_type; subst; contradict IH2; assumption.
    specialize (IH1 O); destruct (timed_exp vname vid vty O e1); [discriminate H|injection H as <-].
    specialize (IH1 _ eq_refl) as [IH1 [l' ->]]; split; [|exact (ex_intro _ l' eq_refl)].
    intros f; inversion f; subst; simpl_exist_type; subst; contradict IH1; assumption.
Qed.

Lemma timed_exp_ge_complete : forall {ty} vname vid vty n e es, @timed_exp_ge ty vname vid vty n e = Result.Err es ->
  exists n', n <= n' /\ ~ well_timed n' e /\ exists l, es = [(l, Result.InvalidTiming vname vid vty)].
Proof using.
  intros ty vname vid vty n e es H.
  revert n es H; induction e as [| |l tin tout op e IH|l ty1 ty2 tout op e1 IH1 e2 IH2|l ty e1 IH1 e2 IH2 e3 IH3|l ty e IH|l ty e1 IH1 e2 IH2]; intros n es H.
  1,2: discriminate H.
  all: simpl timed_exp_ge in H.
  - specialize (IH n); destruct (timed_exp_ge vname vid vty n e); [discriminate H|injection H as ->].
    specialize (IH _ eq_refl) as (n' & Hn & IH & [l' ->]); exists n'; split; [exact Hn|split; [|exact (ex_intro _ l' eq_refl)]].
    intros f; inversion f; simpl_exist_type; subst; contradict IH; assumption.
  - specialize (IH1 n); destruct (timed_exp_ge vname vid vty n e1) as [?|es1]; [|injection H as <-].
    2: specialize (IH1 _ eq_refl) as (n' & Hn & IH1 & [l' ->]); exists n'; split; [exact Hn|split; [|exact (ex_intro _ l' eq_refl)]].
    2: intros f; inversion f; subst; simpl_exist_type; subst; contradict IH1; assumption.
    specialize (IH2 n); destruct (timed_exp_ge vname vid vty n e2) as [?|es2]; [discriminate H|injection H as <-].
    specialize (IH2 _ eq_refl) as (n' & Hn & IH2 & [l' ->]); exists n'; split; [exact Hn|split; [|exact (ex_intro _ l' eq_refl)]].
    intros f; inversion f; subst; simpl_exist_type; subst; contradict IH2; assumption.
  - specialize (IH1 n); destruct (timed_exp_ge vname vid vty n e1) as [?|es1]; [|injection H as <-].
    2: specialize (IH1 _ eq_refl) as (n' & Hn & IH1 & [l' ->]); exists n'; split; [exact Hn|split; [|exact (ex_intro _ l' eq_refl)]].
    2: intros f; inversion f; subst; simpl_exist_type; subst; contradict IH1; assumption.
    specialize (IH2 n); destruct (timed_exp_ge vname vid vty n e2) as [?|es2]; [|injection H as <-].
    2: specialize (IH2 _ eq_refl) as (n' & Hn & IH2 & [l' ->]); exists n'; split; [exact Hn|split; [|exact (ex_intro _ l' eq_refl)]].
    2: intros f; inversion f; subst; simpl_exist_type; subst; contradict IH2; assumption.
    specialize (IH3 n); destruct (timed_exp_ge vname vid vty n e3) as [?|es3]; [discriminate H|injection H as <-].
    specialize (IH3 _ eq_refl) as (n' & Hn & IH3 & [l' ->]); exists n'; split; [exact Hn|split; [|exact (ex_intro _ l' eq_refl)]].
    intros f; inversion f; subst; simpl_exist_type; subst; contradict IH3; assumption.
  - destruct n as [|n].
    1: exists O; split; [exact (le_n _)|split; [intros f; inversion f|injection H as <-; exact (ex_intro _ _ eq_refl)]].
    specialize (IH n); destruct (timed_exp_ge vname vid vty n e); [discriminate H|injection H as <-].
    specialize (IH _ eq_refl) as (n' & Hn & IH & [l' ->]); exists (S n'); split; [exact (le_n_S _ _ Hn)|split; [|exact (ex_intro _ l' eq_refl)]].
    intros f; inversion f; simpl_exist_type; subst; contradict IH; assumption.
  - destruct n as [|n].
    2: specialize (IH2 (S n)); destruct (timed_exp_ge vname vid vty (S n) e2); [discriminate H|injection H as <-].
    2: specialize (IH2 _ eq_refl) as (n' & Hn & IH2 & [l' ->]); exists n'; split; [exact Hn|split; [|exact (ex_intro _ l' eq_refl)]].
    2: intros f; inversion f; [subst; inversion Hn|simpl_exist_type; subst; contradict IH2; assumption].
    clear IH1; assert (IH1 := timed_exp_complete vname vid vty O e1).
    destruct (timed_exp vname vid vty O e1); [|injection H as <-].
    2: exists O; split; [exact (le_n _)|].
    2: specialize (IH1 _ eq_refl) as (IH1 & [l' ->]); split; [|exact (ex_intro _ l' eq_refl)].
    2: intros f; inversion f; subst; simpl_exist_type; subst; contradict IH1; assumption.
    specialize (IH2 (S O)); destruct (timed_exp_ge vname vid vty (S O) e2) as [?|es2]; [discriminate H|injection H as <-].
    specialize (IH2 _ eq_refl) as (n' & Hn & IH2 & [l' ->]); exists n'; split; [exact (le_0_n _)|split; [|exact (ex_intro _ l' eq_refl)]].
    intros f; inversion f; [subst; inversion Hn|subst; simpl_exist_type; subst; contradict IH2; assumption].
Qed.

Lemma timed_eq_complete : forall eq es, timed_eq eq = Result.Err es ->
  exists n, ~ well_timed n (projT2 (snd eq)) /\
  exists vname l, es = [(l, Result.InvalidTiming vname (fst eq) (projT1 (snd eq)))].
Proof using.
  intros [vid [vty e]] es H.
  unfold timed_eq in H.
  match type of H with match timed_exp_ge ?s _ _ _ _ with _ => _ end = _ => remember s as vname eqn:eqvname; clear eqvname end.
  specialize (timed_exp_ge_complete vname vid vty O e) as tmp.
  destruct (timed_exp_ge vname vid vty O e) as [|es']; [discriminate H|injection H as ->].
  specialize (tmp _ eq_refl) as (n & _ & H1 & H2).
  exists n; split; [exact H1|exists vname; exact H2].
Qed.

Lemma timed_list_eq_complete : forall eqs es, timed_list_eq eqs = Result.Err es ->
  exists eqs0, incl eqs0 eqs /\
  Forall (fun eq => In eq eqs0 <-> exists n, ~ well_timed n (projT2 (snd eq))) eqs /\
  exists aux,
  es = List.map (fun '((vid, vty), (l, vname)) => (l, Result.InvalidTiming vname vid vty))
         (List.combine (List.map raw_equation_dest eqs0) aux).
Proof using.
  intros eqs; induction eqs as [|eq eqs IH]; intros es H.
  1: discriminate H.
  simpl timed_list_eq in H.
  assert (Heq := timed_eq_complete eq).
  destruct (timed_eq eq) as [Hok|eq1]; [clear Heq|specialize (Heq _ eq_refl)];
    (destruct (timed_list_eq eqs) as [IHok|eq2]; [clear IH|specialize (IH _ eq_refl)]); [discriminate H|injection H as <-..].
  - destruct IH as (eqs0 & H1 & H2 & H3); exists eqs0; split; [exact (fun _ h => or_intror (H1 _ h))|split; [|exact H3]].
    constructor; [|exact H2].
    split; [|intros [n Hn]; contradict Hn; exact (Hok _)].
    intros H; assert (H' := H).
    apply H1, (proj1 (Forall_forall _ _) H2), proj1 in H'.
    exact (H' H).
  - destruct Heq as (n & Hn & vname & l & ->).
    exists [eq]; split; [intros ? [h|[]]; left; exact h|].
    split; [|exists [(l, vname)]; exact eq_refl].
    constructor; [split; [intros _; exists n; exact Hn|intros _; left; exact eq_refl]|].
    refine (Forall_impl _ _ IHok); clear - Hn.
    intros eq' H; split; [intros [->|[]]; exists n; exact Hn|intros [n' Hn']; contradiction (Hn' (H _))].
  - destruct Heq as (n & Hn & vname & l & ->).
    destruct IH as (eqs0 & H1 & H2 & aux & Haux).
    exists (eq :: eqs0); split; [intros ? [h|h]; [left; exact h|right; exact (H1 _ h)]|].
    split; [|exists ((l, vname) :: aux); exact (f_equal (cons _) Haux)].
    constructor; [split; [intros _; exists n; exact Hn|intros _; left; exact eq_refl]|].
    refine (Forall_impl _ _ H2); clear - Hn.
    intros eq' H; cbn; rewrite H; split; [intros [->|h]; [exists n; exact Hn|exact h]|intros h; right; exact h].
Qed.
