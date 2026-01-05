Set Default Goal Selector "!".

From Reactive.Languages Require Lustre LustreTiming.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Freshness Identifier Inclusion Permutations.

From Stdlib Require Import List Nat Permutation.
From Stdlib.Arith Require Import PeanoNat.

Import ListNotations.

Module Source := Lustre.
Module Target := LustreTiming.


Fixpoint expr_to_raw {ty} (e: Source.exp ty): Target.raw_exp ty :=
  match e with
    | Source.EConst c => Target.Raw_EConst c
    | Source.EVar v => Target.Raw_EVar v
    | Source.EIfte e1 e2 e3 => Target.Raw_EIfte (expr_to_raw e1) (expr_to_raw e2) (expr_to_raw e3)
    | Source.EUnop u e => match u in Source.unop tin tout return Target.raw_exp tin -> Target.raw_exp tout with
      | Source.Uop_neg => fun e => Target.Raw_EUnop Target.Uop_neg e
      | Source.Uop_not => fun e => Target.Raw_EUnop Target.Uop_not e
      | Source.Uop_pre => fun e => Target.Raw_EPre e
      end (expr_to_raw e)
    | Source.EBinop b e1 e2 => match b in Source.binop ty1 ty2 tout return Target.raw_exp ty1 -> Target.raw_exp ty2 -> Target.raw_exp tout with
      | Source.Bop_and => fun e1 e2 => Target.Raw_EBinop Target.Bop_and e1 e2
      | Source.Bop_or => fun e1 e2 => Target.Raw_EBinop Target.Bop_or e1 e2
      | Source.Bop_xor => fun e1 e2 => Target.Raw_EBinop Target.Bop_xor e1 e2
      | Source.Bop_plus => fun e1 e2 => Target.Raw_EBinop Target.Bop_plus e1 e2
      | Source.Bop_minus => fun e1 e2 => Target.Raw_EBinop Target.Bop_minus e1 e2
      | Source.Bop_mult => fun e1 e2 => Target.Raw_EBinop Target.Bop_mult e1 e2
      | Source.Bop_div => fun e1 e2 => Target.Raw_EBinop Target.Bop_div e1 e2
      | Source.Bop_eq => fun e1 e2 => Target.Raw_EBinop Target.Bop_eq e1 e2
      | Source.Bop_neq => fun e1 e2 => Target.Raw_EBinop Target.Bop_neq e1 e2
      | Source.Bop_le => fun e1 e2 => Target.Raw_EBinop Target.Bop_le e1 e2
      | Source.Bop_lt => fun e1 e2 => Target.Raw_EBinop Target.Bop_lt e1 e2
      | Source.Bop_ge => fun e1 e2 => Target.Raw_EBinop Target.Bop_ge e1 e2
      | Source.Bop_gt => fun e1 e2 => Target.Raw_EBinop Target.Bop_gt e1 e2
      | Source.Bop_arrow => fun e1 e2 => Target.Raw_EArrow e1 e2
      end (expr_to_raw e1) (expr_to_raw e2)
  end.

Definition translate_expr {ty} (e: Source.exp ty) (seed: ident): (
    Target.comb_exp ty (* init *)
    * Target.comb_exp ty (* step *)
    * ident (* New identifier origin *)
    * list binder (* Variables created for pre *)
    * list (binder * ident) (* pre equations *)
    (* Equations to merge with the regular equations *)
    (* for init: 
      prex = undef (a variable initialised later)

      for step:
      prex = eqx (eqx being updated later with the current values)
    *)
    (* Equations NOT to be merged, but can be ordered separately *)
    * list Target.equation (* init_post equations *)
    * list Target.equation (* step_post equations *)
  ) :=
    Target.raw_to_comb (expr_to_raw e) seed.

Lemma translate_expr_nextseed {ty} (e: Source.exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) :=  translate_expr e seed in
  exists n, seed' = iter n next_ident seed.
Proof.
  destruct (translate_expr e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_nextseed translation).
Qed.

Lemma freshness_translate_expr {ty} (e: Source.exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_expr e seed in
  freshness seed' (pre_binders ++ map fst pre_eqs).
Proof.
  destruct (translate_expr e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.freshness_raw_to_comb translation).
Qed.

Lemma isnext_translate_expr {ty} (e: Source.exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_expr e seed in
  forall x, In x (map fst pre_binders ++ map (fun eq => fst (fst eq)) pre_eqs) -> exists n, x = iter n next_ident seed.
Proof.
  destruct (translate_expr e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.isnext_raw_to_comb translation).
Qed.

Lemma nodup_translate_expr {ty} (e: Source.exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_expr e seed in
  NoDup (map fst pre_binders ++ map (fun eq => fst (fst eq)) pre_eqs).
Proof.
  destruct (translate_expr e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.nodup_raw_to_comb translation).
Qed.

Lemma translate_expr_assigned_init {ty} (e: Source.exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_expr e seed in
  Permutation (map Target.equation_dest init_post) pre_binders.
Proof.
  destruct (translate_expr e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_assigned_init translation).
Qed.

Lemma translate_expr_assigned_step {ty} (e: Source.exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_expr e seed in
  Permutation (map Target.equation_dest step_post) pre_binders.
Proof.
  destruct (translate_expr e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_assigned_step translation).
Qed.

Lemma translate_expr_init_wd v {ty} {e: Source.exp ty} {n_in n_out n_locals} seed:
  incl (Source.var_of_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_expr e seed in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in ++ n_out ++ pre_binders ++ n_locals)) ((v, existT _ ty ei) :: init_post).
Proof.
  intros Hwd; revert seed; induction e as [ty c|[ty b]|ty1 ty op e IH|ty1 ty2 ty op e1 IH1 e2 IH2|ty e1 IH1 e2 IH2 e3 IH3];
    intros seed; cbn; try (constructor; [|constructor]).
  - intros ? [].
  - exact Hwd.
  - destruct op; cbn.
    all: specialize (IH Hwd seed); unfold translate_expr in IH.
    all: destruct (Target.raw_to_comb (expr_to_raw e) seed) as [[[[[[]]]]]].
    3:{
      constructor; [|constructor].
      - intros ? [<-|[]]; apply in_or_app, or_intror, in_or_app, or_intror; left; exact eq_refl.
      - refine (incl_trans _ _ _ (Forall_inv IH) _).
        cbn.
        apply incl_app_app; [apply incl_refl|].
        apply incl_app_app; [apply incl_refl|].
        intros ? h; right; exact h.
      - refine (Forall_impl _ _ (Forall_inv_tail IH)).
        clear; intros ? Hincl ? Hin.
        specialize (Hincl _ Hin).
        rewrite !in_app_iff in *; cbn; tauto.
    }
    all: constructor; [exact (Forall_inv IH)|exact (Forall_inv_tail IH)].
  - cbn in Hwd; rewrite Source.var_of_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h)))).
    clear Hwd; unfold translate_expr in IH1, IH2.
    destruct op; cbn.
    all: destruct (Target.raw_to_comb (expr_to_raw e1) seed) as [[[[[[] seed2]]]]]; clear e1.
    all: specialize (IH2 seed2).
    all: destruct (Target.raw_to_comb (expr_to_raw e2) seed2) as [[[[[[] seed']]]]]; clear e2.
    14:{
      constructor; [|apply Forall_app; split].
      - refine (incl_trans _ _ _ (Forall_inv IH1) _).
        cbn.
        apply incl_app_app; [apply incl_refl|].
        apply incl_app_app; [apply incl_refl|].
        apply incl_app_app; [|apply incl_refl].
        intros ? h; apply in_or_app; left; exact h.
      - refine (Forall_impl _ _ (Forall_inv_tail IH1)).
        clear; intros ? Hincl ? Hin.
        specialize (Hincl _ Hin).
        cbn; rewrite !in_app_iff in *; tauto.
      - refine (Forall_impl _ _ (Forall_inv_tail IH2)).
        clear; intros ? Hincl ? Hin.
        specialize (Hincl _ Hin).
        cbn; rewrite !in_app_iff in *; tauto.
    }
    all: constructor; [|apply Forall_app; split; [refine (Forall_impl _ _ (Forall_inv_tail IH1))|refine (Forall_impl _ _ (Forall_inv_tail IH2))]].
    2,3,5,6,8,9,11,12,14,15,17,18,20,21,23,24,26,27,29,30,32,33,35,36,38,39: clear; intros ? Hincl ? Hin.
    2-27: specialize (Hincl _ Hin); cbn; rewrite !in_app_iff in *; tauto.
    all: cbn; rewrite Target.var_of_exp_aux_eq.
    all: apply incl_app; [refine (incl_trans _ _ _ (Forall_inv IH1) _)|refine (incl_trans _ _ _ (Forall_inv IH2) _)]; cbn.
    all: apply incl_app_app; [apply incl_refl|].
    all: apply incl_app_app; [apply incl_refl|].
    all: apply incl_app_app; [|apply incl_refl].
    all: intros ? h; apply in_or_app; tauto.
  - cbn in Hwd; rewrite 2!Source.var_of_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl h)))))).
    specialize (IH3 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror h)))))).
    clear Hwd; unfold translate_expr in IH1, IH2, IH3.
    destruct (Target.raw_to_comb (expr_to_raw e1) seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb (expr_to_raw e2) seed2) as [[[[[[] seed3]]]]]; clear e2.
    specialize (IH3 seed3).
    destruct (Target.raw_to_comb (expr_to_raw e3) seed3) as [[[[[[] seed']]]]]; clear e3.
    constructor; [|apply Forall_app; split; [|apply Forall_app; split]].
    2: refine (Forall_impl _ _ (Forall_inv_tail IH1)).
    3: refine (Forall_impl _ _ (Forall_inv_tail IH2)).
    4: refine (Forall_impl _ _ (Forall_inv_tail IH3)).
    2-4: clear; intros ? Hincl ? Hin; specialize (Hincl _ Hin).
    2-4: cbn; rewrite !in_app_iff in *; tauto.
    cbn; rewrite 2!Target.var_of_exp_aux_eq.
    repeat apply incl_app.
    1: refine (incl_trans _ _ _ (Forall_inv IH1) _).
    2: refine (incl_trans _ _ _ (Forall_inv IH2) _).
    3: refine (incl_trans _ _ _ (Forall_inv IH3) _).
    all: do 2 (apply incl_app_app; [apply incl_refl|]).
    all: apply incl_app_app; [|apply incl_refl].
    all: cbn; intros ? h; rewrite !in_app_iff; tauto.
Qed.

Lemma translate_expr_pre_wd {ty} {e: Source.exp ty} {n_in n_out n_locals} seed:
  incl (Source.var_of_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_expr e seed in
  Forall (fun eq => In (snd eq, snd (fst eq)) (n_in ++ n_out ++ pre_binders ++ n_locals)) pre_eqs.
Proof.
  intros _; revert seed; induction e as [ty c|[ty b]|ty1 ty op e IH|ty1 ty2 ty op e1 IH1 e2 IH2|ty e1 IH1 e2 IH2 e3 IH3];
    intros seed; cbn; try (constructor; [|constructor]).
  - apply Forall_nil.
  - apply Forall_nil.
  - destruct op; cbn.
    all: specialize (IH seed); unfold translate_expr in IH.
    all: destruct (Target.raw_to_comb (expr_to_raw e) seed) as [[[[[[]]]]]].
    3:{
      constructor; [|refine (Forall_impl _ _ IH)].
      2: clear; cbn; intros ? Hin; cbn; rewrite !in_app_iff in *; cbn; rewrite in_app_iff; tauto.
      apply in_or_app, or_intror, in_or_app, or_intror; left; exact eq_refl.
    }
    all: exact IH.
  - specialize (IH1 seed).
    unfold translate_expr in IH1, IH2.
    destruct op; cbn.
    all: destruct (Target.raw_to_comb (expr_to_raw e1) seed) as [[[[[[] seed2]]]]]; clear e1.
    all: specialize (IH2 seed2).
    all: destruct (Target.raw_to_comb (expr_to_raw e2) seed2) as [[[[[[] seed']]]]]; clear e2.
    all: apply Forall_app; split; [refine (Forall_impl _ _ IH1)|refine (Forall_impl _ _ IH2)].
    all: clear; intros ? Hin.
    all: rewrite !in_app_iff in *; tauto.
  - unfold translate_expr in IH1, IH2, IH3.
    specialize (IH1 seed).
    destruct (Target.raw_to_comb (expr_to_raw e1) seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb (expr_to_raw e2) seed2) as [[[[[[] seed3]]]]]; clear e2.
    specialize (IH3 seed3).
    destruct (Target.raw_to_comb (expr_to_raw e3) seed3) as [[[[[[] seed']]]]]; clear e3.
    apply Forall_app; split; [|apply Forall_app; split].
    1: refine (Forall_impl _ _ IH1).
    2: refine (Forall_impl _ _ IH2).
    3: refine (Forall_impl _ _ IH3).
    all: clear; intros ? Hin.
    all: rewrite !in_app_iff in *; tauto.
Qed.

Lemma translate_expr_step_wd v {ty} {e: Source.exp ty} {n_in n_out n_locals} seed:
  incl (Source.var_of_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_expr e seed in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) ((n_in ++ n_out ++ pre_binders ++ n_locals) ++ map fst pre_eqs))
    ((v, existT _ ty es) :: step_post).
Proof.
  intros Hwd; revert seed; induction e as [ty c|[ty b]|ty1 ty op e IH|ty1 ty2 ty op e1 IH1 e2 IH2|ty e1 IH1 e2 IH2 e3 IH3];
    intros seed; cbn; try (constructor; [|constructor]).
  - intros ? [].
  - rewrite app_nil_r; exact Hwd.
  - destruct op; cbn.
    all: specialize (IH Hwd seed); unfold translate_expr in IH.
    all: destruct (Target.raw_to_comb (expr_to_raw e) seed) as [[[[[[]]]]]].
    3:{
      constructor; [|constructor].
      - intros ? [<-|[]]; apply in_or_app; right; left; exact eq_refl.
      - refine (incl_trans _ _ _ (Forall_inv IH) _).
        cbn.
        apply incl_app_app; [|intros ? h; right; exact h].
        do 2 (apply incl_app_app; [apply incl_refl|]).
        intros ? h; right; exact h.
      - refine (Forall_impl _ _ (Forall_inv_tail IH)).
        clear; intros ? Hincl ? Hin.
        specialize (Hincl _ Hin).
        rewrite !in_app_iff in *; cbn; tauto.
    }
    all: constructor; [exact (Forall_inv IH)|exact (Forall_inv_tail IH)].
  - cbn in Hwd; rewrite Source.var_of_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h)))).
    clear Hwd; unfold translate_expr in IH1, IH2.
    destruct op; cbn.
    all: destruct (Target.raw_to_comb (expr_to_raw e1) seed) as [[[[[[] seed2]]]]]; clear e1.
    all: specialize (IH2 seed2).
    all: destruct (Target.raw_to_comb (expr_to_raw e2) seed2) as [[[[[[] seed']]]]]; clear e2.
    14:{
      constructor; [|apply Forall_app; split].
      - refine (incl_trans _ _ _ (Forall_inv IH2) _).
        apply incl_app_app; [|intros ? h; rewrite map_app; apply in_or_app; right; exact h].
        do 2 (apply incl_app_app; [apply incl_refl|]).
        apply incl_app_app; [|apply incl_refl].
        intros ? h; apply in_or_app; right; exact h.
      - refine (Forall_impl _ _ (Forall_inv_tail IH1)).
        clear; intros ? Hincl ? Hin.
        specialize (Hincl _ Hin).
        cbn; rewrite map_app, !in_app_iff in *; tauto.
      - refine (Forall_impl _ _ (Forall_inv_tail IH2)).
        clear; intros ? Hincl ? Hin.
        specialize (Hincl _ Hin).
        cbn; rewrite map_app, !in_app_iff in *; tauto.
    }
    all: constructor; [|apply Forall_app; split; [refine (Forall_impl _ _ (Forall_inv_tail IH1))|refine (Forall_impl _ _ (Forall_inv_tail IH2))]].
    2,3,5,6,8,9,11,12,14,15,17,18,20,21,23,24,26,27,29,30,32,33,35,36,38,39: clear; intros ? Hincl ? Hin.
    2-27: specialize (Hincl _ Hin); cbn; rewrite map_app, !in_app_iff in *; tauto.
    all: cbn; rewrite Target.var_of_exp_aux_eq.
    all: apply incl_app; [refine (incl_trans _ _ _ (Forall_inv IH1) _)|refine (incl_trans _ _ _ (Forall_inv IH2) _)]; cbn.
    all: apply incl_app_app; [|intros ? h; rewrite map_app; apply in_or_app; tauto].
    all: do 2 (apply incl_app_app; [apply incl_refl|]).
    all: apply incl_app_app; [|apply incl_refl].
    all: intros ? h; apply in_or_app; tauto.
  - cbn in Hwd; rewrite 2!Source.var_of_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl h)))))).
    specialize (IH3 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror h)))))).
    clear Hwd; unfold translate_expr in IH1, IH2, IH3.
    destruct (Target.raw_to_comb (expr_to_raw e1) seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb (expr_to_raw e2) seed2) as [[[[[[] seed3]]]]]; clear e2.
    specialize (IH3 seed3).
    destruct (Target.raw_to_comb (expr_to_raw e3) seed3) as [[[[[[] seed']]]]]; clear e3.
    constructor; [|apply Forall_app; split; [|apply Forall_app; split]].
    2: refine (Forall_impl _ _ (Forall_inv_tail IH1)).
    3: refine (Forall_impl _ _ (Forall_inv_tail IH2)).
    4: refine (Forall_impl _ _ (Forall_inv_tail IH3)).
    2-4: clear; intros ? Hincl ? Hin; specialize (Hincl _ Hin).
    2-4: cbn; rewrite !map_app, !in_app_iff in *; tauto.
    cbn; rewrite 2!Target.var_of_exp_aux_eq.
    repeat apply incl_app.
    1: refine (incl_trans _ _ _ (Forall_inv IH1) _).
    2: refine (incl_trans _ _ _ (Forall_inv IH2) _).
    3: refine (incl_trans _ _ _ (Forall_inv IH3) _).
    all: apply incl_app_app; [|intros ? h; rewrite !map_app, !in_app_iff; tauto].
    all: do 2 (apply incl_app_app; [apply incl_refl|]).
    all: apply incl_app_app; [|apply incl_refl].
    all: cbn; intros ? h; rewrite !in_app_iff; tauto.
Qed.

Fixpoint translate_equations (eqs: list Source.equation) (seed: ident): (
    list Target.equation (* init *)
    * list Target.equation (* step *)
    * ident (* New identifier origin *)
    * list binder (* Variables created for pre *)
    * list (binder * ident)(* pre equations *)
    (* Equations to merge with the regular equations *)
    (* for init: 
      prex = undef (a variable initialised later)

      for step:
      prex = eqx (eqx being updated later with the current values)
    *)
    (* Equations NOT to be merged, but can be ordered separately *)
    * list Target.equation (* init_post equations *)
    * list Target.equation (* step_post equations *)
  ) :=
    match eqs with
      | [] => ([], [], seed, [], [], [], [])
      | eq::eqs => let '(init_eq, step_eq, seed1, pre_binders0, pre_eqs0, init_post0, step_post0) := translate_equations eqs seed in
        let '(ident, existT _ ty e) := eq in
          let '(ei, es, seed2, pre_binders1, pre_eqs1, init_post1, step_post1) := translate_expr e seed1 in
            (
              (ident, existT _ ty ei)::init_eq,
              (ident, existT _ ty es)::step_eq,
              seed2,
              pre_binders1 ++ pre_binders0,
              pre_eqs1 ++ pre_eqs0,
              init_post1 ++ init_post0,
              step_post1 ++ step_post0
            )
    end.

Lemma translate_equations_app (eqs1 eqs2: list Source.equation) (seed: ident):
  let '(init_eq2, step_eq2, seed2, pre_binders2, pre_eqs2, init_post2, step_post2) := translate_equations eqs2 seed in
  let '(init_eq1, step_eq1, seed1, pre_binders1, pre_eqs1, init_post1, step_post1) := translate_equations eqs1 seed2 in
  translate_equations (eqs1 ++ eqs2) seed = (
    init_eq1 ++ init_eq2,
    step_eq1 ++ step_eq2,
    seed1,
    pre_binders1 ++ pre_binders2,
    pre_eqs1 ++ pre_eqs2,
    init_post1 ++ init_post2,
    step_post1 ++ step_post2
  ).
Proof.
  induction eqs1 as [|eq eqs1 IH].
  1: simpl.
  1: destruct (translate_equations eqs2 seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  1: reflexivity.
  simpl.
  destruct eq as [ident [ty exp]].
  destruct (translate_equations eqs2 seed) as [[[[[[init_eqs2 step_eqs2] seed2] pre_binders2] pre_eqs2] init_post2] step_post2].
  destruct (translate_equations eqs1 seed2) as [[[[[[init_eqs1 step_eqs1] seed1] pre_binders1] pre_eqs1] init_post1] step_post1].
  rewrite IH.
  destruct (translate_expr exp seed1) as [[[[[[ei es] seed'] pre_binders] pre_eqs] init_post] step_post].
  repeat rewrite app_assoc.
  reflexivity.
Qed.


Lemma translate_equations_nextseed (eqs: list Source.equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  exists n, seed' = iter n next_ident seed.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    exists 0.
    reflexivity.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    specialize (translate_expr_nextseed expr seed0) as unfoldseed.
    destruct (translate_expr expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    destruct unfoldseed as [nexpr seedexpr].
    destruct IH as [nIH IH].
    rewrite IH in seedexpr.
    rewrite <- Nat.iter_add in seedexpr.
    exists (nexpr + nIH).
    assumption.
Qed.

Lemma freshness_translate_equations (eqs: list Source.equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  freshness seed' (pre_binders ++ map fst pre_eqs).
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    intro n.
    tauto.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    assert (freshness_expr := freshness_translate_expr expr seed0).
    assert (nextseed_expr := translate_expr_nextseed expr seed0).
    destruct (translate_expr expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    apply (freshness_later_e nextseed_expr) in IH.
    refine (freshness_permutation (freshness_fusion freshness_expr IH) _).
    rewrite map_app, !app_assoc; apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head, Permutation_app_comm.
Qed.

Lemma isnext_translate_equations (eqs: list Source.equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  forall x, In x (map fst pre_binders ++ map (fun eq => fst (fst eq)) pre_eqs) -> exists n, x = iter n next_ident seed.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    intros.
    contradiction.
  - simpl in translation.
    assert (nextseed := translate_equations_nextseed eqs seed).
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    assert (isnext_expr := isnext_translate_expr expr seed0).
    destruct (translate_expr expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    intros x isin.
    specialize (IH x).
    destruct nextseed as [nseed nextseed].
    rewrite nextseed in isnext_expr.
    specialize (isnext_expr x).
    cbn in IH, isnext_expr, isin.
    rewrite !map_app in isin.
    rewrite in_app_iff in IH, isnext_expr, isin; rewrite !in_app_iff in isin.
    destruct isin as [[isin | isin] | [isin | isin]].
    2,4: tauto.
    1: specialize (isnext_expr (or_introl isin)).
    2: specialize (isnext_expr (or_intror isin)).
    all: destruct isnext_expr as [n isnext_expr].
    all: rewrite <- Nat.iter_add in isnext_expr.
    all: exists (n + nseed).
    all: assumption.
Qed.

Lemma nodup_translate_equations (eqs: list Source.equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  NoDup (map fst pre_binders ++ map (fun eq => fst (fst eq)) pre_eqs).
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    apply NoDup_nil.
  - simpl in translation.
    assert (freshness_trans := freshness_translate_equations eqs seed).
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    assert (nodup_expr := nodup_translate_expr expr seed0).
    assert (isnext := isnext_translate_expr expr seed0).
    destruct (translate_expr expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    cbn in *; rewrite !map_app.
    refine (Permutation_NoDup _ (NoDup_app nodup_expr IH _)).
    1: rewrite !app_assoc; apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head, Permutation_app_comm.
    intros x isin2 isin0.
    specialize (isnext x isin2).
    destruct isnext as [n isnext].
    specialize (freshness_trans n).
    rewrite isnext, <-(map_map fst fst), <-map_app in isin0.
    contradiction.
Qed.

Lemma translate_equations_assigned_init (eqs: list Source.equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  Permutation (map Target.equation_dest init_post) pre_binders.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    apply perm_nil.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    assert (perm_expr := translate_expr_assigned_init expr seed0).
    destruct (translate_expr expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_app, IH, perm_expr; apply Permutation_refl.
Qed.

Lemma translate_equations_assigned_step (eqs: list Source.equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  Permutation (map Target.equation_dest step_post) pre_binders.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    apply perm_nil.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    assert (perm_expr := translate_expr_assigned_step expr seed0).
    destruct (translate_expr expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_app, IH, perm_expr; apply Permutation_refl.
Qed.

Lemma translate_equations_conservation_init (eqs: list Source.equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  map Source.equation_dest eqs = map Target.equation_dest init_eqs.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    reflexivity.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    destruct (translate_expr expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_cons.
    unfold Source.equation_dest at 1, Target.equation_dest at 1, fst, snd, projT1.
    rewrite IH.
    reflexivity.
Qed.

Lemma translate_equations_conservation_step (eqs: list Source.equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  map Source.equation_dest eqs = map Target.equation_dest step_eqs.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    reflexivity.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    destruct (translate_expr expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_cons.
    unfold Source.equation_dest at 1, Target.equation_dest at 1, fst, snd, projT1.
    rewrite IH.
    reflexivity.
Qed.

Lemma translate_init_assigned {n_body n_out n_locals} (n_seed: ident)
  (n_vars_all_assigned : Permutation (map Source.equation_dest n_body) (n_out ++ n_locals)) :
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Permutation (map Target.equation_dest (init_eqs ++ init_post_eqs)) (n_out ++ pre_binders ++ n_locals).
Proof.
  assert (conservation_init := translate_equations_conservation_init n_body n_seed).
  assert (assigned_init := translate_equations_assigned_init n_body n_seed).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  rewrite map_app.
  rewrite <- conservation_init.
  rewrite (Permutation_app_comm (map Source.equation_dest n_body)).
  rewrite !app_assoc.
  rewrite (Permutation_app_comm n_out).
  rewrite <- !app_assoc.
  rewrite <- n_vars_all_assigned.
  apply Permutation_app.
  2: apply Permutation_refl.
  assumption.
Qed.

Lemma translate_step_assigned {n_body n_out n_locals} (n_seed: ident)
  (n_vars_all_assigned : Permutation (map Source.equation_dest n_body) (n_out ++ n_locals)) :
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Permutation (map Target.equation_dest (step_eqs ++ step_post_eqs)) (n_out ++ pre_binders ++ n_locals).
Proof.
  assert (conservation_step := translate_equations_conservation_step n_body n_seed).
  assert (assigned_step := translate_equations_assigned_step n_body n_seed).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  rewrite map_app.
  rewrite <- conservation_step.
  rewrite (Permutation_app_comm (map Source.equation_dest n_body)).
  rewrite !app_assoc.
  rewrite (Permutation_app_comm n_out).
  rewrite <- !app_assoc.
  rewrite <- n_vars_all_assigned.
  apply Permutation_app.
  2: apply Permutation_refl.
  assumption.
Qed.

Lemma translate_vars_unique {n_in n_out n_locals n_seed} (n_body: list Source.equation)
  (n_vars_unique : NoDup (map fst (n_in ++ n_out ++ n_locals)))
  (n_seed_always_fresh : freshness n_seed (n_in ++ n_out ++ n_locals)) :
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  NoDup (map fst (n_in ++ n_out ++ pre_binders ++ n_locals) ++ map (fun eq => fst (fst eq)) pre_eqs).
Proof.
  assert (nodup_translate := nodup_translate_equations n_body n_seed).
  assert (isnext := isnext_translate_equations n_body n_seed).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  rewrite <-(map_map fst fst), <-map_app.
  rewrite !map_app.
  rewrite !map_app in n_vars_unique.
  unfold freshness in n_seed_always_fresh.
  rewrite !map_app in n_seed_always_fresh.
  rewrite app_assoc.
  rewrite Permutation_app_comm.
  rewrite (Permutation_app_comm (map fst pre_binders)).
  rewrite <- app_assoc.
  rewrite Permutation_app_comm.
  rewrite 2!app_assoc, <-app_assoc, <-(app_assoc (map _ _)), map_map.
  apply NoDup_app.
  1, 2: assumption.
  intros x f isin; revert f.
  specialize (isnext x isin).
  destruct isnext as [n isnext].
  rewrite isnext.
  apply (n_seed_always_fresh n).
Qed.

Lemma translate_seed_always_fresh {n_in n_out n_locals n_seed} (n_body: list Source.equation)
  (n_seed_always_fresh : freshness n_seed (n_in ++ n_out ++ n_locals)) :
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  freshness new_seed ((n_in ++ n_out ++ pre_binders ++ n_locals) ++ map fst pre_eqs).
Proof.
  assert (fresh_translate := freshness_translate_equations n_body n_seed).
  assert (nextseed := translate_equations_nextseed n_body n_seed).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  intros n isin.
  rewrite !map_app in isin.
  unfold freshness in n_seed_always_fresh.
  rewrite !map_app in n_seed_always_fresh.
  rewrite app_assoc in isin.
  rewrite (Permutation_app_comm (map _ pre_binders)) in isin.
  rewrite app_assoc, <-app_assoc, <-(map_app _ pre_binders) in isin.
  rewrite Permutation_app_comm in isin.
  rewrite <-app_assoc in isin.
  apply in_app_or in isin.
  destruct nextseed as [nseed nextseed].
  specialize (fresh_translate n).
  destruct isin as [isin | isin].
  1: contradiction.
  rewrite nextseed in isin.
  rewrite <- Nat.iter_add in isin.
  specialize (n_seed_always_fresh (n + nseed)).
  contradiction.
Qed.

Lemma translation_conservation n_seed n_body eq:
  In eq n_body ->
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  let '(ident, existT _ ty e) := eq in
  exists seed1,
  let '(ei, es, seed2, pre_binders1, pre_eqs1, init_post1, step_post1) := translate_expr e seed1 in
    In (ident, existT _ ty ei) init_eqs /\
    In (ident, existT _ ty es) step_eqs.
Proof.
  induction n_body as [|eq' n_body IH].
  1: contradiction.
  simpl.
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  intros [|isin]; subst.
  all: destruct eq as [ident [ty e]].
  - destruct (translate_expr e seed') as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: translation.
    exists seed'.
    destruct (translate_expr e seed') as [[[[[[]]]]]].
    injection translation as <- <- <- <- <- <- <-.
    split.
    all: constructor 1.
    all: reflexivity.
  - destruct eq' as [ident' [ty' e']].
    specialize (IH isin).
    destruct IH as [seed1 IH].
    destruct (translate_expr e' seed') as [[[[[[]]]]]].
    exists seed1.
    destruct (translate_expr e seed1) as [[[[[[]]]]]].
    destruct IH.
    split.
    all: constructor 2; assumption.
Qed.

Lemma translate_init_wd {n_in n_out n_locals n_body} n_seed:
  Forall (fun eq => incl (Source.var_of_exp (projT2 (snd eq))) (n_in ++ n_out ++ n_locals)) n_body ->
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in ++ n_out ++ pre_binders ++ n_locals)) (init_eqs ++ init_post_eqs).
Proof.
  intros n_all_vars_exist.
  induction n_body as [|[eqid [eqty eqeq]] n_body IH].
  1: apply Forall_nil.
  simpl.
  specialize (IH (Forall_inv_tail n_all_vars_exist)).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed1] pre_binders] pre_eqs] init_post] step_post].
  assert (Hexpr := translate_expr_init_wd eqid seed1 (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_expr.
  clear - IH Hexpr.
  destruct (Target.raw_to_comb (expr_to_raw eqeq) seed1) as [[[[[[]]]]]]; cbn in *.
  apply Forall_app in IH.
  apply Forall_cons; [refine (incl_trans _ _ _ (Forall_inv Hexpr) _)|apply Forall_app; split; [|apply Forall_app; split]].
  2: refine (Forall_impl _ _ (proj1 IH)).
  3: refine (Forall_impl _ _ (Forall_inv_tail Hexpr)).
  4: refine (Forall_impl _ _ (proj2 IH)).
  1: clear; intros ? Hincl.
  2-4: clear; intros ? Hincl ? Hin; specialize (Hincl _ Hin); clear - Hincl.
  all: rewrite !in_app_iff in *; tauto.
Qed.

Lemma translate_pre_wd {n_in n_out n_locals n_body} n_seed:
  Forall (fun eq => incl (Source.var_of_exp (projT2 (snd eq))) (n_in ++ n_out ++ n_locals)) n_body ->
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Forall (fun eq => In (snd eq, snd (fst eq)) (n_in ++ n_out ++ pre_binders ++ n_locals)) pre_eqs.
Proof.
  intros n_all_vars_exist.
  induction n_body as [|[eqid [eqty eqeq]] n_body IH].
  1: apply Forall_nil.
  simpl.
  specialize (IH (Forall_inv_tail n_all_vars_exist)).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed1] pre_binders] pre_eqs] init_post] step_post].
  assert (Hexpr := translate_expr_pre_wd seed1 (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_expr.
  clear - IH Hexpr.
  destruct (Target.raw_to_comb (expr_to_raw eqeq) seed1) as [[[[[[]]]]]]; cbn in *.
  apply Forall_app; split.
  1: refine (Forall_impl _ _ Hexpr).
  2: refine (Forall_impl _ _ IH).
  all: clear; intros ? Hin; clear - Hin.
  all: rewrite !in_app_iff in *; tauto.
Qed.

Lemma translate_step_wd {n_in n_out n_locals n_body} n_seed:
  Forall (fun eq => incl (Source.var_of_exp (projT2 (snd eq))) (n_in ++ n_out ++ n_locals)) n_body ->
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) ((n_in ++ n_out ++ pre_binders ++ n_locals) ++ map fst pre_eqs)) (step_eqs ++ step_post_eqs).
Proof.
  intros n_all_vars_exist.
  induction n_body as [|[eqid [eqty eqeq]] n_body IH].
  1: apply Forall_nil.
  simpl.
  specialize (IH (Forall_inv_tail n_all_vars_exist)).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed1] pre_binders] pre_eqs] init_post] step_post].
  assert (Hexpr := translate_expr_step_wd eqid seed1 (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_expr.
  clear - IH Hexpr.
  destruct (Target.raw_to_comb (expr_to_raw eqeq) seed1) as [[[[[[]]]]]]; cbn in *.
  apply Forall_app in IH.
  apply Forall_cons; [refine (incl_trans _ _ _ (Forall_inv Hexpr) _)|apply Forall_app; split; [|apply Forall_app; split]].
  2: refine (Forall_impl _ _ (proj1 IH)).
  3: refine (Forall_impl _ _ (Forall_inv_tail Hexpr)).
  4: refine (Forall_impl _ _ (proj2 IH)).
  1: clear; intros ? Hincl.
  2-4: clear; intros ? Hincl ? Hin; specialize (Hincl _ Hin); clear - Hincl.
  all: rewrite ?map_app, !in_app_iff in *; tauto.
Qed.


Definition translate_node (node: Source.node) : Result.t type Target.node.
Proof.
  left. (* FIXME: check the timing before returning the node *)

  destruct node as [
    n_loc
    n_name

    n_in
    n_out
    n_locals
    n_body
    
    n_vars
    n_assigned_vars
    
    n_all_vars_exist
    n_vars_all_assigned
    n_vars_unique
    
    n_seed
    n_seed_always_fresh
  ].
  assert (init_assigned := translate_init_assigned n_seed n_vars_all_assigned).
  assert (step_assigned := translate_step_assigned n_seed n_vars_all_assigned).
  assert (vars_unique := translate_vars_unique n_body n_vars_unique n_seed_always_fresh).
  assert (fresh_seed := translate_seed_always_fresh n_body n_seed_always_fresh).
  assert (init_wd := translate_init_wd n_seed n_all_vars_exist).
  assert (pre_wd := translate_pre_wd n_seed n_all_vars_exist).
  assert (step_wd := translate_step_wd n_seed n_all_vars_exist).

  destruct (translate_equations n_body n_seed) as [
    [[[[[init_eqs
    step_eqs]
    new_seed]
    pre_binders]
    pre_eqs]
    init_post_eqs]
    step_post_eqs
  ].

  refine {|
    Target.n_loc := n_loc;
    Target.n_name := n_name;

    Target.n_in := n_in;
    Target.n_out := n_out;
    Target.n_locals := pre_binders ++ n_locals;
    Target.n_pre := pre_eqs;
    Target.n_init := init_eqs ++ init_post_eqs;
    Target.n_step := step_eqs ++ step_post_eqs;

    Target.n_seed := new_seed;
  |}.
  all: assumption.
Defined.


(* Semantics preservation *)
Theorem semantics_preservation_inv (n: Target.node) (n0: Source.node) (h: history):
  translate_node n0 = Result.Ok n -> Target.sem_node n h -> Source.sem_node n0 h.
Proof.
  intro translated.
  unfold translate_node in translated.
  apply Result.ok_eq in translated.
  destruct n0 as [n0_loc n0_name n0_in n0_out n0_locals n0_body n0_vars n0_assigned_vars n0_all_vars_exist n0_vars_all_assigned n0_vars_unique n0_seed n0_seed_always_fresh].
  remember (translate_init_assigned n0_seed n0_vars_all_assigned) as init_assigned eqn: tmp; clear tmp.
  remember (translate_step_assigned n0_seed n0_vars_all_assigned) as step_assigned eqn: tmp; clear tmp.
  remember (translate_vars_unique n0_body n0_vars_unique n0_seed_always_fresh) as vars_unique eqn: tmp; clear tmp.
  remember (translate_seed_always_fresh n0_body n0_seed_always_fresh) as seed_fresh eqn: tmp; clear tmp.
  remember (translate_init_wd n0_seed n0_all_vars_exist) as init_wd eqn: tmp; clear tmp.
  remember (translate_pre_wd n0_seed n0_all_vars_exist) as pre_wd eqn: tmp; clear tmp.
  remember (translate_step_wd n0_seed n0_all_vars_exist) as step_wd eqn: tmp; clear tmp.
  destruct (translate_equations n0_body n0_seed) as [[[[[[trans_init trans_step] trans_seed] trans_pre_binders] trans_pre_eqs] trans_init_eqs] trans_step_eqs] eqn: translation.
  subst.
  unfold Source.sem_node, Target.sem_node, Target.n_vars, Target.n_init, Target.n_in, Target.n_out, Target.n_locals, Target.n_step, Target.n_pre, Source.n_body.

  intro sem_target.
  intros idn ty expr s inbody ismapped time.

  specialize (sem_target idn ty) as [sem_target _].
  assert (id_is_var : In (idn, ty) (n0_in ++ n0_out ++ trans_pre_binders ++ n0_locals)).
  {
   assert (id_is_var2 : In (idn, ty) (n0_out ++ n0_locals)).
   2: apply in_or_app; right; apply in_or_app.
   2: apply in_app_or in id_is_var2; destruct id_is_var2.
   2: left; assumption.
   2: right; apply in_or_app; right; assumption.
   rewrite <- n0_vars_all_assigned.
   unfold n0_assigned_vars.
   apply (in_map Source.equation_dest) in inbody.
   unfold Source.equation_dest at 1 in inbody.
   unfold fst, snd, projT1 in inbody.
   assumption.
  }

  specialize (sem_target id_is_var).
  destruct sem_target as [s' [ismapped' sem_target]].
  assert (seq := h_maps_to_eq idn s' s h ismapped' ismapped).
  subst.

  destruct sem_target as [sem_init sem_step].

  apply in_split in inbody.
  destruct inbody as [body1 [body2]]; subst.

  assert (translate_app := translate_equations_app body1 ((idn, existT (fun ty : type => Source.exp ty) ty expr) :: body2) n0_seed).

  simpl in translate_app.

  unfold Source.equation in translate_app. (* Types... *)
  
  destruct (translate_equations body2 n0_seed) as [[[[[[init_eq2 step_eq2] seed2] pre_binders2] pre_eqs2] init_post2] step_post2].

  induction expr.
  - simpl in translate_app.
    destruct (translate_equations body1 seed2) as [[[[[[init_eq1 step_eq1] seed1] pre_binders1] pre_eqs1] init_post1] step_post1].
    rewrite translation in translate_app.
    injection translate_app as -> -> -> -> -> -> ->.
  (* I cannot find how to prove this*)
Admitted.
