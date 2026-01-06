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
    | Source.EConst l c => Target.Raw_EConst l c
    | Source.EVar l v => Target.Raw_EVar l v
    | Source.EIfte l e1 e2 e3 => Target.Raw_EIfte l (expr_to_raw e1) (expr_to_raw e2) (expr_to_raw e3)
    | Source.EUnop l u e => match u in Source.unop tin tout return Target.raw_exp tin -> Target.raw_exp tout with
      | Source.Uop_neg => fun e => Target.Raw_EUnop l Target.Uop_neg e
      | Source.Uop_not => fun e => Target.Raw_EUnop l Target.Uop_not e
      | Source.Uop_pre => fun e => Target.Raw_EPre l e
      end (expr_to_raw e)
    | Source.EBinop l b e1 e2 => match b in Source.binop ty1 ty2 tout return Target.raw_exp ty1 -> Target.raw_exp ty2 -> Target.raw_exp tout with
      | Source.Bop_and => fun e1 e2 => Target.Raw_EBinop l Target.Bop_and e1 e2
      | Source.Bop_or => fun e1 e2 => Target.Raw_EBinop l Target.Bop_or e1 e2
      | Source.Bop_xor => fun e1 e2 => Target.Raw_EBinop l Target.Bop_xor e1 e2
      | Source.Bop_plus => fun e1 e2 => Target.Raw_EBinop l Target.Bop_plus e1 e2
      | Source.Bop_minus => fun e1 e2 => Target.Raw_EBinop l Target.Bop_minus e1 e2
      | Source.Bop_mult => fun e1 e2 => Target.Raw_EBinop l Target.Bop_mult e1 e2
      | Source.Bop_div => fun e1 e2 => Target.Raw_EBinop l Target.Bop_div e1 e2
      | Source.Bop_eq => fun e1 e2 => Target.Raw_EBinop l Target.Bop_eq e1 e2
      | Source.Bop_neq => fun e1 e2 => Target.Raw_EBinop l Target.Bop_neq e1 e2
      | Source.Bop_le => fun e1 e2 => Target.Raw_EBinop l Target.Bop_le e1 e2
      | Source.Bop_lt => fun e1 e2 => Target.Raw_EBinop l Target.Bop_lt e1 e2
      | Source.Bop_ge => fun e1 e2 => Target.Raw_EBinop l Target.Bop_ge e1 e2
      | Source.Bop_gt => fun e1 e2 => Target.Raw_EBinop l Target.Bop_gt e1 e2
      | Source.Bop_arrow => fun e1 e2 => Target.Raw_EArrow l e1 e2
      end (expr_to_raw e1) (expr_to_raw e2)
  end.

Fixpoint eqs_to_raw (eqs: list Source.equation): list Target.raw_equation :=
  match eqs with
  | [] => []
  | eq::eqs => (match eq with
    | (ident, existT _ ty e) => (ident, existT _ ty (expr_to_raw e))
    end)::(eqs_to_raw eqs)
  end.

Lemma equation_conservation {ty} (i: ident) (e: Source.exp ty) (body: list Source.equation) :
  In (i, existT _ ty e) body -> In (i, existT _ ty (expr_to_raw e)) (eqs_to_raw body).
Proof.
  intro inbody.
  induction body as [| eq body IH].
  1: inversion inbody.
  simpl in inbody.
  destruct inbody as [iseq | inbody].
  2: specialize (IH inbody).
  2: right; assumption.
  clear IH.
  rewrite iseq.
  simpl.
  left.
  reflexivity.
Defined.

Lemma equation_conservation_inv {ty} (i: ident) (raw_e: Target.raw_exp ty) (body: list Source.equation) :
  In (i, existT _ ty raw_e) (eqs_to_raw body) -> exists e, In (i, existT _ ty e) body /\ raw_e = expr_to_raw e.
Proof.
  intro inraw.
  induction body as [| eq body IH].
  1: inversion inraw.
  simpl in inraw.
  destruct inraw as [iseq | inraw].
  2: specialize (IH inraw).
  2: destruct IH as [e [inbody israw]].
  2: exists e; split; [right|]; assumption.
  clear IH.
  destruct eq as [i' [ty' e]].
  injection iseq as -> -> iseq.
  apply sig2T_eq_type in iseq.
  subst.
  exists e.
  split; [left|]; reflexivity.
Defined.

Definition translate_raw {ty} (e: Target.raw_exp ty) (seed: ident): (
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
    Target.raw_to_comb e seed.

Lemma translate_raw_nextseed {ty} (e: Target.raw_exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) :=  translate_raw e seed in
  exists n, seed' = iter n next_ident seed.
Proof.
  destruct (translate_raw e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_nextseed translation).
Qed.

Lemma freshness_translate_raw {ty} (e: Target.raw_exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed in
  freshness seed' (pre_binders ++ map fst pre_eqs).
Proof.
  destruct (translate_raw e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.freshness_raw_to_comb translation).
Qed.

Lemma isnext_translate_expr {ty} (e: Target.raw_exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed in
  forall x, In x (map fst pre_binders ++ map (fun eq => fst (fst eq)) pre_eqs) -> exists n, x = iter n next_ident seed.
Proof.
  destruct (translate_raw e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.isnext_raw_to_comb translation).
Qed.

Lemma nodup_translate_expr {ty} (e: Target.raw_exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed in
  NoDup (map fst pre_binders ++ map (fun eq => fst (fst eq)) pre_eqs).
Proof.
  destruct (translate_raw e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.nodup_raw_to_comb translation).
Qed.

Lemma translate_expr_assigned_init {ty} (e: Target.raw_exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed in
  Permutation (map Target.equation_dest init_post) pre_binders.
Proof.
  destruct (translate_raw e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_assigned_init translation).
Qed.

Lemma translate_expr_assigned_step {ty} (e: Target.raw_exp ty) (seed: ident):
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed in
  Permutation (map Target.equation_dest step_post) pre_binders.
Proof.
  destruct (translate_raw e seed) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_assigned_step translation).
Qed.

Lemma translate_expr_init_wd v {ty} {e: Target.raw_exp ty} {n_in n_out n_locals} seed:
  incl (Target.var_of_raw_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in ++ n_out ++ pre_binders ++ n_locals)) ((v, existT _ ty ei) :: init_post).
Proof.
  intros Hwd; revert seed; induction e as [loc ty c|loc [ty b]|loc ty1 ty op e IH|loc ty1 ty2 ty op e1 IH1 e2 IH2|loc ty e1 IH1 e2 IH2 e3 IH3|loc ty e IH |loc ty e1 IH1 e2 IH2];
    intros seed; cbn; try (constructor; [|constructor]).
  - intros ? [].
  - exact Hwd.
  - destruct op; cbn.
    all: specialize (IH Hwd seed); unfold translate_raw in IH.
    all: destruct (Target.raw_to_comb e seed) as [[[[[[]]]]]].
    all: constructor; [exact (Forall_inv IH)|exact (Forall_inv_tail IH)].
  - cbn in Hwd; rewrite Target.var_of_raw_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h)))).
    clear Hwd; unfold translate_raw in IH1, IH2.
    destruct op; cbn.
    all: destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    all: specialize (IH2 seed2).
    all: destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed']]]]]; clear e2.
    all: constructor; [|apply Forall_app; split; [refine (Forall_impl _ _ (Forall_inv_tail IH1))|refine (Forall_impl _ _ (Forall_inv_tail IH2))]].
    2,3,5,6,8,9,11,12,14,15,17,18,20,21,23,24,26,27,29,30,32,33,35,36,38,39: clear; intros ? Hincl ? Hin.
    2-27: specialize (Hincl _ Hin); cbn; rewrite !in_app_iff in *; tauto.
    all: cbn; rewrite Target.var_of_exp_aux_eq.
    all: apply incl_app; [refine (incl_trans _ _ _ (Forall_inv IH1) _)|refine (incl_trans _ _ _ (Forall_inv IH2) _)]; cbn.
    all: apply incl_app_app; [apply incl_refl|].
    all: apply incl_app_app; [apply incl_refl|].
    all: apply incl_app_app; [|apply incl_refl].
    all: intros ? h; apply in_or_app; tauto.
  - cbn in Hwd; rewrite 2!Target.var_of_raw_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl h)))))).
    specialize (IH3 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror h)))))).
    clear Hwd; unfold translate_raw in IH1, IH2, IH3.
    destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed3]]]]]; clear e2.
    specialize (IH3 seed3).
    destruct (Target.raw_to_comb e3 seed3) as [[[[[[] seed']]]]]; clear e3.
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
  - specialize (IH Hwd seed); unfold translate_raw in IH.
    destruct (Target.raw_to_comb e seed) as [[[[[[]]]]]].
    constructor; [|constructor].
    + intros ? [<-|[]]; apply in_or_app, or_intror, in_or_app, or_intror; left; exact eq_refl.
    + refine (incl_trans _ _ _ (Forall_inv IH) _).
      cbn.
      apply incl_app_app; [apply incl_refl|].
      apply incl_app_app; [apply incl_refl|].
      intros ? h; right; exact h.
    + refine (Forall_impl _ _ (Forall_inv_tail IH)).
      clear; intros ? Hincl ? Hin.
      specialize (Hincl _ Hin).
      rewrite !in_app_iff in *; cbn; tauto.
  - cbn in Hwd; rewrite Target.var_of_raw_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h)))).
    clear Hwd; unfold translate_raw in IH1, IH2.
    destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed']]]]]; clear e2.
    constructor; [|apply Forall_app; split].
    + refine (incl_trans _ _ _ (Forall_inv IH1) _).
      cbn.
      apply incl_app_app; [apply incl_refl|].
      apply incl_app_app; [apply incl_refl|].
      apply incl_app_app; [|apply incl_refl].
      intros ? h; apply in_or_app; left; exact h.
    + refine (Forall_impl _ _ (Forall_inv_tail IH1)).
      clear; intros ? Hincl ? Hin.
      specialize (Hincl _ Hin).
      cbn; rewrite !in_app_iff in *; tauto.
    + refine (Forall_impl _ _ (Forall_inv_tail IH2)).
      clear; intros ? Hincl ? Hin.
      specialize (Hincl _ Hin).
      cbn; rewrite !in_app_iff in *; tauto.
Qed.

Lemma translate_expr_pre_wd {ty} {e: Target.raw_exp ty} {n_in n_out n_locals} seed:
  incl (Target.var_of_raw_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed in
  Forall (fun eq => In (snd eq, snd (fst eq)) (n_in ++ n_out ++ pre_binders ++ n_locals)) pre_eqs.
Proof.
  intros _; revert seed; induction e as [loc ty c|loc [ty b]|loc ty1 ty op e IH|loc ty1 ty2 ty op e1 IH1 e2 IH2|loc ty e1 IH1 e2 IH2 e3 IH3|loc ty e IH|loc ty e1 IH1 e2 IH2];
    intros seed; cbn; try (constructor; [|constructor]).
  - apply Forall_nil.
  - apply Forall_nil.
  - destruct op; cbn.
    all: specialize (IH seed); unfold translate_raw in IH.
    all: destruct (Target.raw_to_comb e seed) as [[[[[[]]]]]].
    all: exact IH.
  - specialize (IH1 seed).
    unfold translate_raw in IH1, IH2.
    destruct op; cbn.
    all: destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    all: specialize (IH2 seed2).
    all: destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed']]]]]; clear e2.
    all: apply Forall_app; split; [refine (Forall_impl _ _ IH1)|refine (Forall_impl _ _ IH2)].
    all: clear; intros ? Hin.
    all: rewrite !in_app_iff in *; tauto.
  - unfold translate_raw in IH1, IH2, IH3.
    specialize (IH1 seed).
    destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed3]]]]]; clear e2.
    specialize (IH3 seed3).
    destruct (Target.raw_to_comb e3 seed3) as [[[[[[] seed']]]]]; clear e3.
    apply Forall_app; split; [|apply Forall_app; split].
    1: refine (Forall_impl _ _ IH1).
    2: refine (Forall_impl _ _ IH2).
    3: refine (Forall_impl _ _ IH3).
    all: clear; intros ? Hin.
    all: rewrite !in_app_iff in *; tauto.
  - all: specialize (IH seed); unfold translate_raw in IH.
    all: destruct (Target.raw_to_comb e seed) as [[[[[[]]]]]].
    constructor; [|refine (Forall_impl _ _ IH)].
    2: clear; cbn; intros ? Hin; cbn; rewrite !in_app_iff in *; cbn; rewrite in_app_iff; tauto.
    apply in_or_app, or_intror, in_or_app, or_intror; left; exact eq_refl.
  - specialize (IH1 seed).
    unfold translate_raw in IH1, IH2.
    destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed']]]]]; clear e2.
    apply Forall_app; split; [refine (Forall_impl _ _ IH1)|refine (Forall_impl _ _ IH2)].
    all: clear; intros ? Hin.
    all: rewrite !in_app_iff in *; tauto.
Qed.

Lemma translate_expr_step_wd v {ty} {e: Target.raw_exp ty} {n_in n_out n_locals} seed:
  incl (Target.var_of_raw_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) ((n_in ++ n_out ++ pre_binders ++ n_locals) ++ map fst pre_eqs))
    ((v, existT _ ty es) :: step_post).
Proof.
  intros Hwd; revert seed; induction e as [loc ty c|loc [ty b]|loc ty1 ty op e IH|loc ty1 ty2 ty op e1 IH1 e2 IH2|loc ty e1 IH1 e2 IH2 e3 IH3|loc ty e IH|loc ty e1 IH1 e2 IH2];
    intros seed; cbn; try (constructor; [|constructor]).
  - intros ? [].
  - rewrite app_nil_r; exact Hwd.
  - destruct op; cbn.
    all: specialize (IH Hwd seed); unfold translate_raw in IH.
    all: destruct (Target.raw_to_comb e seed) as [[[[[[]]]]]].
    all: constructor; [exact (Forall_inv IH)|exact (Forall_inv_tail IH)].
  - cbn in Hwd; rewrite Target.var_of_raw_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h)))).
    clear Hwd; unfold translate_raw in IH1, IH2.
    destruct op; cbn.
    all: destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    all: specialize (IH2 seed2).
    all: destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed']]]]]; clear e2.
    all: constructor; [|apply Forall_app; split; [refine (Forall_impl _ _ (Forall_inv_tail IH1))|refine (Forall_impl _ _ (Forall_inv_tail IH2))]].
    2,3,5,6,8,9,11,12,14,15,17,18,20,21,23,24,26,27,29,30,32,33,35,36,38,39: clear; intros ? Hincl ? Hin.
    2-27: specialize (Hincl _ Hin); cbn; rewrite map_app, !in_app_iff in *; tauto.
    all: cbn; rewrite Target.var_of_exp_aux_eq.
    all: apply incl_app; [refine (incl_trans _ _ _ (Forall_inv IH1) _)|refine (incl_trans _ _ _ (Forall_inv IH2) _)]; cbn.
    all: apply incl_app_app; [|intros ? h; rewrite map_app; apply in_or_app; tauto].
    all: do 2 (apply incl_app_app; [apply incl_refl|]).
    all: apply incl_app_app; [|apply incl_refl].
    all: intros ? h; apply in_or_app; tauto.
  - cbn in Hwd; rewrite 2!Target.var_of_raw_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl h)))))).
    specialize (IH3 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror h)))))).
    clear Hwd; unfold translate_raw in IH1, IH2, IH3.
    destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed3]]]]]; clear e2.
    specialize (IH3 seed3).
    destruct (Target.raw_to_comb e3 seed3) as [[[[[[] seed']]]]]; clear e3.
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
  - specialize (IH Hwd seed); unfold translate_raw in IH.
    destruct (Target.raw_to_comb e seed) as [[[[[[]]]]]].
    constructor; [|constructor].
    + intros ? [<-|[]]; apply in_or_app; right; left; exact eq_refl.
    + refine (incl_trans _ _ _ (Forall_inv IH) _).
      cbn.
      apply incl_app_app; [|intros ? h; right; exact h].
      do 2 (apply incl_app_app; [apply incl_refl|]).
      intros ? h; right; exact h.
    + refine (Forall_impl _ _ (Forall_inv_tail IH)).
      clear; intros ? Hincl ? Hin.
      specialize (Hincl _ Hin).
      rewrite !in_app_iff in *; cbn; tauto.
  - cbn in Hwd; rewrite Target.var_of_raw_exp_aux_eq in Hwd.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) seed).
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h)))).
    clear Hwd; unfold translate_raw in IH1, IH2.
    destruct (Target.raw_to_comb e1 seed) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 seed2).
    destruct (Target.raw_to_comb e2 seed2) as [[[[[[] seed']]]]]; clear e2.
    constructor; [|apply Forall_app; split].
    + refine (incl_trans _ _ _ (Forall_inv IH2) _).
      apply incl_app_app; [|intros ? h; rewrite map_app; apply in_or_app; right; exact h].
      do 2 (apply incl_app_app; [apply incl_refl|]).
      apply incl_app_app; [|apply incl_refl].
      intros ? h; apply in_or_app; right; exact h.
    + refine (Forall_impl _ _ (Forall_inv_tail IH1)).
      clear; intros ? Hincl ? Hin.
      specialize (Hincl _ Hin).
      cbn; rewrite map_app, !in_app_iff in *; tauto.
    + refine (Forall_impl _ _ (Forall_inv_tail IH2)).
      clear; intros ? Hincl ? Hin.
      specialize (Hincl _ Hin).
      cbn; rewrite map_app, !in_app_iff in *; tauto.
Qed.

Fixpoint translate_equations (eqs: list Target.raw_equation) (seed: ident): (
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
          let '(ei, es, seed2, pre_binders1, pre_eqs1, init_post1, step_post1) := translate_raw e seed1 in
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

Lemma translate_equations_nextseed (eqs: list Target.raw_equation) (seed: ident):
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
    specialize (translate_raw_nextseed expr seed0) as unfoldseed.
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    destruct unfoldseed as [nexpr seedexpr].
    destruct IH as [nIH IH].
    rewrite IH in seedexpr.
    rewrite <- Nat.iter_add in seedexpr.
    exists (nexpr + nIH).
    assumption.
Qed.

Lemma freshness_translate_equations (eqs: list Target.raw_equation) (seed: ident):
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
    assert (freshness_expr := freshness_translate_raw expr seed0).
    assert (nextseed_expr := translate_raw_nextseed expr seed0).
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    apply (freshness_later_e nextseed_expr) in IH.
    refine (freshness_permutation (freshness_fusion freshness_expr IH) _).
    rewrite map_app, !app_assoc; apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head, Permutation_app_comm.
Qed.

Lemma isnext_translate_equations (eqs: list Target.raw_equation) (seed: ident):
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
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
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

Lemma nodup_translate_equations (eqs: list Target.raw_equation) (seed: ident):
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
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
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

Lemma translate_equations_assigned_init (eqs: list Target.raw_equation) (seed: ident):
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
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_app, IH, perm_expr; apply Permutation_refl.
Qed.

Lemma translate_equations_assigned_step (eqs: list Target.raw_equation) (seed: ident):
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
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_app, IH, perm_expr; apply Permutation_refl.
Qed.

Lemma translate_equations_conservation_init (eqs: list Target.raw_equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  map Target.raw_equation_dest eqs = map Target.equation_dest init_eqs.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    reflexivity.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_cons.
    unfold Target.raw_equation_dest at 1, Target.equation_dest at 1, fst, snd, projT1.
    rewrite IH.
    reflexivity.
Qed.

Lemma translate_equations_conservation_step (eqs: list Target.raw_equation) (seed: ident):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  map Target.raw_equation_dest eqs = map Target.equation_dest step_eqs.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    reflexivity.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_cons.
    unfold Target.raw_equation_dest at 1, Target.equation_dest at 1, fst, snd, projT1.
    rewrite IH.
    reflexivity.
Qed.

Lemma translate_init_assigned {n_body n_out n_locals} (n_seed: ident)
  (n_vars_all_assigned : Permutation (map Target.raw_equation_dest n_body) (n_out ++ n_locals)) :
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Permutation (map Target.equation_dest (init_eqs ++ init_post_eqs)) (n_out ++ pre_binders ++ n_locals).
Proof.
  assert (conservation_init := translate_equations_conservation_init n_body n_seed).
  assert (assigned_init := translate_equations_assigned_init n_body n_seed).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  rewrite map_app.
  rewrite <- conservation_init.
  rewrite (Permutation_app_comm (map Target.raw_equation_dest n_body)).
  rewrite !app_assoc.
  rewrite (Permutation_app_comm n_out).
  rewrite <- !app_assoc.
  rewrite <- n_vars_all_assigned.
  apply Permutation_app.
  2: apply Permutation_refl.
  assumption.
Qed.

Lemma translate_step_assigned {n_body n_out n_locals} (n_seed: ident)
  (n_vars_all_assigned : Permutation (map Target.raw_equation_dest n_body) (n_out ++ n_locals)) :
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Permutation (map Target.equation_dest (step_eqs ++ step_post_eqs)) (n_out ++ pre_binders ++ n_locals).
Proof.
  assert (conservation_step := translate_equations_conservation_step n_body n_seed).
  assert (assigned_step := translate_equations_assigned_step n_body n_seed).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  rewrite map_app.
  rewrite <- conservation_step.
  rewrite (Permutation_app_comm (map Target.raw_equation_dest n_body)).
  rewrite !app_assoc.
  rewrite (Permutation_app_comm n_out).
  rewrite <- !app_assoc.
  rewrite <- n_vars_all_assigned.
  apply Permutation_app.
  2: apply Permutation_refl.
  assumption.
Qed.

Lemma translate_vars_unique {n_in n_out n_locals n_seed} (n_body: list Target.raw_equation)
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

Lemma translate_seed_always_fresh {n_in n_out n_locals n_seed} (n_body: list Target.raw_equation)
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
  let '(ei, es, seed2, pre_binders1, pre_eqs1, init_post1, step_post1) := translate_raw e seed1 in
    In (ident, existT _ ty ei) init_eqs /\
    In (ident, existT _ ty es) step_eqs.
Proof.
  induction n_body as [|eq' n_body IH].
  1: contradiction.
  simpl.
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  intros [|isin]; subst.
  all: destruct eq as [ident [ty e]].
  - destruct (translate_raw e seed') as [[[[[[ei1 es1] seed1] binders1] pre_eqs1] init_post1] step_post1] eqn: translation.
    exists seed'.
    destruct (translate_raw e seed') as [[[[[[]]]]]].
    injection translation as <- <- <- <- <- <- <-.
    split.
    all: constructor 1.
    all: reflexivity.
  - destruct eq' as [ident' [ty' e']].
    specialize (IH isin).
    destruct IH as [seed1 IH].
    destruct (translate_raw e' seed') as [[[[[[]]]]]].
    exists seed1.
    destruct (translate_raw e seed1) as [[[[[[]]]]]].
    destruct IH.
    split.
    all: constructor 2; assumption.
Qed.

Lemma translate_init_wd {n_in n_out n_locals n_body} n_seed:
  Forall (fun eq => incl (Target.var_of_raw_exp (projT2 (snd eq))) (n_in ++ n_out ++ n_locals)) n_body ->
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in ++ n_out ++ pre_binders ++ n_locals)) (init_eqs ++ init_post_eqs).
Proof.
  intros n_all_vars_exist.
  induction n_body as [|[eqid [eqty eqeq]] n_body IH].
  1: apply Forall_nil.
  simpl.
  specialize (IH (Forall_inv_tail n_all_vars_exist)).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed1] pre_binders] pre_eqs] init_post] step_post].
  assert (Hexpr := translate_expr_init_wd eqid seed1 (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_raw.
  clear - IH Hexpr.
  destruct (Target.raw_to_comb eqeq seed1) as [[[[[[]]]]]]; cbn in *.
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
  Forall (fun eq => incl (Target.var_of_raw_exp (projT2 (snd eq))) (n_in ++ n_out ++ n_locals)) n_body ->
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Forall (fun eq => In (snd eq, snd (fst eq)) (n_in ++ n_out ++ pre_binders ++ n_locals)) pre_eqs.
Proof.
  intros n_all_vars_exist.
  induction n_body as [|[eqid [eqty eqeq]] n_body IH].
  1: apply Forall_nil.
  simpl.
  specialize (IH (Forall_inv_tail n_all_vars_exist)).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed1] pre_binders] pre_eqs] init_post] step_post].
  assert (Hexpr := translate_expr_pre_wd seed1 (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_raw.
  clear - IH Hexpr.
  destruct (Target.raw_to_comb eqeq seed1) as [[[[[[]]]]]]; cbn in *.
  apply Forall_app; split.
  1: refine (Forall_impl _ _ Hexpr).
  2: refine (Forall_impl _ _ IH).
  all: clear; intros ? Hin; clear - Hin.
  all: rewrite !in_app_iff in *; tauto.
Qed.

Lemma translate_step_wd {n_in n_out n_locals n_body} n_seed:
  Forall (fun eq => incl (Target.var_of_raw_exp (projT2 (snd eq))) (n_in ++ n_out ++ n_locals)) n_body ->
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) ((n_in ++ n_out ++ pre_binders ++ n_locals) ++ map fst pre_eqs)) (step_eqs ++ step_post_eqs).
Proof.
  intros n_all_vars_exist.
  induction n_body as [|[eqid [eqty eqeq]] n_body IH].
  1: apply Forall_nil.
  simpl.
  specialize (IH (Forall_inv_tail n_all_vars_exist)).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed1] pre_binders] pre_eqs] init_post] step_post].
  assert (Hexpr := translate_expr_step_wd eqid seed1 (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_raw.
  clear - IH Hexpr.
  destruct (Target.raw_to_comb eqeq seed1) as [[[[[[]]]]]]; cbn in *.
  apply Forall_app in IH.
  apply Forall_cons; [refine (incl_trans _ _ _ (Forall_inv Hexpr) _)|apply Forall_app; split; [|apply Forall_app; split]].
  2: refine (Forall_impl _ _ (proj1 IH)).
  3: refine (Forall_impl _ _ (Forall_inv_tail Hexpr)).
  4: refine (Forall_impl _ _ (proj2 IH)).
  1: clear; intros ? Hincl.
  2-4: clear; intros ? Hincl ? Hin; specialize (Hincl _ Hin); clear - Hincl.
  all: rewrite ?map_app, !in_app_iff in *; tauto.
Qed.

Lemma equation_dest_conservation (body: list Source.equation) :
  map Source.equation_dest body = map Target.raw_equation_dest (eqs_to_raw body).
Proof.
  induction body as [|[ident [ty eq]] body IH].
  1: reflexivity.
  simpl.
  rewrite IH.
  unfold Source.equation_dest, Target.raw_equation_dest at 2.
  simpl.
  reflexivity.
Qed.

Definition translate_to_raw_node (node: Source.node) : Result.t type Target.raw_node.
Proof.
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

  remember (eqs_to_raw n_body) as new_body eqn: translation.

  destruct (Target.timed_list_eq n_name new_body) as [timed_body | err].
  2: right; exact err.
  left.

  refine {|
    Target.rn_loc := n_loc;
    Target.rn_name := n_name;

    Target.rn_in := n_in;
    Target.rn_out := n_out;
    Target.rn_locals := n_locals;
    Target.rn_body := new_body;
    
    Target.rn_vars_unique := n_vars_unique;

    Target.rn_seed := n_seed;
    Target.rn_seed_always_fresh := n_seed_always_fresh;

    Target.rn_well_timed := timed_body;
  |}.

  all: clear -n_all_vars_exist n_vars_all_assigned translation.

  - clear n_vars_all_assigned.
    induction n_body as [| [ident [ty eq]] n_body IH] in new_body, translation, n_assigned_vars, n_all_vars_exist |- *.
    1: simpl in translation; subst; constructor.
    simpl in translation.
    subst.
    constructor.
    2: {
      apply IH.
      2: reflexivity.
      apply Forall_inv_tail in n_all_vars_exist.
      assumption.
    }
    clear IH.
    apply Forall_inv in n_all_vars_exist.
    simpl in n_all_vars_exist.
    induction eq as [loc c | loc v | loc ty1 ty2 u e IH | loc ty1 ty2 ty3 b e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3].
    + simpl.
      unfold Target.var_of_raw_exp, Target.var_of_raw_exp_aux.
      apply incl_nil_l.
    + simpl.
      unfold Target.var_of_raw_exp, Target.var_of_raw_exp_aux.
      unfold Source.var_of_exp in n_all_vars_exist.
      simpl in n_all_vars_exist.
      assumption.
    + simpl.
      unfold Source.var_of_exp in n_all_vars_exist.
      simpl in n_all_vars_exist.
      rewrite Source.var_of_exp_aux_eq, app_nil_r in n_all_vars_exist.
      apply IH in n_all_vars_exist.
      clear IH.
      simpl in n_all_vars_exist.
      destruct u.
      all: unfold Target.var_of_raw_exp; simpl.
      all: rewrite Target.var_of_raw_exp_aux_eq, app_nil_r.
      all: assumption.
    + unfold Source.var_of_exp in n_all_vars_exist.
      simpl in IH1, IH2, n_all_vars_exist.
      rewrite 2!Source.var_of_exp_aux_eq, app_nil_r in n_all_vars_exist.
      apply incl_app_inv in n_all_vars_exist.
      destruct n_all_vars_exist as [vars1_exist vars2_exist].
      apply IH1 in vars1_exist.
      apply IH2 in vars2_exist.
      clear IH1 IH2.
      destruct b.
      all: unfold Target.var_of_raw_exp; simpl.
      all: rewrite 2!Target.var_of_raw_exp_aux_eq, app_nil_r.
      all: apply incl_app.
      all: assumption.
    + unfold Source.var_of_exp in n_all_vars_exist.
      simpl in IH1, IH2, IH3, n_all_vars_exist.
      rewrite 3!Source.var_of_exp_aux_eq, app_nil_r in n_all_vars_exist.
      apply incl_app_inv in n_all_vars_exist.
      destruct n_all_vars_exist as [vars1_exist tmp].
      apply incl_app_inv in tmp.
      destruct tmp as [vars2_exist vars3_exist].
      apply IH1 in vars1_exist.
      apply IH2 in vars2_exist.
      apply IH3 in vars3_exist.
      clear IH1 IH2 IH3.
      unfold Target.var_of_raw_exp; simpl.
      rewrite 3!Target.var_of_raw_exp_aux_eq, app_nil_r.
      apply incl_app; [ | apply incl_app].
      all: assumption.
  - rewrite translation, <- equation_dest_conservation.
    assumption.
Defined.


Definition translate_raw_to_node (node: Target.raw_node) : Target.node.
Proof.

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

Definition translate_node (node: Source.node) : Result.t type Target.node.
Proof.
  destruct (translate_to_raw_node node) as [raw_node | err].
  2: right; exact err.
  left.
  exact (translate_raw_to_node raw_node).
Defined.

Property raw_expr_complete {ty} (h: history) (t: nat) (e: Source.exp ty) (v: value ty):
  Source.sem_exp h t e v -> Target.sem_raw_exp h t (expr_to_raw e) v.
Proof.
  generalize dependent t.
  induction e as [loc ty c|loc b | loc tyin tyout u e IH | loc ty1 ty2 tyout b e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3].
  all: intros t sem_source; simpl.
  - inversion sem_source; subst.
    apply sig2T_eq_type in H3; subst.
    apply sig2T_eq_type in H4.
    rewrite <- H4.
    constructor.
  - inversion sem_source; subst.
    apply sig2T_eq_type in H5; subst.
    constructor.
    assumption.
  - destruct u.
    all: inversion sem_source; subst.
    1-3: do 2 apply sig2T_eq_type in H4.
    1-3: apply sig2T_eq_type in H5, H6.
    1-3: subst.
    1-3: inversion H7.
    1-2: apply sig2T_eq_type in H, H0; subst.
    1-2: specialize (IH vin _ H3).
    1-2: econstructor.
    1,3: apply IH.
    1-2: constructor.
    + apply sig2T_eq_type in H1, H2; subst.
      constructor.
      specialize (IH _ _ H3).
      assumption.
  - destruct b.
    all: inversion sem_source; subst.
    1-14: do 3 apply sig2T_eq_type in H5.
    1-14: apply sig2T_eq_type in H6, H7, H8.
    1-14: subst.
    1-14: inversion H10.
    1-13: apply sig2T_eq_type in H, H0, H1; subst.
    1-13: specialize (IH1 _ _ H4).
    1-13: specialize (IH2 _ _ H9).
    1-13: econstructor.
    all: try apply IH1.
    all: try apply IH2.
    all: try constructor.
    all: apply sig2T_eq_type in H1, H3, H4; subst.
    + specialize (IH1 _ _ H2).
      assumption.
    + specialize (IH2 _ _ H2).
      assumption.
  - inversion sem_source.
    apply sig2T_eq_type in H1, H5, H6; subst.
    specialize (IH1 _ _ H4).
    specialize (IH2 _ _ H7).
    specialize (IH3 _ _ H8).
    constructor; assumption.
Qed.

Property raw_expr_correct {ty} (h: history) (t: nat) (e: Source.exp ty) (v: value ty):
  Target.sem_raw_exp h t (expr_to_raw e) v -> Source.sem_exp h t e v.
Proof.
  generalize dependent t.
  induction e as [loc ty c|loc b | loc tyin tyout u e IH | loc ty1 ty2 tyout b e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3].
  all: intros t sem_target; simpl.
  - inversion sem_target; subst.
    apply sig2T_eq_type in H3, H4; subst.
    constructor.
  - inversion sem_target; subst.
    apply sig2T_eq_type in H5; subst.
    constructor.
    assumption.
  - destruct u.
    all: inversion sem_target; subst.
    1-2: do 2 apply sig2T_eq_type in H4.
    1-2: apply sig2T_eq_type in H5, H6.
    1-2: subst.
    1-2: specialize (IH _ _ H3).
    1-2: inversion H7.
    1-2: apply sig2T_eq_type in H, H0; subst.
    1-2: econstructor.
    1,3: apply IH.
    1,2: constructor.

    apply sig2T_eq_type in H3, H4; subst.
    specialize (IH _ _ H2).
    constructor.
    assumption.
  - destruct b.
    all: inversion sem_target; subst.
    1-13: do 3 apply sig2T_eq_type in H5.
    1-13: apply sig2T_eq_type in H6, H7, H8.
    1-13: subst.
    1-13: specialize (IH1 _ _ H4).
    1-13: specialize (IH2 _ _ H9).
    1-13: inversion H10.
    1-13: apply sig2T_eq_type in H, H0, H1; subst.
    1-13: econstructor.
    all: try apply IH1.
    all: try apply IH2.
    all: try constructor.
    all: apply sig2T_eq_type in H3, H4, H5; subst.
    + apply IH1.
      assumption.
    + apply IH2.
      assumption.
  - inversion sem_target.
    apply sig2T_eq_type in H1, H5, H6.
    subst.
    specialize (IH1 _ _ H4).
    specialize (IH2 _ _ H7).
    specialize (IH3 _ _ H8).
    constructor; assumption.
Qed.

Theorem raw_translation_complete (n: Target.raw_node) (n0: Source.node) (h: history):
  translate_to_raw_node n0 = Result.Ok n -> Source.sem_node n0 h -> Target.sem_raw_node n h.
Proof.
  intro translated.
  unfold translate_to_raw_node in translated.
  destruct n0 as [n0_loc n0_name n0_in n0_out n0_locals n0_body n0_vars n0_assigned_vars n0_all_vars_exist n0_vars_all_assigned n0_vars_unique n0_seed n0_seed_always_fresh].
  destruct (Target.timed_list_eq n0_name (eqs_to_raw n0_body)) as [timed_body | err].
  2: inversion translated.
  apply Result.ok_eq in translated.
  rewrite <- translated.
  clear translated.
  unfold Source.sem_node, Source.n_vars, Source.n_in, Source.n_out, Source.n_locals, Source.n_body, Target.sem_raw_node, Target.rn_vars, Target.rn_in, Target.rn_out, Target.rn_locals, Target.rn_body.

  intro sem_source.
  intros ident ty is_var.
  specialize (sem_source ident ty is_var).
  destruct sem_source as [s [mapped sem_source]].
  exists s.
  split.
  1: exact mapped.
  intros raw_e is_eq t.

  assert (in_body := equation_conservation_inv ident raw_e n0_body is_eq).
  destruct in_body as [e [in_body israw]].
  specialize (sem_source e in_body t).
  rewrite israw.
  apply raw_expr_complete.
  assumption.
Qed.

Theorem raw_translation_correct (n: Target.raw_node) (n0: Source.node) (h: history):
  translate_to_raw_node n0 = Result.Ok n -> Target.sem_raw_node n h -> Source.sem_node n0 h.
Proof.
  intro translated.
  unfold translate_to_raw_node in translated.
  destruct n0 as [n0_loc n0_name n0_in n0_out n0_locals n0_body n0_vars n0_assigned_vars n0_all_vars_exist n0_vars_all_assigned n0_vars_unique n0_seed n0_seed_always_fresh].
  destruct (Target.timed_list_eq n0_name (eqs_to_raw n0_body)) as [timed_body | err].
  2: inversion translated.
  apply Result.ok_eq in translated.
  rewrite <- translated.
  clear translated.
  unfold Source.sem_node, Source.n_vars, Source.n_in, Source.n_out, Source.n_locals, Source.n_body, Target.sem_raw_node, Target.rn_vars, Target.rn_in, Target.rn_out, Target.rn_locals, Target.rn_body.

  intro sem_target.
  intros ident ty is_var.
  specialize (sem_target ident ty is_var).
  destruct sem_target as [s [mapped sem_target]].
  exists s.
  split.
  1: exact mapped.
  intros e is_eq t.

  assert (in_body := equation_conservation ident e n0_body is_eq).
  specialize (sem_target (expr_to_raw e) in_body t).
  apply raw_expr_correct.
  assumption.
Qed.

(* Semantics preservation *)
(* TODO *)
Theorem semantics_preservation_inv (n: Target.node) (n0: Source.node) (h: history):
  translate_node n0 = Result.Ok n -> Target.sem_node n h -> Source.sem_node n0 h.
Proof.
Admitted.
(*
  intro translated.
  unfold translate_node, translate_to_raw_node in translated.
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

  specialize (sem_target idn ty) as [sem_target sem_target_pre].
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
  
Admitted.
*)
