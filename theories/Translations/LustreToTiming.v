Set Default Goal Selector "!".

From Reactive.Props Require Import Identifier Inclusion Permutations.
From Reactive.Languages Require Lustre LustreTiming.
From Reactive.Languages Require Import Freshness Semantics.

From Stdlib Require Import List Nat Permutation String.
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

Definition eq_to_raw '((ident, existT _ ty e): Source.equation): Target.raw_equation := (ident, existT _ ty (expr_to_raw e)).
Definition eqs_to_raw: list Source.equation -> list Target.raw_equation := List.map eq_to_raw.

Lemma equation_conservation {ty} i (e: Source.exp ty) (body: list Source.equation) :
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

Lemma equation_conservation_inv {ty} i (raw_e: Target.raw_exp ty) (body: list Source.equation) :
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

Definition translate_raw {ty} (e: Target.raw_exp ty) (seed: seed_ty) s: (
    Target.comb_exp ty (* init *)
    * Target.comb_exp ty (* step *)
    * ident (* New identifier origin *)
    * list binder (* Variables created for pre *)
    * list (binder * (string * ident)) (* pre equations *)
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
    Target.raw_to_comb e seed s.

Lemma translate_raw_nextseed {ty} (e: Target.raw_exp ty) (seed: seed_ty) s:
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  exists aux, seed' = fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed.
Proof.
  destruct (translate_raw e seed s) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_nextseed translation).
Qed.

Lemma freshness_translate_raw {ty} (e: Target.raw_exp ty) (seed: seed_ty) s:
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  freshness seed' (pre_binders ++ map fst pre_eqs).
Proof.
  destruct (translate_raw e seed s) as [[[[[[]]]]]] eqn: translation.
  apply (Target.freshness_raw_to_comb translation).
Qed.

Lemma isnext_translate_expr {ty} (e: Target.raw_exp ty) (seed: seed_ty) s:
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  forall x, In x (pre_binders ++ map fst pre_eqs) ->
  exists aux vn vt, x = snd (next_ident (fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed) vn vt).
Proof.
  destruct (translate_raw e seed s) as [[[[[[]]]]]] eqn: translation.
  apply (Target.isnext_raw_to_comb translation).
Qed.

Lemma nodup_translate_expr {ty} (e: Target.raw_exp ty) (seed: seed_ty) s:
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  NoDup (map binder_id pre_binders ++ map (fun eq => binder_id (fst eq)) pre_eqs).
Proof.
  destruct (translate_raw e seed s) as [[[[[[]]]]]] eqn: translation.
  apply (Target.nodup_raw_to_comb translation).
Qed.

Lemma translate_expr_assigned_init {ty} (e: Target.raw_exp ty) (seed: seed_ty) s:
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  Permutation (map Target.equation_dest init_post) pre_binders.
Proof.
  destruct (translate_raw e seed s) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_assigned_init translation).
Qed.

Lemma translate_expr_assigned_step {ty} (e: Target.raw_exp ty) (seed: seed_ty) s:
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  Permutation (map Target.equation_dest step_post) pre_binders.
Proof.
  destruct (translate_raw e seed s) as [[[[[[]]]]]] eqn: translation.
  apply (Target.raw_to_comb_assigned_step translation).
Qed.

Lemma translate_expr_init_wd v {ty} {e: Target.raw_exp ty} {n_in n_out n_locals} seed s:
  incl (Target.var_of_raw_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in ++ n_out ++ pre_binders ++ n_locals)) ((v, existT _ ty ei) :: init_post).
Proof.
  intros Hwd; revert s seed;
    induction e as [loc ty c|loc [ty b]|loc ty1 ty op e IH|loc ty1 ty2 ty op e1 IH1 e2 IH2|loc ty e1 IH1 e2 IH2 e3 IH3|loc ty e IH |loc ty e1 IH1 e2 IH2];
    intros s seed; try (constructor; [|constructor]).
  - intros ? [].
  - exact Hwd.
  - destruct op; cbn.
    all: specialize (IH Hwd s seed); unfold translate_raw in IH.
    all: destruct (Target.raw_to_comb e seed s) as [[[[[[]]]]]].
    all: constructor; [exact (Forall_inv IH)|exact (Forall_inv_tail IH)].
  - cbn in Hwd; rewrite Target.var_of_raw_exp_aux_eq in Hwd.
    unfold translate_raw in IH1, IH2.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) ("b1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("b1_" ++ s)) as [[[[[[] seed2]]]]].
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h))) ("b2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("b2_" ++ s)) as [[[[[[] seed']]]]].
    constructor; [|apply Forall_app; split; [refine (Forall_impl _ _ (Forall_inv_tail IH1))|refine (Forall_impl _ _ (Forall_inv_tail IH2))]].
    2,3: clear; intros ? Hincl ? Hin.
    2,3: specialize (Hincl _ Hin); cbn; rewrite !in_app_iff in *; tauto.
    cbn; rewrite Target.var_of_exp_aux_eq.
    apply incl_app; [refine (incl_trans _ _ _ (Forall_inv IH1) _)|refine (incl_trans _ _ _ (Forall_inv IH2) _)]; cbn.
    all: apply incl_app_app; [apply incl_refl|].
    all: apply incl_app_app; [apply incl_refl|].
    all: apply incl_app_app; [|apply incl_refl].
    all: intros ? h; apply in_or_app; tauto.
  - cbn in Hwd; rewrite 2!Target.var_of_raw_exp_aux_eq in Hwd.
    unfold translate_raw in IH1, IH2, IH3.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) ("c1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("c1_" ++ s)) as [[[[[[] seed2]]]]].
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl h))))) ("c2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("c2_" ++ s)) as [[[[[[] seed3]]]]].
    specialize (IH3 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror h))))) ("c3_" ++ s)%string seed3).
    destruct (Target.raw_to_comb e3 seed3 ("c3_" ++ s)) as [[[[[[] seed']]]]].
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
  - unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH Hwd ("val_" ++ s)%string seed); unfold translate_raw in IH.
    destruct (Target.raw_to_comb e seed ("val_" ++ s)) as [[[[[[]]]]]].
    remember ("pre_" ++ s)%string as s1 eqn:eqs1.
    remember ("eqn_" ++ s)%string as s2 eqn:eqs2.
    cbn.
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
      rewrite !in_app_iff in *; cbn; rewrite in_app_iff; tauto.
  - cbn in Hwd; rewrite Target.var_of_raw_exp_aux_eq in Hwd.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    unfold translate_raw in IH1, IH2.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) ("a1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("a1_" ++ s)) as [[[[[[] seed2]]]]].
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h))) ("a2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("a2_" ++ s)) as [[[[[[] seed']]]]].
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

Lemma translate_expr_pre_wd {ty} {e: Target.raw_exp ty} {n_in n_out n_locals} seed s:
  incl (Target.var_of_raw_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  Forall (fun eq => In {| binder_name := fst (snd eq); binder_id := snd (snd eq); binder_ty := binder_ty (fst eq) |} (n_in ++ n_out ++ pre_binders ++ n_locals)) pre_eqs.
Proof.
  intros _; revert s seed; induction e as [loc ty c|loc [ty b]|loc ty1 ty op e IH|loc ty1 ty2 ty op e1 IH1 e2 IH2|loc ty e1 IH1 e2 IH2 e3 IH3|loc ty e IH|loc ty e1 IH1 e2 IH2];
    intros s seed; try (constructor; [|constructor]).
  - apply Forall_nil.
  - apply Forall_nil.
  - cbn.
    specialize (IH s seed); unfold translate_raw in IH.
    destruct (Target.raw_to_comb e seed s) as [[[[[[]]]]]].
    exact IH.
  - unfold translate_raw in IH1, IH2.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH1 ("b1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("b1_" ++ s)) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 ("b2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("b2_" ++ s)) as [[[[[[] seed']]]]]; clear e2.
    apply Forall_app; split; [refine (Forall_impl _ _ IH1)|refine (Forall_impl _ _ IH2)].
    all: clear; intros ? Hin.
    all: rewrite !in_app_iff in *; tauto.
  - unfold translate_raw in IH1, IH2, IH3.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH1 ("c1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("c1_" ++ s)) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 ("c2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("c2_" ++ s)) as [[[[[[] seed3]]]]]; clear e2.
    specialize (IH3 ("c3_" ++ s)%string seed3).
    destruct (Target.raw_to_comb e3 seed3 ("c3_" ++ s)) as [[[[[[] seed']]]]]; clear e3.
    apply Forall_app; split; [|apply Forall_app; split].
    1: refine (Forall_impl _ _ IH1).
    2: refine (Forall_impl _ _ IH2).
    3: refine (Forall_impl _ _ IH3).
    all: clear; intros ? Hin.
    all: rewrite !in_app_iff in *; tauto.
  - unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH ("val_" ++ s)%string seed); unfold translate_raw in IH.
    destruct (Target.raw_to_comb e seed ("val_" ++ s)) as [[[[[[]]]]]].
    constructor; [|refine (Forall_impl _ _ IH)].
    2: clear; cbn; intros ? Hin; cbn; rewrite !in_app_iff in *; cbn; rewrite in_app_iff; tauto.
    apply in_or_app, or_intror, in_or_app, or_intror; left; exact eq_refl.
  - unfold translate_raw in IH1, IH2.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH1 ("a1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("a1_" ++ s)) as [[[[[[] seed2]]]]]; clear e1.
    specialize (IH2 ("a2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("a2_" ++ s)) as [[[[[[] seed']]]]]; clear e2.
    apply Forall_app; split; [refine (Forall_impl _ _ IH1)|refine (Forall_impl _ _ IH2)].
    all: clear; intros ? Hin.
    all: rewrite !in_app_iff in *; tauto.
Qed.

Lemma translate_expr_step_wd v {ty} {e: Target.raw_exp ty} {n_in n_out n_locals} seed s:
  incl (Target.var_of_raw_exp e) (n_in ++ n_out ++ n_locals) ->
  let '(ei, es, seed', pre_binders, pre_eqs, init_post, step_post) := translate_raw e seed s in
  Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) ((n_in ++ n_out ++ pre_binders ++ n_locals) ++ map fst pre_eqs))
    ((v, existT _ ty es) :: step_post).
Proof.
  intros Hwd; revert s seed; induction e as [loc ty c|loc [ty b]|loc ty1 ty op e IH|loc ty1 ty2 ty op e1 IH1 e2 IH2|loc ty e1 IH1 e2 IH2 e3 IH3|loc ty e IH|loc ty e1 IH1 e2 IH2];
    intros s seed; try (constructor; [|constructor]).
  - intros ? [].
  - rewrite app_nil_r; exact Hwd.
  - cbn.
    specialize (IH Hwd s seed); unfold translate_raw in IH.
    destruct (Target.raw_to_comb e seed s) as [[[[[[]]]]]].
    constructor; [exact (Forall_inv IH)|exact (Forall_inv_tail IH)].
  - cbn in Hwd; rewrite Target.var_of_raw_exp_aux_eq in Hwd.
    unfold translate_raw in IH1, IH2.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) ("b1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("b1_" ++ s)) as [[[[[[] seed2]]]]].
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h))) ("b2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("b2_" ++ s)) as [[[[[[] seed']]]]].
    constructor; [|apply Forall_app; split; [refine (Forall_impl _ _ (Forall_inv_tail IH1))|refine (Forall_impl _ _ (Forall_inv_tail IH2))]].
    2,3: clear; intros ? Hincl ? Hin.
    2,3: specialize (Hincl _ Hin); cbn; rewrite map_app, !in_app_iff in *; tauto.
    cbn; rewrite Target.var_of_exp_aux_eq.
    apply incl_app; [refine (incl_trans _ _ _ (Forall_inv IH1) _)|refine (incl_trans _ _ _ (Forall_inv IH2) _)]; cbn.
    all: apply incl_app_app; [|intros ? h; rewrite map_app; apply in_or_app; tauto].
    all: do 2 (apply incl_app_app; [apply incl_refl|]).
    all: apply incl_app_app; [|apply incl_refl].
    all: intros ? h; apply in_or_app; tauto.
  - cbn in Hwd; rewrite 2!Target.var_of_raw_exp_aux_eq in Hwd.
    unfold translate_raw in IH1, IH2, IH3.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) ("c1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("c1_" ++ s)) as [[[[[[] seed2]]]]].
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl h))))) ("c2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("c2_" ++ s)) as [[[[[[] seed3]]]]].
    specialize (IH3 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror h))))) ("c3_" ++ s)%string seed3).
    destruct (Target.raw_to_comb e3 seed3 ("c3_" ++ s)) as [[[[[[] seed']]]]].
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
  - unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH Hwd ("val_" ++ s)%string seed); unfold translate_raw in IH.
    destruct (Target.raw_to_comb e seed ("val_" ++ s)) as [[[[[[]]]]]].
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
    unfold translate_raw in IH1, IH2.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb.
    specialize (IH1 (fun _ h => Hwd _ (in_or_app _ _ _ (or_introl h))) ("a1_" ++ s)%string seed).
    destruct (Target.raw_to_comb e1 seed ("a1_" ++ s)) as [[[[[[] seed2]]]]].
    specialize (IH2 (fun _ h => Hwd _ (in_or_app _ _ _ (or_intror h))) ("a2_" ++ s)%string seed2).
    destruct (Target.raw_to_comb e2 seed2 ("a2_" ++ s)) as [[[[[[] seed']]]]].
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

Fixpoint translate_equations (eqs: list Target.raw_equation) (seed: seed_ty): (
    list Target.equation (* init *)
    * list Target.equation (* step *)
    * ident (* New identifier origin *)
    * list binder (* Variables created for pre *)
    * list (binder * (string * ident))(* pre equations *)
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
          let '(ei, es, seed2, pre_binders1, pre_eqs1, init_post1, step_post1) := translate_raw e seed1 (fst (fst eq)) in
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

Lemma translate_equations_nextseed (eqs: list Target.raw_equation) (seed: seed_ty):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  exists aux, seed' = fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed.
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    exists [].
    reflexivity.
  - simpl in translation.
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    specialize (translate_raw_nextseed expr seed0 (fst ident)) as unfoldseed.
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    destruct unfoldseed as [nexpr seedexpr].
    destruct IH as [nIH IH].
    rewrite IH in seedexpr.
    rewrite <- fold_left_app in seedexpr.
    exists (nIH ++ nexpr).
    assumption.
Qed.

Lemma freshness_translate_equations (eqs: list Target.raw_equation) (seed: seed_ty):
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
    assert (freshness_expr := freshness_translate_raw expr seed0 (fst ident)).
    assert (nextseed_expr := translate_raw_nextseed expr seed0 (fst ident)).
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    apply (freshness_later_e nextseed_expr) in IH.
    refine (freshness_permutation (freshness_fusion freshness_expr IH) _).
    rewrite map_app, !app_assoc; apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head, Permutation_app_comm.
Qed.

Lemma isnext_translate_equations (eqs: list Target.raw_equation) (seed: seed_ty):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  forall x, In x (pre_binders ++ map fst pre_eqs) ->
  exists aux vn vt, x = snd (next_ident (fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed) vn vt).
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
    assert (isnext_expr := isnext_translate_expr expr seed0 (fst ident)).
    cbn in translation.
    destruct (translate_raw expr seed0 (fst ident)) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
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
    all: rewrite <- fold_left_app in isnext_expr.
    all: exists (nseed ++ n).
    all: assumption.
Qed.

Lemma nodup_translate_equations (eqs: list Target.raw_equation) (seed: seed_ty):
  let '(init_eqs, step_eqs, seed', pre_binders, pre_eqs, init_post, step_post) := translate_equations eqs seed in
  NoDup (map binder_id pre_binders ++ map (fun eq => binder_id (fst eq)) pre_eqs).
Proof.
  destruct (translate_equations eqs seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post] eqn: translation.
  induction eqs as [| eq eqs IH] in seed, seed', pre_binders, init_eqs, step_eqs, pre_eqs, init_post, step_post, translation |- *.
  - injection translation as <- <- <- <- <- <- <-.
    apply NoDup_nil.
  - simpl in translation.
    assert (freshness_trans := freshness_translate_equations eqs seed).
    destruct (translate_equations eqs seed) as [[[[[[init_eqs0 step_eqs0] seed0] binders0] pre_eqs0] init_post0] step_post0] eqn: unfoldtrans.
    destruct eq as [ident [ty expr]].
    assert (nodup_expr := nodup_translate_expr expr seed0 (fst ident)).
    assert (isnext := isnext_translate_expr expr seed0 (fst ident)).
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    cbn in *; rewrite !map_app.
    refine (Permutation_NoDup _ (NoDup_app nodup_expr IH _)).
    1: rewrite !app_assoc; apply Permutation_app_tail; rewrite <-!app_assoc; apply Permutation_app_head, Permutation_app_comm.
    intros x isin2 isin0.
    rewrite <-(map_map fst binder_id), <-map_app in isin0, isin2; apply in_map_inv in isin2.
    destruct isin2 as [y [isin2 <-]].
    specialize (isnext y isin2).
    destruct isnext as (n & vn & vt & ->).
    specialize (freshness_trans n vn vt).
    cbn in freshness_trans, isin0.
    contradiction.
Qed.

Lemma translate_equations_assigned_init (eqs: list Target.raw_equation) (seed: seed_ty):
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
    assert (perm_expr := translate_expr_assigned_init expr seed0 (fst ident)).
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_app, IH, perm_expr; apply Permutation_refl.
Qed.

Lemma translate_equations_assigned_step (eqs: list Target.raw_equation) (seed: seed_ty):
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
    assert (perm_expr := translate_expr_assigned_step expr seed0 (fst ident)).
    destruct (translate_raw expr seed0) as [[[[[[ei2 es2] seed2] binders2] pre_eqs2] init_post2] step_post2].
    injection translation as <- <- <- <- <- <- <-.
    specialize (IH _ _ _ _ _ _ _ _ unfoldtrans).
    rewrite !map_app, IH, perm_expr; apply Permutation_refl.
Qed.

Lemma translate_equations_conservation_init (eqs: list Target.raw_equation) (seed: seed_ty):
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

Lemma translate_equations_conservation_step (eqs: list Target.raw_equation) (seed: seed_ty):
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

Lemma translate_init_assigned {n_body n_out n_locals} (n_seed: seed_ty)
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

Lemma translate_step_assigned {n_body n_out n_locals} (n_seed: seed_ty)
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
  (n_vars_unique : NoDup (map binder_id (n_in ++ n_out ++ n_locals)))
  (n_seed_always_fresh : freshness n_seed (n_in ++ n_out ++ n_locals)) :
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  NoDup (map binder_id (n_in ++ n_out ++ pre_binders ++ n_locals) ++ map (fun eq => binder_id (fst eq)) pre_eqs).
Proof.
  assert (nodup_translate := nodup_translate_equations n_body n_seed).
  assert (isnext := isnext_translate_equations n_body n_seed).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed'] pre_binders] pre_eqs] init_post] step_post].
  rewrite <-(map_map fst binder_id), <-map_app.
  rewrite !map_app.
  rewrite !map_app in n_vars_unique.
  unfold freshness in n_seed_always_fresh.
  rewrite !map_app in n_seed_always_fresh.
  rewrite app_assoc.
  rewrite Permutation_app_comm.
  rewrite (Permutation_app_comm (map binder_id pre_binders)).
  rewrite <- app_assoc.
  rewrite Permutation_app_comm.
  rewrite 2!app_assoc, <-app_assoc, <-(app_assoc (map _ _)), map_map.
  apply NoDup_app.
  1, 2: assumption.
  intros x f isin; revert f.
  rewrite <-(map_map fst binder_id), <-map_app in isin; apply in_map_inv in isin.
  destruct isin as [y [isin <-]].
  specialize (isnext y isin).
  destruct isnext as (n & vn & vt & ->).
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
  intros n vn vt isin.
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
  specialize (fresh_translate n vn vt).
  destruct isin as [isin | isin].
  1: contradiction.
  rewrite nextseed in isin.
  rewrite <- fold_left_app in isin.
  specialize (n_seed_always_fresh (nseed ++ n) vn vt).
  contradiction.
Qed.

Lemma translation_conservation n_seed n_body eq:
  In eq n_body ->
  let '(init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs) := translate_equations n_body n_seed in
  let '(ident, existT _ ty e) := eq in
  exists seed1,
  let '(ei, es, seed2, pre_binders1, pre_eqs1, init_post1, step_post1) := translate_raw e seed1 (fst (fst eq)) in
    In (ident, existT _ ty ei) init_eqs /\
    In (ident, existT _ ty es) step_eqs /\
    incl pre_binders1 pre_binders /\ incl pre_eqs1 pre_eqs /\ incl init_post1 init_post_eqs /\ incl step_post1 step_post_eqs.
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
    split; [|split; [|split; [|split; [|split]]]].
    1-2: constructor 1.
    1-2: exact eq_refl.
    1: exact (incl_appl _ (incl_refl _)).
    1: exact (incl_appl _ (incl_refl _)).
    1: exact (incl_appl _ (incl_refl _)).
    1: exact (incl_appl _ (incl_refl _)).
  - destruct eq' as [ident' [ty' e']].
    specialize (IH isin).
    destruct IH as [seed1 IH].
    destruct (translate_raw e' seed') as [[[[[[]]]]]].
    exists seed1.
    destruct (translate_raw e seed1) as [[[[[[]]]]]].
    destruct IH as (IH1 & IH2 & IH3 & IH4 & IH5 & IH6).
    split; [|split; [|split; [|split; [|split]]]].
    1-2: constructor 2; assumption.
    1: exact (incl_appr _ IH3).
    1: exact (incl_appr _ IH4).
    1: exact (incl_appr _ IH5).
    1: exact (incl_appr _ IH6).
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
  assert (Hexpr := translate_expr_init_wd eqid seed1 (fst eqid) (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_raw.
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
  Forall (fun eq => In {| binder_name := fst (snd eq); binder_id := snd (snd eq); binder_ty := binder_ty (fst eq) |} (n_in ++ n_out ++ pre_binders ++ n_locals)) pre_eqs.
Proof.
  intros n_all_vars_exist.
  induction n_body as [|[eqid [eqty eqeq]] n_body IH].
  1: apply Forall_nil.
  simpl.
  specialize (IH (Forall_inv_tail n_all_vars_exist)).
  destruct (translate_equations n_body n_seed) as [[[[[[init_eqs step_eqs] seed1] pre_binders] pre_eqs] init_post] step_post].
  assert (Hexpr := translate_expr_pre_wd seed1 (fst eqid) (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_raw.
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
  assert (Hexpr := translate_expr_step_wd eqid seed1 (fst eqid) (Forall_inv n_all_vars_exist)); cbn in Hexpr; unfold translate_raw.
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

  destruct (Target.timed_list_eq new_body) as [timed_body | err].
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
    + apply sig2T_eq_type in H3, H4; subst.
      constructor.
      specialize (IH _ _ H2).
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
    all: apply sig2T_eq_type in H3, H4, H5; subst.
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
  destruct (Target.timed_list_eq (eqs_to_raw n0_body)) as [timed_body | err].
  2: inversion translated.
  apply Result.ok_eq in translated.
  rewrite <- translated.
  clear translated.
  unfold Source.sem_node, Source.n_vars, Source.n_in, Source.n_out, Source.n_locals, Source.n_body, Target.sem_raw_node, Target.rn_vars, Target.rn_in, Target.rn_out, Target.rn_locals, Target.rn_body.

  intro sem_source.
  intros b is_var.
  specialize (sem_source b is_var).
  destruct sem_source as [s [mapped sem_source]].
  exists s.
  split.
  1: exact mapped.
  intros raw_e is_eq t.

  assert (in_body := equation_conservation_inv (binder_name b, binder_id b) raw_e n0_body is_eq).
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
  destruct (Target.timed_list_eq (eqs_to_raw n0_body)) as [timed_body | err].
  2: inversion translated.
  apply Result.ok_eq in translated.
  rewrite <- translated.
  clear translated.
  unfold Source.sem_node, Source.n_vars, Source.n_in, Source.n_out, Source.n_locals, Source.n_body, Target.sem_raw_node, Target.rn_vars, Target.rn_in, Target.rn_out, Target.rn_locals, Target.rn_body.

  intro sem_target.
  intros b is_var.
  specialize (sem_target b is_var).
  destruct sem_target as [s [mapped sem_target]].
  exists s.
  split.
  1: exact mapped.
  intros e is_eq t.

  assert (in_body := equation_conservation (binder_name b, binder_id b) e n0_body is_eq).
  specialize (sem_target (expr_to_raw e) in_body t).
  apply raw_expr_correct.
  assumption.
Qed.

Theorem next_translation_correct (n: Target.node) (n0: Target.raw_node) (h: history):
  translate_raw_to_node n0 = n ->
  Target.sem_node n h ->
  Target.sem_raw_node n0 h.
Proof.
  intros translated.
  unfold translate_raw_to_node in translated.
  destruct n0 as [n0_loc n0_name n0_in n0_out n0_locals n0_body n0_vars n0_assigned_vars n0_all_vars_exist n0_vars_all_assigned n0_vars_unique n0_seed n0_seed_always_fresh n0_well_timed].
  remember (translate_init_assigned n0_seed n0_vars_all_assigned) as init_assigned eqn: tmp; clear tmp.
  remember (translate_step_assigned n0_seed n0_vars_all_assigned) as step_assigned eqn: tmp; clear tmp.
  remember (translate_vars_unique n0_body n0_vars_unique n0_seed_always_fresh) as vars_unique eqn: tmp; clear tmp.
  remember (translate_seed_always_fresh n0_body n0_seed_always_fresh) as seed_fresh eqn: tmp; clear tmp.
  remember (translate_init_wd n0_seed n0_all_vars_exist) as init_wd eqn: tmp; clear tmp.
  remember (translate_pre_wd n0_seed n0_all_vars_exist) as pre_wd eqn: tmp; clear tmp.
  remember (translate_step_wd n0_seed n0_all_vars_exist) as step_wd eqn: tmp; clear tmp.
  assert (Hcons := translation_conservation n0_seed n0_body).
  destruct (translate_equations n0_body n0_seed) as [[[[[[trans_init trans_step] trans_seed] trans_pre_binders] trans_pre_eqs] trans_init_eqs] trans_step_eqs] eqn: translation.
  subst.
  unfold Target.sem_raw_node, Target.sem_node; cbn.
  intros Htrans b Hity.
  rewrite app_assoc in Hity.
  assert (tmp := fun H1 H2 => proj1 (Htrans b) match in_app_or _ _ _ Hity with or_introl h => H1 h | or_intror h => H2 h end).
  rewrite app_assoc in tmp.
  specialize (tmp (fun h => in_or_app _ _ _ (or_introl h))).
  rewrite app_assoc, <-(app_assoc n0_in) in tmp.
  specialize (tmp (fun h => in_or_app _ _ _ (or_intror h))).
  destruct tmp as [s [Hs [H1 H2]]]; exists s; split; [exact Hs|].
  intros e He.
  specialize (Hcons _ He) as [seed1 Hcons].
  destruct (translate_raw e seed1) as [[[[[[ei es] seede] lb] lbi] le1] le2] eqn:eqtrans.
  destruct Hcons as [Hei [Hes Hcons]].
  specialize (H1 _ (in_or_app _ _ _ (or_introl Hei))); clear Hei.
  specialize (H2 _ (in_or_app _ _ _ (or_introl Hes))); clear Hes.
  assert (Hpreeqs := fun b => proj2 (Htrans b)).
  assert (Hprebs := fun b H => proj1 (Htrans b) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl H))))))).
  intros n.
  assert (Hwt := proj1 (Forall_forall _ _) n0_well_timed _ He n).
  revert n Hwt.
  clear - H1 H2 eqtrans Hpreeqs Hprebs Hcons.
  intros n; remember (Stream.nth n s) as v eqn:eqv.
  assert (H1' : n = O -> Target.sem_comb_exp h O ei v)
    by (intros ->; subst v; exact H1).
  assert (H2' : match n with O => True | S _ => Target.sem_comb_exp h n es v end)
    by (destruct n; [exact I|subst v; exact (H2 _)]).
  clear eqv s H1 H2.
  cbn in eqtrans |- *.
  destruct b as [s tmp1 ty]; cbn in *; clear tmp1.
  revert s seed1 v ei es seede lb lbi le1 le2 eqtrans n H1' H2' Hcons;
    induction e as [l ty c|l b|l tin tout op e IH|l ty1 ty2 tout op e1 IH1 e2 IH2|l ty e1 IH1 e2 IH2 e3 IH3|l ty e IH|l ty e1 IH1 e2 IH2];
    intros s seed1 v ei es seede lb lbi le1 le2.
  - intros [=<- <- <- <- <- <- <-] [|n] H1 H2 Hcons Hwt.
    1: specialize (H1 eq_refl); clear - H1.
    1: inversion H1; simpl_exist_type; subst; constructor.
    clear - H2.
    inversion H2; simpl_exist_type; subst; constructor.
  - intros [=<- <- <- <- <- <- <-] [|n] H1 H2 Hcons Hwt.
    1: specialize (H1 eq_refl); clear - H1.
    1: inversion H1; simpl_exist_type; subst.
    1: refine (Target.Raw_SeVar _ _ _ _ _ _); assumption.
    clear - H2.
    inversion H2; simpl_exist_type; subst.
    refine (Target.Raw_SeVar _ _ _ _ _ _); assumption.
  - cbn; unfold translate_raw in IH.
    specialize (IH s seed1).
    destruct (Target.raw_to_comb e seed1 s) as [[[[[[ei' es'] seed'] lb'] lbi'] lbe1'] lbe2'].
    intros [=<- <- <- <- <- <- <-] n H1 H2 Hcons Hwt.
    specialize (fun v h1 h2 h3 => IH v _ _ _ _ _ _ _ eq_refl n h1 h2 h3 ltac:(inversion Hwt; simpl_exist_type; subst; assumption)).
    destruct n as [|n].
    1: specialize (H1 eq_refl); clear - IH H1 Hcons.
    1: inversion H1; simpl_exist_type; subst.
    1: refine (Target.Raw_SeUnop _ _ _ _ _ _ _ _ _); [refine (IH _ (fun _ => _) I _)|eassumption]; assumption.
    clear - IH H2 Hcons.
    inversion H2; simpl_exist_type; subst.
    refine (Target.Raw_SeUnop _ _ _ _ _ _ _ _ _); [refine (IH _ ltac:(discriminate 1) _ _)|eassumption]; assumption.
  - unfold translate_raw in IH1, IH2.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb; simpl fst.
    specialize (IH1 ("b1_" ++ s)%string seed1).
    destruct (Target.raw_to_comb e1 seed1 ("b1_" ++ s)) as [[[[[[ei1' es1'] seed1'] lb1'] lbi1'] lbe11'] lbe21'].
    specialize (IH2 ("b2_" ++ s)%string seed1').
    destruct (Target.raw_to_comb e2 seed1' ("b2_" ++ s)) as [[[[[[ei2' es2'] seed2'] lb2'] lbi2'] lbe12'] lbe22'].
    intros [=<- <- <- <- <- <- <-] n H1 H2 Hcons Hwt.
    specialize (fun v h1 h2 h3 => IH1 v _ _ _ _ _ _ _ eq_refl n h1 h2 h3 ltac:(inversion Hwt; simpl_exist_type; subst; assumption)).
    specialize (fun v h1 h2 h3 => IH2 v _ _ _ _ _ _ _ eq_refl n h1 h2 h3 ltac:(inversion Hwt; simpl_exist_type; subst; assumption)).
    destruct n as [|n].
    1: specialize (H1 eq_refl); clear - IH1 IH2 H1 Hcons.
    1: inversion H1; simpl_exist_type; subst; simpl_exist_type; subst.
    1: destruct Hcons as (h1 & h2 & h3 & h4); apply incl_app_inv in h1, h2, h3, h4;
         assert (Hcons1 := conj (proj1 h1) (conj (proj1 h2) (conj (proj1 h3) (proj1 h4))));
         assert (Hcons2 := conj (proj2 h1) (conj (proj2 h2) (conj (proj2 h3) (proj2 h4)))).
    1: refine (Target.Raw_SeBinop _ _ _ _ _ _ _ _ _ _ _ _); [refine (IH1 _ (fun _ => _) I _)|refine (IH2 _ (fun _ => _) I _)|eassumption]; assumption.
    clear - IH1 IH2 H2 Hcons.
    inversion H2; simpl_exist_type; subst; simpl_exist_type; subst.
    destruct Hcons as (h1 & h2 & h3 & h4); apply incl_app_inv in h1, h2, h3, h4;
      assert (Hcons1 := conj (proj1 h1) (conj (proj1 h2) (conj (proj1 h3) (proj1 h4))));
      assert (Hcons2 := conj (proj2 h1) (conj (proj2 h2) (conj (proj2 h3) (proj2 h4)))).
    refine (Target.Raw_SeBinop _ _ _ _ _ _ _ _ _ _ _ _); [refine (IH1 _ ltac:(discriminate 1) _ _)|refine (IH2 _ ltac:(discriminate 1) _ _)|eassumption]; assumption.
  - unfold translate_raw in IH1, IH2, IH3.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb; simpl fst.
    specialize (IH1 ("c1_" ++ s)%string seed1).
    destruct (Target.raw_to_comb e1 seed1 ("c1_" ++ s)) as [[[[[[ei1' es1'] seed1'] lb1'] lbi1'] lbe11'] lbe21'].
    specialize (IH2 ("c2_" ++ s)%string seed1').
    destruct (Target.raw_to_comb e2 seed1' ("c2_" ++ s)) as [[[[[[ei2' es2'] seed2'] lb2'] lbi2'] lbe12'] lbe22'].
    specialize (IH3 ("c3_" ++ s)%string seed2').
    destruct (Target.raw_to_comb e3 seed2' ("c3_" ++ s)) as [[[[[[ei3' es3'] seed3'] lb3'] lbi3'] lbe13'] lbe23'].
    intros [=<- <- <- <- <- <- <-] n H1 H2 Hcons Hwt.
    specialize (fun v h1 h2 h3 => IH1 v _ _ _ _ _ _ _ eq_refl n h1 h2 h3 ltac:(inversion Hwt; simpl_exist_type; subst; assumption)).
    specialize (fun v h1 h2 h3 => IH2 v _ _ _ _ _ _ _ eq_refl n h1 h2 h3 ltac:(inversion Hwt; simpl_exist_type; subst; assumption)).
    specialize (fun v h1 h2 h3 => IH3 v _ _ _ _ _ _ _ eq_refl n h1 h2 h3 ltac:(inversion Hwt; simpl_exist_type; subst; assumption)).
    destruct n as [|n].
    1: specialize (H1 eq_refl); clear - IH1 IH2 IH3 H1 Hcons.
    1: inversion H1; simpl_exist_type; subst; simpl_exist_type; subst.
    1: destruct Hcons as (h1 & h2 & h3 & h4); apply incl_app_inv in h1, h2, h3, h4;
         destruct h1 as [h11 h12], h2 as [h21 h22], h3 as [h31 h32], h4 as [h41 h42];
         apply incl_app_inv in h12, h22, h32, h42;
         assert (Hcons1 := conj h11 (conj h21 (conj h31 h41)));
         assert (Hcons2 := conj (proj1 h12) (conj (proj1 h22) (conj (proj1 h32) (proj1 h42))));
         assert (Hcons3 := conj (proj2 h12) (conj (proj2 h22) (conj (proj2 h32) (proj2 h42)))).
    1: refine (Target.Raw_SeIfte _ _ _ _ _ _ _ _ _ _ _ _); [refine (IH1 _ (fun _ => _) I _)|refine (IH2 _ (fun _ => _) I _)|refine (IH3 _ (fun _ => _) I _)]; assumption.
    clear - IH1 IH2 IH3 H2 Hcons.
    inversion H2; simpl_exist_type; subst; simpl_exist_type; subst.
    destruct Hcons as (h1 & h2 & h3 & h4); apply incl_app_inv in h1, h2, h3, h4;
      destruct h1 as [h11 h12], h2 as [h21 h22], h3 as [h31 h32], h4 as [h41 h42];
      apply incl_app_inv in h12, h22, h32, h42;
      assert (Hcons1 := conj h11 (conj h21 (conj h31 h41)));
      assert (Hcons2 := conj (proj1 h12) (conj (proj1 h22) (conj (proj1 h32) (proj1 h42))));
      assert (Hcons3 := conj (proj2 h12) (conj (proj2 h22) (conj (proj2 h32) (proj2 h42)))).
    refine (Target.Raw_SeIfte _ _ _ _ _ _ _ _ _ _ _ _); [refine (IH1 _ ltac:(discriminate 1) _ _)|refine (IH2 _ ltac:(discriminate 1) _ _)|refine (IH3 _ ltac:(discriminate 1) _ _)]; assumption.
  - unfold translate_raw in IH.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb; simpl fst.
    specialize (IH ("val_" ++ s)%string seed1).
    destruct (Target.raw_to_comb e seed1 ("val_" ++ s)) as [[[[[[ei1' es1'] seed1'] lb1'] lbi1'] lbe11'] lbe21'].
    remember (next_ident seed1' ("pre_" ++ s) ty) as tmp eqn:eqpre; destruct tmp as [seed2' ident_pre].
    remember (next_ident seed2' ("eqn_" ++ s) ty) as tmp eqn:eqeq; destruct tmp as [seed3' ident_eq].
    cbn.
    intros [=<- <- <- <- <- <- <-] n H1 H2 Hcons Hwt.
    destruct n as [|n].
    1: inversion Hwt.
    specialize (fun v h1 h2 h3 => IH v _ _ _ _ _ _ _ eq_refl n h1 h2 h3 ltac:(inversion Hwt; simpl_exist_type; subst; assumption)).
    constructor.
    destruct Hcons as (Hc1 & Hc2 & Hc3 & Hc4).
    assert (tmp := Hpreeqs _ _ (Hc2 _ (or_introl eq_refl))).
    destruct tmp as [s0 [Hs0h Hs0v]].
    specialize (Hs0v n l).
    assert (tmp := Hprebs _ (Hc1 _ (or_introl eq_refl))).
    destruct tmp as [s1 [Hs1h [Hs1vi Hs1vs]]].
    specialize (Hs1vi _ (in_or_app _ _ _ (or_intror (Hc3 _ (or_introl eq_refl))))).
    specialize (Hs1vs _ (in_or_app _ _ _ (or_intror (Hc4 _ (or_introl eq_refl))))).
    clear H1.
    unfold h_maps_to in Hs0h, Hs1h.
    assert (Hvs1 : v = Stream.nth n s1).
    1:{
      assert (Hs0s1 : Stream.nth n (Stream.tl s0) = Stream.nth n s1).
      1:{
        inversion Hs0v; simpl_exist_type; subst.
        cbn in H1.
        clear - H1 H5 Hs1h.
        unfold Dict.maps_to in Hs1h, H1; cbn in Hs1h; rewrite H1 in Hs1h.
        injection Hs1h as H0; simpl_exist_type; subst.
        exact (eq_sym H5).
      }
      rewrite <-Hs0s1.
      clear - H2 Hs0h.
      inversion H2; simpl_exist_type; subst.
      cbn in H1.
      unfold Dict.maps_to in Hs0h, H1; cbn in Hs0h; rewrite H1 in Hs0h.
      injection Hs0h as H0; simpl_exist_type; subst.
      exact eq_refl.
    }
    subst v.
    refine (IH _ _ _ _).
    1: intros ->; exact Hs1vi.
    1: destruct n; [exact I|exact (Hs1vs _)].
    split; [exact (fun _ h => Hc1 _ (or_intror h))|].
    split; [exact (fun _ h => Hc2 _ (or_intror h))|].
    split; [exact (fun _ h => Hc3 _ (or_intror h))|].
    exact (fun _ h => Hc4 _ (or_intror h)).
  - unfold translate_raw in IH1, IH2.
    unfold translate_raw, Target.raw_to_comb; fold @Target.raw_to_comb; simpl fst.
    specialize (IH1 ("a1_" ++ s)%string seed1).
    destruct (Target.raw_to_comb e1 seed1 ("a1_" ++ s)) as [[[[[[ei1' es1'] seed1'] lb1'] lbi1'] lbe11'] lbe21'].
    specialize (IH2 ("a2_" ++ s)%string seed1').
    destruct (Target.raw_to_comb e2 seed1' ("a2_" ++ s)) as [[[[[[ei2' es2'] seed2'] lb2'] lbi2'] lbe12'] lbe22'].
    intros [=<- <- <- <- <- <- <-] n H1 H2 Hcons Hwt.
    destruct Hcons as (h1 & h2 & h3 & h4); apply incl_app_inv in h1, h2, h3, h4;
      assert (Hcons1 := conj (proj1 h1) (conj (proj1 h2) (conj (proj1 h3) (proj1 h4))));
      assert (Hcons2 := conj (proj2 h1) (conj (proj2 h2) (conj (proj2 h3) (proj2 h4)))).
    inversion Hwt as [| | | | | |? ? ? ? Hwt1|? ? ? ? ? Hwt2]; simpl_exist_type; subst.
    + constructor; refine (IH1 _ _ _ _ _ _ _ _ eq_refl _ _ _ _ _); assumption.
    + constructor; refine (IH2 _ _ _ _ _ _ _ _ eq_refl (S _) ltac:(discriminate 1) _ _ _); assumption.
Qed.

Axiom next_translation_complete : forall (n: Target.node) (n0: Target.raw_node) (h: history),
  translate_raw_to_node n0 = n ->
  Target.sem_raw_node n0 h ->
  (forall aux vn vt, ~ Dict.is_in (binder_id (snd (next_ident (fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux n0.(Target.rn_seed)) vn vt))) h) ->
  exists h1, Dict.inclusion h h1 /\
  Target.sem_node n h1.
(* TODO *)

(* Semantics preservation *)
Lemma semantics_preservation (n: Target.node) (n0: Source.node) (h: history):
  translate_node n0 = Result.Ok n ->
  Source.sem_node n0 h ->
  (forall aux vn vt, ~ Dict.is_in (binder_id (snd (next_ident (fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux n0.(Source.n_seed)) vn vt))) h) ->
  exists h1, Dict.inclusion h h1 /\
  Target.sem_node n h1.
Proof using.
  intros H1 H2 H3.
  unfold translate_node in H1.
  destruct (translate_to_raw_node n0) as [n1|e] eqn:eqt1; [injection H1 as eqt2|discriminate H1].
  apply (raw_translation_complete _ _ _ eqt1) in H2.
  refine (next_translation_complete _ _ _ eqt2 H2 _).
  refine (eq_ind _ (fun s => forall aux vn vt,
    ~ Dict.is_in (binder_id (snd (next_ident (fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux s) vn vt))) h) H3 _ _).
  clear - eqt1; destruct n0, n1; cbn in *.
  destruct (Target.timed_list_eq (eqs_to_raw n_body)); [injection eqt1 as ?; assumption|discriminate eqt1].
Qed.

Lemma semantics_preservation_inv (n: Target.node) (n0: Source.node) (h: history):
  translate_node n0 = Result.Ok n -> Target.sem_node n h -> Source.sem_node n0 h.
Proof using.
  intros H1 H2.
  unfold translate_node in H1.
  destruct (translate_to_raw_node n0) as [n1|e] eqn:eqt1; [injection H1 as eqt2|discriminate H1].
  refine (raw_translation_correct _ _ _ eqt1 _).
  refine (next_translation_correct _ _ _ eqt2 _).
  exact H2.
Qed.

(* FIXME: add a well_timed semantic for Source.exp as well *)
Lemma translation_complete (n: Source.node) es:
  translate_node n = Result.Err es ->
  exists eqs, incl eqs n.(Source.n_body) /\
  Forall (fun eq => In eq eqs <-> exists n, ~ Target.well_timed n (expr_to_raw (projT2 (snd eq)))) n.(Source.n_body) /\
  exists aux,
  es = List.map (fun '(b, l) => (l, Result.InvalidTiming (binder_name b) (binder_id b) (binder_ty b)))
         (List.combine (List.map Source.equation_dest eqs) aux).
Proof using.
  unfold translate_node.
  intros H.
  destruct (translate_to_raw_node n) as [?|es'] eqn:H2; [discriminate H|injection H as ->].
  destruct n as [nl nn nin out loc eqs vars assvars ave vaa vun seed Hseed]; unfold Source.n_body.
  unfold translate_to_raw_node in H2.
  assert (tmp := Target.timed_list_eq_complete (eqs_to_raw eqs)).
  destruct (Target.timed_list_eq (eqs_to_raw eqs)) as [?|es'] eqn:H; [discriminate H2|injection H2 as ->].
  clear - tmp.
  specialize (tmp _ eq_refl) as (eqs0 & H1 & H2).
  assert (tmp : exists eqs1, incl eqs1 eqs /\ eqs0 = map (fun eq => (fst eq, existT Target.raw_exp (projT1 (snd eq)) (expr_to_raw (projT2 (snd eq))))) eqs1).
  1:{
    clear - H1.
    induction eqs0 as [|[i [ty e2]] eqs2 IH].
    1: exists []; exact (conj (fun _ => False_ind _) eq_refl).
    specialize (equation_conservation_inv _ _ _ (H1 _ (or_introl eq_refl))) as [e1 [He eqeq]].
    specialize (IH (fun _ h => H1 _ (or_intror h))) as [eqs1 [Heqs1 eqeqs]].
    exists ((i, existT Source.exp ty e1) :: eqs1).
    split; [intros ? [<-|h]; [exact He|exact (Heqs1 _ h)]|].
    exact (f_equal2 (fun e es => (_, existT _ _ e) :: es) eqeq eqeqs).
  }
  destruct tmp as [eqs1 [Hi ->]].
  exists eqs1; split; [exact Hi|].
  rewrite map_map in H2; refine (conj _ (proj2 H2)).
  apply proj1 in H2; clear - H2.
  unfold eqs_to_raw in H2; rewrite Forall_map in H2.
  refine (Forall_impl _ _ H2); clear.
  intros [i [ty e]] H; rewrite <-H; clear H.
  cbn.
  split; [exact (in_map _ _ _)|].
  intros H.
  apply in_map_iff in H; destruct H as [[i2 [ty2 e2]] [[=-> -> eq2] H]].
  simpl_exist_type; refine (eq_ind _ (fun e => In (_, existT _ _ e) _) H _ _); clear - eq2.
  revert e eq2; induction e2 as [l ty c|l [n i ty]|l tin tout [] e IH|l ty1 ty2 ty [] e1 IH1 e2 IH2|l ty ec IHc e1 IH1 e2 IH2];
    intros e' Heq; specialize (Source.exp_inv e') as [l' Heqe];
    destruct Heqe as [[[[(c' & ->)|([n' i' ty'] & tmp & ->)]
      |(tin' & op' & e1' & ->)]|(ty1' & ty2' & op' & e1' & e2' & ->)]|(ec' & e1' & e2' & ->)]; try discriminate Heq; cbn in *.
  2,8,11,14,17,20,23,26,29,32,35,38,41,44,47,50,53,56,59: cbn in tmp; subst ty'; discriminate Heq.
  4: cbn in tmp; subst ty'; cbn in *.
  1: injection Heq as <- eqc; simpl_exist_type; subst; exact eq_refl.
  1,2,4,5: cbn in op'; destruct op'; discriminate Heq.
  1: injection Heq as <- <- eqi; exact (f_equal (fun i => Source.EVar _ {| binder_name := _; binder_id := i; binder_ty := _ |} : Source.exp ty) eqi).
  2,4,6: specialize (Source.binop_inv op') as tmp;
     repeat match type of tmp with _ + { _ } => destruct tmp as [tmp|tmp] | { _ } + { _ } => destruct tmp as [tmp|tmp] end;
     repeat match type of tmp with ex _ => destruct tmp as [? tmp] end; subst; try discriminate;
     repeat match goal with h : TInt = TInt |- _ => assert (tmp := Eqdep_dec.UIP_dec type_dec h eq_refl); subst end; discriminate.
  1,2,3: specialize (Source.unop_inv op') as [[(-> & h & ->)|(-> & h & ->)]|(-> & ->)];
         try assert (tmp := Eqdep_dec.UIP_dec type_dec h eq_refl); subst; try discriminate Heq; cbn in *;
         injection Heq as <- H; simpl_exist_type; apply IH in H; congruence.
  1,3,5,7,9,11,13,15,17,19,21,23,25,27,29:
    specialize (Source.unop_inv op') as [[(-> & h & ->)|(-> & h & ->)]|(-> & ->)];
    try assert (tmp := Eqdep_dec.UIP_dec type_dec h eq_refl); subst; discriminate.
  1-15: specialize (Source.binop_inv op') as tmp;
     repeat match type of tmp with _ + { _ } => destruct tmp as [tmp|tmp] | { _ } + { _ } => destruct tmp as [tmp|tmp] end;
     repeat match type of tmp with ex _ => destruct tmp as [? tmp] end; subst; try discriminate;
     repeat match goal with
     | h : TInt = TInt |- _ => assert (tmp := Eqdep_dec.UIP_dec type_dec h eq_refl); subst
     | h : TBool = TBool |- _ => assert (tmp := Eqdep_dec.UIP_dec type_dec h eq_refl); subst
     end;
     try discriminate;
     injection Heq as <- H1 H2; simpl_exist_type; apply IH1 in H1; apply IH2 in H2; cbn; congruence.
  injection Heq as <- Hc H1 H2; simpl_exist_type; apply IHc in Hc; apply IH1 in H1; apply IH2 in H2; cbn; congruence.
Qed.
