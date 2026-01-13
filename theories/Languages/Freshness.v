Set Default Goal Selector "!".

From Stdlib.Arith Require Import PeanoNat.
From Stdlib Require Import String List Permutation.
From Reactive.Props Require Import Identifier.
From Reactive.Languages Require Import Semantics.

Definition seed_ty := ident.
Definition next_ident (s: seed_ty) (vname: string) (vtype: type): (seed_ty * binder)%type :=
  (S s, {| binder_name := vname; binder_id := s; binder_ty := vtype |}).

Lemma iter_next_ident_seed (seed: seed_ty) aux:
  fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed = seed + length aux.
Proof using.
  cbn.
  induction aux as [|[? ?] tl IH] in seed |- *.
  1: exact (eq_sym (Nat.add_0_r _)).
  cbn; rewrite Nat.add_succ_r; exact (IH _).
Qed.

Lemma ident_diff (seed: seed_ty):
  forall aux, aux <> nil -> seed <> fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed.
Proof.
  intros [|[vn vt] aux] Haux; [contradiction (Haux eq_refl)|clear Haux; cbn].
  rewrite iter_next_ident_seed.
  apply Nat.lt_neq, le_n_S; clear vn vt.
  exact (Nat.le_add_r _ _).
Qed.

Definition freshness (seed: seed_ty) (vars: list binder) :=
  forall aux vn vt, ~ In (binder_id (snd (next_ident (fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed) vn vt))) (map binder_id vars).

Definition freshness' (seed: seed_ty) (vars: list binder) :=
  forall n vn vt, ~ In (binder_id (snd (next_ident (seed + n) vn vt))) (map binder_id vars).

Lemma freshness_freshness' seed vars: freshness seed vars <-> freshness' seed vars.
Proof using.
  unfold freshness, freshness'; split; intros H aux vn vt f.
  1: refine (H (repeat (vn, vt) aux) vn vt _); rewrite iter_next_ident_seed; rewrite repeat_length; exact f.
  rewrite iter_next_ident_seed in f; exact (H _ _ _ f).
Qed.

Lemma freshness_permutation {seed} {vars1 vars2: list binder}:
  freshness seed vars1 -> Permutation vars1 vars2 -> freshness seed vars2.
Proof using.
  rewrite !freshness_freshness'.
  intros Hfresh Hperm n vn vt Hin.
  specialize (Hfresh n vn vt).
  rewrite Hperm in Hfresh.
  exact (Hfresh Hin).
Qed.

Lemma freshness_fusion {seed: seed_ty} {vars1 vars2: list binder}:
  freshness seed vars1 -> freshness seed vars2 -> freshness seed (vars1 ++ vars2).
Proof.
  rewrite !freshness_freshness'.
  intros fresh1 fresh2 n vn vt.
  specialize (fresh1 n vn vt).
  specialize (fresh2 n vn vt).
  rewrite map_app; intro isin.
  apply in_app_or in isin.
  tauto.
Qed.

Lemma freshness_later {seed1 seed2: seed_ty} {aux} {vars: list binder}:
  seed2 = fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed1 -> freshness seed1 vars -> freshness seed2 vars.
Proof.
  rewrite !freshness_freshness', iter_next_ident_seed.
  intros -> isiter m vn vt.
  specialize (isiter (length aux + m)).
  cbn in *.
  rewrite <-Nat.add_assoc.
  exact (isiter vn vt).
Qed.

Lemma freshness_later_e {seed1 seed2: ident} {vars: list binder}:
  (exists aux, seed2 = fold_left (fun s '(vn, vt) => fst (next_ident s vn vt)) aux seed1) -> freshness seed1 vars -> freshness seed2 vars.
Proof.
  intros [n isiter].
  apply (freshness_later isiter).
Qed.

Opaque next_ident.
