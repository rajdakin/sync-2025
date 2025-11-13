Set Default Goal Selector "!".

From Reactive.Props Require Import Identifier.
From Stdlib.Arith Require Import PeanoNat.
From Stdlib Require Import List.

Definition freshness {A} (seed: ident) (vars: list (ident * A)) := forall n, ~In (Nat.iter n next_ident seed) (map fst vars).

Lemma freshness_fusion {A} {seed: ident} {vars1 vars2: list (ident * A)}:
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

Lemma freshness_later {A} {seed1 seed2: ident} {n: nat} {vars: list (ident * A)}:
  seed2 = Nat.iter n next_ident seed1 -> freshness seed1 vars -> freshness seed2 vars.
Proof.
  intros fresh1 isiter.
  intro m.
  specialize (isiter (m + n)).
  rewrite Nat.iter_add in isiter.
  rewrite <- fresh1 in isiter.
  assumption.
Qed.

Lemma freshness_later_e {A} {seed1 seed2: ident} {vars: list (ident * A)}:
  (exists n, seed2 = Nat.iter n next_ident seed1) -> freshness seed1 vars -> freshness seed2 vars.
Proof.
  intros [n isiter].
  apply (freshness_later isiter).
Qed.
