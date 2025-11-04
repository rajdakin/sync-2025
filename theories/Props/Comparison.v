Set Default Goal Selector "!".

From Stdlib Require Import Nat Lia.

Lemma lt_n_S_stt (n m: nat):
  n < m -> S n < S m.
Proof. lia. Qed.

Lemma refl (n: nat):
  n ?= n = Eq.
Proof.
  now induction n.
Qed.

Lemma eq_is_eq (m n: nat):
  m ?= n = Eq <-> m = n.
Proof.
  split.

  - revert n.
    induction m; intros n H.
    + destruct n; [ reflexivity |].
      discriminate.

    + destruct n; [ discriminate |].
      f_equal.
      now apply IHm.

  - intros <-.
    apply refl.
Qed.

Lemma lt_refl (m: nat):
  m ?= (S m) = Lt.
Proof.
  now induction m.
Qed.

Lemma lt_S (m n: nat):
  m ?= n = Lt ->
  m ?= (S n) = Lt.
Proof.
  revert n.
  induction m; intros n H.
  { reflexivity. }

  destruct n.
  + inversion H.
  + now apply IHm.
Qed.

Lemma lt_is_lt (m n: nat):
  m ?= n = Lt <-> lt m n.
Proof.
  split.

  - revert n.
    induction m; intros n H.
    + destruct n; [ discriminate |].
      lia.

    + destruct n; [ discriminate |].
      apply lt_n_S_stt.
      now apply IHm.

  - induction 1.
    + apply lt_refl.
    + now apply lt_S.
Qed.

Lemma gt_refl (m: nat):
  (S m) ?= m = Gt.
Proof.
  now induction m.
Qed.

Lemma gt_S (m n: nat):
  m ?= n = Gt ->
  (S m) ?= n = Gt.
Proof.
  revert m.
  induction n; intros m H.
  { reflexivity. }

  destruct m.
  + inversion H.
  + now apply IHn.
Qed.

Lemma gt_is_gt (m n: nat):
  m ?= n = Gt <-> lt n m.
Proof.
  split.

  - revert n.
    induction m; intros n H.
    + destruct n; [| discriminate ].
      rewrite refl in H.
      discriminate.

    + destruct n; [ lia |].
      apply lt_n_S_stt.
      now apply IHm.

  - induction 1.
    + apply gt_refl.
    + now apply gt_S.
Qed.
