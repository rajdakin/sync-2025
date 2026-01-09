Set Default Goal Selector "!".

From Stdlib Require Import Lia.

Definition ident := nat.

Definition next_ident: ident -> ident := S.

Lemma ident_diff (seed: ident):
  forall n, seed <> Nat.iter (S n) next_ident seed.
Proof.
  assert (s: forall n, seed < Nat.iter (S n) next_ident seed).
  - intro n.
    induction n.
    + unfold next_ident.
      simpl.
      lia.
    + simpl in IHn.
      simpl.
      unfold next_ident at 1 2.
      unfold next_ident at 1 in IHn.
      lia.
  - intro n.
    specialize (s n).
    lia.
Qed.

Definition ident_dec (x y: ident) : {x = y} + {x <> y} := (PeanoNat.Nat.eq_dec x y).
