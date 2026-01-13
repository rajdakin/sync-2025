Set Default Goal Selector "!".

From Stdlib Require Import Lia.

Definition ident := nat.

Definition ident_dec (x y: ident) : {x = y} + {x <> y} := (PeanoNat.Nat.eq_dec x y).
