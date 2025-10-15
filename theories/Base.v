#[export] Set Default Goal Selector "!".

From Stdlib Require Export List Nat String.
From Stdlib Require Export Lia.

Export ListNotations.
Open Scope nat_scope.

Lemma sig2T_eq :
  forall {A : Type}, (forall x y : A, {x = y} + {x <> y}) ->
  forall {P : A -> Type} {u x y}, existT P u x = existT P u y -> x = y.
Proof using.
  intros A HA P u x y Hxy.
  specialize (projT2_eq Hxy : eq_rect u P x u (projT1_eq Hxy) = y) as tmp.
  rewrite (Eqdep_dec.UIP_dec HA (projT1_eq Hxy) eq_refl) in tmp.
  exact tmp.
Qed.

Axiom ProofIrrelevance: forall (P: Prop) (p q: P), p = q.

Lemma sig2T_eq_PI :
  forall {A : Type} {P : A -> Type} {u x y}, existT P u x = existT P u y -> x = y.
Proof using.
  intros A P u x y Hxy.
  specialize (projT2_eq Hxy : eq_rect u P x u (projT1_eq Hxy) = y) as tmp.
  rewrite (ProofIrrelevance _ (projT1_eq Hxy) eq_refl) in tmp.
  exact tmp.
Qed.

Definition ident := nat.
