Set Default Goal Selector "!".

From Stdlib Require Import List.

Lemma Forall_univ : forall [A] (P : A -> Prop), (forall x, P x) -> forall l, Forall P l.
Proof using.
  intros A P HP l; induction l as [|hd tl IH]; constructor; [exact (HP _)|exact IH].
Qed.
