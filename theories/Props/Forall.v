Set Default Goal Selector "!".

From Stdlib Require Import List.

Lemma Forall2_rev : forall [A B] (P : A -> B -> Prop) l1 l2, Forall2 P l1 l2 -> Forall2 P (rev l1) (rev l2).
Proof using.
  intros A B P l1 l2 H; induction H as [|hd1 hd2 tl1 tl2 H1 H2 IH]; [exact (Forall2_nil _)|cbn].
  exact (Forall2_app IH (Forall2_cons _ _ H1 (Forall2_nil _))).
Qed.

Lemma Forall_impl_in {A: Type} (P Q: A -> Prop) (l: list A):
  (forall a : A, In a l -> P a -> Q a) ->
  Forall P l -> Forall Q l.
Proof.
  intros H Hforall.
  induction l as [ | x l ]; [ constructor | ].
  constructor.
  - apply H.
    + left.
      reflexivity.
    + apply Forall_inv with (l := l).
      assumption.
  - apply IHl.
    + intros a Hin HPa.
      apply H; [ | assumption ].
      right.
      assumption.
    + apply Forall_inv_tail with (a := x).
      assumption.
Qed.
