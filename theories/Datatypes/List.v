From Reactive Require Export Base.


Lemma in_map_fst {A B} (y: A) (xs: list (A * B)):
  In y (map fst xs) ->
    exists ys, In (y, ys) xs.
Proof.
  induction xs as [| x xs IHxs ].
  { intros. inversion H. }

  simpl.
  intros [HIn | HIn].
  { subst. exists (snd x). left. destruct x. reflexivity. }

  destruct (IHxs HIn) as [ys HIn'].
  exists ys. right. assumption.
Qed.
