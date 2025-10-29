From Reactive Require Import Base.

From Stdlib Require Import Permutation ListDec.

Lemma nodup_permutation_app_r {A} {l1 l2 l3: list A}:
  Permutation l2 l3 -> NoDup (l1 ++ l2) -> NoDup (l1 ++ l3).
Proof.
  induction l1 as [ | a l1 IH].
  1: apply Permutation_NoDup.
  
  intros perm nodup.
  simpl in nodup.
  apply NoDup_cons_iff in nodup.
  destruct nodup as [notin nodup].
  specialize (IH perm nodup).
  simpl.
  apply NoDup_cons.
  2: assumption.

  apply (Permutation_app_head l1) in perm.

  intro isin.

  apply (Permutation_in a (Permutation_sym perm)) in isin.
  contradiction.
Qed.

Lemma NoDup_remove_inv:
  forall {A} (l l': list A) (a: A),
  NoDup (l ++ l') /\ ~ In a (l ++ l') -> NoDup (l ++ a :: l').
Proof.
  intros A l l' a.
  induction l as [ | b l IH].
  1: simpl.
  1: intros [].
  1: apply NoDup_cons.
  1,2: assumption.
  simpl.
  intros [nodup notin].

  apply Decidable.not_or in notin.
  destruct notin as [bdifa anotin].

  apply NoDup_cons_iff in nodup.
  destruct nodup as [bnotin nodup].

  apply NoDup_cons.
  - clear -bdifa bnotin.
    induction l as [| c l IH].
    + simpl.
      simpl in bnotin.
      intros []; auto.
    + simpl.
      intros [cb | bin].
      * subst.
        simpl in bnotin.
        contradiction bnotin.
        left; reflexivity.
      * contradiction IH.
        intro binll.
        apply bnotin.
        simpl.
        right.
        assumption.
  - apply IH.
    split; assumption.
Qed.

Lemma nodup_permutation_app_l {A} {l1 l2 l3: list A}:
  Permutation l1 l3 -> NoDup (l1 ++ l2) -> NoDup (l3 ++ l2).
Proof.
  induction l2 as [ | a l2 IH].
  1: do 2 rewrite app_nil_r.
  1: apply Permutation_NoDup.

  intros perm nodup.
  apply NoDup_remove in nodup.
  destruct nodup as [nodup notin].
  specialize (IH perm nodup).

  simpl.
  apply NoDup_remove_inv.
  split.
  1: assumption.
  intro ina.
  apply in_app_or in ina.

  apply notin.
  apply in_or_app.

  destruct ina as [ina | ina].

  - left.
    exact (Permutation_in a (Permutation_sym perm) ina).
  - right. assumption.
Qed.

Lemma NoDup_remove {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a: A) (l: list A):
  NoDup l -> NoDup (List.remove eq_dec a l).
Proof.
  intro nodup.
  induction l as [| b l IH].
  - apply NoDup_nil.
  - apply NoDup_cons_iff in nodup.
    destruct nodup as [notin nodup].
    specialize (IH nodup).
    simpl.
    destruct (eq_dec a b).
    1: subst; assumption.
    apply NoDup_cons_iff.
    split.
    2: assumption.
    intro inb.
    apply in_remove in inb.
    destruct inb.
    contradiction.
Qed.

Lemma permutation_nodup_remove_cons {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (a: A) (l l': list A):
  Permutation (a::l) l' -> NoDup (a::l) -> Permutation l (List.remove eq_dec a l').
Proof.
  intros permut nodup.

  assert (nodup_l' := nodup).

  apply NoDup_cons_iff in nodup.
  destruct nodup as [notin nodup_l].

  apply (Permutation_NoDup permut) in nodup_l'.

  apply NoDup_Permutation.
  - assumption.
  - apply (NoDup_remove eq_dec _ _ nodup_l').
  - intro x.
    destruct (eq_dec x a) as [? | noteq].
    + subst.
      split.
      1: contradiction.
      intro in_contra.
      apply remove_In in in_contra.
      contradiction.
    + split.
      * intro xinl.
        apply (Permutation_in x) in permut.
        2: right; assumption.
        apply (in_in_remove eq_dec _ noteq permut).
      * intro xinl.
        apply (in_remove eq_dec _ _ _) in xinl.
        destruct xinl as [xinl _].
        apply Permutation_sym in permut.
        apply (Permutation_in x) in permut.
        2: assumption.
        destruct permut.
        1: contradiction noteq; symmetry; assumption.
        assumption.
Qed.

Lemma add_removed {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a: A) (l: list A):
  In a l -> NoDup l -> Permutation l (a :: (List.remove eq_dec a l)).
Proof.
  induction l as [| b l IH].
  1: intros; contradiction.
  intros ain nodup.
  simpl.
  apply NoDup_cons_iff in nodup.
  destruct nodup as [notin nodup].
  destruct (eq_dec a b) as [| noteq].
  - subst.
    rewrite (notin_remove _ _ _ notin).
    apply Permutation_refl.
  - simpl in ain.
    destruct ain as [| ain].
    1: contradiction noteq; symmetry; assumption.
    specialize (IH ain nodup).
    refine (Permutation_trans _ (perm_swap _ _ _)).
    apply perm_skip.
    assumption.
Qed.

