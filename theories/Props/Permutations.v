Set Default Goal Selector "!".

From Stdlib Require Import List Permutation ListDec.

Import ListNotations.

Lemma NoDup_permutation_app_l {A} {l1 l2 l3: list A}:
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

Lemma NoDup_permutation_app_r {A} {l1 l2 l3: list A}:
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

Lemma permutation_NoDup_remove_cons {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (a: A) (l l': list A):
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

Lemma permutation_add_removed {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a: A) (l: list A):
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

Lemma NoDup_app_list_remove_r {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a: A) (l1 l2: list A):
  NoDup (l1 ++ l2) -> NoDup (l1 ++ (List.remove eq_dec a l2)).
Proof.
  intro nodup.
  induction l1 as [| b l1 IH].
  - apply NoDup_remove.
    assumption.
  - simpl.
    inversion nodup; subst.
    constructor.
    2: tauto.
    rewrite in_app_iff.
    intros [inl1 | inl2].
    + apply H1.
      apply in_or_app.
      tauto.
    + apply in_remove in inl2.
      destruct inl2 as [inl2 _].
      apply H1.
      apply in_or_app.
      tauto.
Qed.

Lemma NoDup_app_list_remove_l {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a: A) (l1 l2: list A):
  NoDup (l1 ++ l2) -> NoDup ((List.remove eq_dec a l1) ++ l2).
Proof.
  intro nodup.
  induction l1 as [| b l1 IH].
  1: assumption.
  simpl.
  inversion nodup; subst.
  specialize (IH H2).
  destruct (eq_dec a b); subst.
  - assumption.
  - simpl.
    constructor.
    2: assumption.
    rewrite in_app_iff.
    intros [inl1 | inl2].
    + apply in_remove in inl1.
      destruct inl1 as [inl1 _].
      apply H1.
      apply in_or_app.
      tauto.
    + apply H1.
      apply in_or_app.
      tauto.
Qed.

Lemma nodup_app_in_l {A} (x: A) (l r: list A):
  NoDup (l ++ r) -> In x l -> ~In x r.
Proof.
  intros nodup isin.
  induction l as [| a l IH].
  1: inversion isin.
  simpl in isin.
  simpl in nodup.
  apply NoDup_cons_iff in nodup.
  destruct nodup as [notin nodup].
  specialize (IH nodup).
  destruct isin as [eq | isin].
  - subst.
    intro inxr.
    apply notin.
    apply in_or_app.
    right.
    assumption.
  - tauto.
Qed.

Lemma nodup_app_in_r {A} (x: A) (l r: list A):
  NoDup (l ++ r) -> In x r -> ~In x l.
Proof.
  intros nodup isin.
  induction l as [| a l IH].
  1: tauto.
  intro isinl.
  simpl in nodup.
  apply NoDup_cons_iff in nodup.
  destruct nodup as [notin nodup].
  specialize (IH nodup).
  destruct isinl as [eq | isinl].
  - subst.
    apply notin.
    apply in_or_app.
    right.
    assumption.
  - contradiction.
Qed.

Lemma nodup_app_in_mid {A} (x: A) (l r m: list A):
  NoDup (l ++ m ++ r) -> In x (l ++ r) -> ~In x m.
Proof.
  intros nodup isin.
  induction l as [| a l IH].
  - apply (nodup_app_in_r _ _ r).
    all: assumption.
  - simpl in isin.
    simpl in nodup.
    apply NoDup_cons_iff in nodup.
    destruct nodup as [notin nodup].
    specialize (IH nodup).
    destruct isin as [eq | isin].
    2: tauto.
    subst.
    intro.
    apply notin.
    apply in_or_app.
    right.
    apply in_or_app.
    left.
    assumption.
Qed.
