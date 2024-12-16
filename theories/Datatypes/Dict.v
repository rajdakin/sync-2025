From Reactive Require Import Base.
From Reactive.Datatypes Require Comparison Sorted.


Record t (A: Type): Type := {
  d_elements: list (nat * A);
  d_sorted: Sorted.t d_elements;
}.

Arguments d_elements {A}.
Arguments d_sorted {A}.


(** ** Functions *)

Definition add {A: Type} (i: nat) (x: A) (d: t A): t A := {|
  d_elements := Sorted.add i x d.(d_elements);
  d_sorted := Sorted.add_sorted i x d.(d_elements) d.(d_sorted);
|}.

Definition empty (A: Type): t A := {|
  d_elements := [];
  d_sorted := Sorted.LSorted_nil _;
|}.

Definition map {A B: Type} (f: A -> B) (d: t A): t B := {|
  d_elements := Sorted.map f d.(d_elements);
  d_sorted := Sorted.map_sorted f d.(d_elements) d.(d_sorted);
|}.

Definition remove {A: Type} (i: nat) (d: t A): t A := {|
  d_elements := Sorted.remove i d.(d_elements);
  d_sorted := Sorted.remove_sorted i d.(d_elements) d.(d_sorted);
|}.


(** ** Properties *)

Definition find {A: Type} (i: nat) (d: t A): option A :=
  Sorted.find i d.(d_elements).

Definition maps_to {A: Type} (i: nat) (x: A) (d: t A): Prop :=
  find i d = Some x.

Definition is_in {A: Type} (i: nat) (d: t A): Prop :=
  exists x: A, maps_to i x d.

Definition inclusion {A: Type} (d1 d2: t A): Prop :=
  forall (i: nat) (x: A),
    maps_to i x d1 -> maps_to i x d2.

Definition equivalence {A: Type} (d1 d2: t A): Prop :=
  inclusion d1 d2 /\ inclusion d2 d1.

Definition ForAll {A: Type} (P: ident -> A -> Prop) (d: t A): Prop :=
  forall (i: ident) (x: A), Dict.maps_to i x d -> P i x.

(** ** Proofs *)

(** *** Maps to *)

Lemma maps_to_imp_is_in {A: Type} (i: nat) (x: A) (d: t A):
  maps_to i x d -> is_in i d.
Proof.
  now exists x.
Qed.

(** *** Add *)

Lemma maps_to_add {A: Type} (i j: nat) (x y: A) (d: t A):
  maps_to i x d ->
  i <> j ->
    maps_to i x (add j y d).
Proof.
  intros Hmaps Hne.
  destruct d as [ l Hsort ].
  unfold maps_to, find in *.
  simpl in *.
  apply Sorted.find_some_is_in in Hmaps.
  apply Sorted.in_find_some.
  - apply Sorted.add_sorted.
    assumption.
  - induction l as [ | (k, z) l IH ]; [ inversion Hmaps | ].
    simpl.
    destruct (j ?= k) eqn: Hcomp.
    + apply Comparison.eq_is_eq in Hcomp.
      subst.
      destruct Hmaps as [ Heq | Hin ].
      * exfalso.
        apply Hne.
        inversion Heq.
        reflexivity.
      * right.
        assumption.
    + right.
      assumption.
    + destruct Hmaps as [ Heq | Hin ].
      * left.
        assumption.
      * right.
        apply IH; [ | assumption ].
        apply Sorted.cons in Hsort.
        assumption.
Qed.

(** *** Map *)

Lemma maps_to_map {A B: Type} (f: A -> B) (i: nat) (x: A) (d: t A):
  maps_to i x d -> maps_to i (f x) (map f d).
Proof.
  destruct d as [ l Hsort ].
  unfold map, maps_to, find.
  simpl.
  intros H.
  induction l as [ | (j, y) l IH ]; [ discriminate | ].
  simpl in *.
  destruct (i =? j).
  - inversion H.
    reflexivity.
  - apply IH; [ | assumption ].
    apply Sorted.cons in Hsort.
    assumption.
Qed.

(** *** Remove *)

Lemma removed_element_not_in {A: Type} (i: nat) (d: t A):
  ~ is_in i (remove i d).
Proof.
  intros H.
  destruct d as [ l Hsort ].
  unfold is_in, maps_to, find in H.
  destruct H as [ x Hx ].
  simpl in Hx.
  induction l as [ | (j, y) l IH ]; [ discriminate | ].
  simpl in Hx.
  destruct (i =? j) eqn: Heq.
  - apply PeanoNat.Nat.eqb_eq in Heq.
    subst.
    apply Sorted.not_twice in Hsort.
    apply Hsort.
    apply Sorted.find_some_is_in in Hx.
    apply in_map with (f := fst) in Hx.
    assumption.
  - apply IH.
    + apply Sorted.cons in Hsort.
      assumption.
    + simpl in Hx.
      rewrite Heq in Hx.
      assumption.
Qed.

Lemma maps_to_not_removed {A: Type} (i j: nat) (x: A) (d: t A):
  maps_to i x d ->
  i <> j ->
    maps_to i x (remove j d).
Proof.
  destruct d as [ l Hsort ].
  unfold maps_to, find.
  simpl.
  intros Hmaps Hne.
  induction l as [ | (k, z) l IH ]; [ discriminate | ].
  simpl.
  destruct (j =? k) eqn: Heq.
  - apply PeanoNat.Nat.eqb_eq in Heq.
    subst.
    simpl in Hmaps.
    apply PeanoNat.Nat.eqb_neq in Hne.
    rewrite Hne in Hmaps.
    assumption.
  - simpl in *.
    destruct (i =? k); [ assumption | ].
    apply IH.
    + apply Sorted.cons in Hsort.
      assumption.
    + assumption.
Qed.

Lemma maps_to_with_removal {A: Type} (i j: nat) (x: A) (d: t A):
  maps_to i x (remove j d) ->
    maps_to i x d.
Proof.
  destruct d as [ l Hsort ].
  unfold maps_to, find.
  simpl.
  intros H.
  induction l as [ | (k, z) l IH ]; [ discriminate | ].
  simpl in *.
  destruct (i =? k) eqn: Heqik.
  - apply PeanoNat.Nat.eqb_eq in Heqik.
    subst.
    destruct (j =? k) eqn: Heqjk.
    + apply PeanoNat.Nat.eqb_eq in Heqjk.
      subst.
      exfalso.
      apply Sorted.change_fst_element_right_side with (y := x) in Hsort.
      apply removed_element_not_in with (i := k) (d := {| d_elements := (k, x) :: l; d_sorted := Hsort |}).
      exists x.
      unfold maps_to, find.
      simpl.
      rewrite PeanoNat.Nat.eqb_refl.
      assumption.
    + simpl in H.
      rewrite PeanoNat.Nat.eqb_refl in H.
      assumption.
  - destruct (j =? k); [ assumption | ].
    apply IH.
    + apply Sorted.cons in Hsort.
      assumption.
    + simpl in H.
      rewrite Heqik in H.
      assumption.
Qed.

(** *** No dupliacte *)

Theorem no_dup_left_handside {A: Type} (d: t A):
  NoDup (List.map fst d.(d_elements)).
Proof.
  destruct d as [ l Hsort ].
  simpl.
  apply Sorted.no_dup_left_handside.
  assumption.
Qed.

(** *** Equivalence *)

Lemma inclusion_is_list_incl {A: Type} (d1 d2: t A):
  inclusion d1 d2 <-> incl d1.(d_elements) d2.(d_elements).
Proof.
  destruct d1 as [ l1 Hsort1 ].
  destruct d2 as [ l2 Hsort2 ].
  split.
  - intros H [ i x ] Hin.
    unfold inclusion, maps_to, find in H.
    simpl in *.
    revert l2 Hsort2 H.
    induction l1 as [ | (j, y) l1 IH ]; intros l2 Hsort2 H.
    + inversion Hin.
    + destruct Hin as [ Heq | Hin ].
      * inversion Heq.
        subst.
        apply Sorted.find_some_is_in.
        apply H.
        simpl.
        rewrite PeanoNat.Nat.eqb_refl.
        reflexivity.
      * apply Sorted.cons in Hsort1 as Hsort1_inner.
        apply IH; [ assumption.. | ].
        intros k z Hkz.
        apply H.
        simpl.
        destruct (k =? j) eqn: Hcomp; [ | assumption ].
        exfalso.
        apply PeanoNat.Nat.eqb_eq in Hcomp.
        subst.
        apply Sorted.not_twice with (i := j) (x := y) (l := l1); [ assumption | ].
        change (In (fst (j, z)) (List.map fst l1)).
        apply in_map with (f := fst).
        apply Sorted.find_some_is_in in Hkz.
        assumption.
  - unfold inclusion, maps_to, find.
    simpl in *.
    intros H i x Hfind.
    induction l1 as [ | (j, y) l1 IH ].
    + inversion Hfind.
    + pose proof Hfind as Hfind'.
      simpl in Hfind'.
      destruct (i =? j) eqn: Hcomp.
      * inversion Hfind'.
        subst.
        apply Sorted.find_some_is_in in Hfind.
        apply H in Hfind.
        apply Sorted.in_find_some in Hfind; assumption.
      * apply Sorted.find_some_is_in in Hfind'.
        apply Sorted.in_find_some; [ assumption | ].
        apply H.
        right.
        assumption.
Qed.

Lemma equivalence_is_elements_eq {A: Type} (d1 d2: t A):
  equivalence d1 d2 <-> d1.(d_elements) = d2.(d_elements).
Proof.
  simpl.
  split.
  - intros [ H1 H2 ].
    apply Sorted.equivalence_is_eq.
    + apply inclusion_is_list_incl.
      assumption.
    + apply inclusion_is_list_incl.
      assumption.
    + apply d1.(d_sorted).
    + apply d2.(d_sorted).
  - intros H.
    unfold equivalence, inclusion, maps_to, find.
    rewrite H.
    auto.
Qed.

Theorem equivalence_is_eq {A: Type} (d1 d2: t A):
  equivalence d1 d2 <-> d1 = d2.
Proof.
  split.
  - intros H.
    destruct d1 as [ l1 Hsort1 ].
    destruct d2 as [ l2 Hsort2 ].
    apply equivalence_is_elements_eq in H.
    simpl in H.
    subst.
    pose proof (ProofIrrelevance _ Hsort1 Hsort2).
    subst.
    reflexivity.
  - intros.
    apply f_equal with (f := fun d => d_elements d) in H.
    apply equivalence_is_elements_eq in H.
    assumption.
Qed.

Lemma no_element_is_empty {A: Type} (d: t A):
  d.(d_elements) = [] <-> d = empty A.
Proof.
  destruct d as [ l Hsort ].
  simpl.
  split.
  - intros H.
    apply equivalence_is_eq.
    split.
    + intros i x Hmaps.
      unfold maps_to, find in Hmaps.
      simpl in Hmaps.
      rewrite H in Hmaps.
      discriminate.
    + intros i x Hmaps.
      unfold maps_to, find in Hmaps.
      discriminate.
  - intros H.
    unfold empty in H.
    inversion H.
    reflexivity.
Qed.

(** *** Equivalence consequences *)

Lemma remove_then_add_same_elt {A: Type} (i: nat) (x: A) (d: t A):
  maps_to i x d ->
    d = add i x (remove i d).
Proof.
  destruct d as [ l Hsort ].
  simpl.
  intros H.
  apply equivalence_is_eq.
  split.
  - intros j y Hmaps.
    unfold maps_to, find in *.
    simpl in *.
    destruct (PeanoNat.Nat.eq_dec j i).
    + subst.
      rewrite H in Hmaps.
      inversion Hmaps.
      apply Sorted.add_find_new_element.
    + induction l as [ | (k, z) l IH ]; [ discriminate | ].
      simpl in *.
      destruct (i =? k) eqn: Heqik.
      * apply Sorted.cons in Hsort.
        change (maps_to j y (add i x {| d_elements := l; d_sorted := Hsort |})).
        apply maps_to_add; [ | assumption ].
        destruct (j =? k) eqn: Heqjk.
        -- inversion Hmaps.
           subst.
           exfalso.
           apply n.
           apply PeanoNat.Nat.eqb_eq in Heqik, Heqjk.
           subst.
           reflexivity.
        -- unfold maps_to, find.
           simpl.
           assumption.
      * simpl.
        destruct (i ?= k) eqn: Hcomp.
        -- exfalso.
           apply PeanoNat.Nat.eqb_neq in Heqik.
           apply Comparison.eq_is_eq in Hcomp.
           auto.
        -- simpl.
           apply PeanoNat.Nat.eqb_neq in n.
           rewrite n.
           destruct (j =? k); [ assumption | ].
           apply Sorted.cons in Hsort.
           change (maps_to j y (remove i {| d_elements := l; d_sorted := Hsort |})).
           apply PeanoNat.Nat.eqb_neq in n.
           apply maps_to_not_removed; [ | assumption ].
           unfold maps_to, find.
           assumption.
        -- simpl.
           destruct (j =? k); [ assumption | ].
           apply IH; [ | assumption | assumption ].
           apply Sorted.cons in Hsort.
           assumption.
  - intros j y Hmaps.
    unfold maps_to, find in *.
    simpl in *.
    induction l as [ | (k, z) l IH ]; [ discriminate | ].
    simpl in *.
    destruct (j =? k) eqn: Heqjk.
    + apply PeanoNat.Nat.eqb_eq in Heqjk.
      subst.
      destruct (i =? k) eqn: Heqik.
      * apply PeanoNat.Nat.eqb_eq in Heqik.
        subst.
        pose proof (Sorted.add_find_new_element k x l) as H'.
        rewrite H' in Hmaps.
        inversion H.
        inversion Hmaps.
        reflexivity.
      * simpl in Hmaps.
        destruct (i ?= k) eqn: Hcomp.
        -- exfalso.
           apply PeanoNat.Nat.eqb_neq in Heqik.
           apply Comparison.eq_is_eq in Hcomp.
           auto.
        -- simpl in Hmaps.
           rewrite PeanoNat.Nat.eqb_sym in Heqik.
           rewrite Heqik in Hmaps.
           rewrite PeanoNat.Nat.eqb_refl in Hmaps.
           assumption.
        -- simpl in Hmaps.
           rewrite PeanoNat.Nat.eqb_refl in Hmaps.
           assumption.
    + destruct (i =? k) eqn: Heqik.
      * apply PeanoNat.Nat.eqb_eq in Heqik.
        inversion H.
        subst.
        apply PeanoNat.Nat.eqb_neq in Heqjk.
        apply Sorted.add_find_other_element in Hmaps; assumption.
      * apply PeanoNat.Nat.eqb_neq in Heqik.
        apply IH.
        -- apply Sorted.cons in Hsort.
           assumption.
        -- assumption.
        -- destruct (PeanoNat.Nat.eq_dec i j) as [ eq | ne ].
           ++ subst.
              rewrite Sorted.add_find_new_element in *.
              assumption.
           ++ apply Sorted.add_find_other_element in Hmaps; [ | symmetry; assumption ].
              simpl in Hmaps.
              rewrite Heqjk in Hmaps.
              apply Sorted.find_other_added_element; [ assumption | ].
              auto.
Qed.
