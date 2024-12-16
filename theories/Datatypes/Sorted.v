From Reactive Require Import Base.
From Reactive.Datatypes Require Comparison.

From Coq Require Export Sorting.


Definition t {A: Type}: list (nat * A) -> Prop :=
  LocallySorted (fun '(i, _) '(j, _) => i < j).

(** ** Functions *)

Fixpoint add {A: Type} (i: nat) (x: A) (l: list (nat * A)): list (nat * A) :=
  match l with
  | [] => [(i, x)]
  | (j, y) :: p =>
      match i ?= j with
      | Eq => (i, x) :: p
      | Lt => (i, x) :: (j, y) :: p
      | Gt => (j, y) :: add i x p
      end
  end.

Fixpoint find {A: Type} (i: nat) (l: list (nat * A)): option A :=
  match l with
  | [] => None
  | (j, v) :: p =>
      if i =? j then Some v
      else find i p
  end.

Fixpoint min {A: Type} (l: list (nat * A)): option nat :=
  match l with
  | [] => None
  | x :: l =>
      match min l with
      | None => Some (fst x)
      | Some y => Some (Nat.min (fst x) y)
      end
  end.

Fixpoint map {A B: Type} (f: A -> B) (l: list (nat * A)): list (nat * B) :=
  match l with
  | [] => []
  | (i, x) :: p => (i, f x) :: map f p
  end.

Fixpoint remove {A: Type} (i: nat) (l: list (nat * A)): list (nat * A) :=
  match l with
  | [] => []
  | (j, x) :: p =>
      if i =? j then p
      else (j, x) :: remove i p
  end.


(** ** Proofs *)

(** *** Relations between elements *)

Lemma fst_smaller_than_snd {A: Type} (p1 p2: nat * A) (l: list (nat * A)):
  t (p1 :: p2 :: l) -> fst p1 < fst p2.
Proof.
  inversion 1; subst.
  now destruct p1, p2.
Qed.

Lemma cons {A: Type} (p: nat * A) (l: list (nat * A)):
  t (p :: l) -> t l.
Proof.
  inversion 1; subst.
  - constructor.
  - assumption.
Qed.

Lemma cons_cons {A: Type} (p1 p2: nat * A) (l: list (nat * A)):
  t (p1 :: p2 :: l) -> t (p1 :: l).
Proof.
  revert p1 p2.

  induction l as [| p3 l IH ]; intros p1 p2 H.
  { constructor. }

  constructor.
  { now do 2 apply cons in H. }

  destruct p1, p2, p3.
  apply fst_smaller_than_snd in H as Hlt1.
  apply cons in H.
  apply fst_smaller_than_snd in H as Hlt2.
  simpl in Hlt1, Hlt2.
  lia.
Qed.

Lemma change_fst_element_right_side {A: Type} (i: nat) (x y: A) (l: list (nat * A)):
  t ((i, x) :: l) -> t ((i, y) :: l).
Proof.
  intros H.
  destruct l as [| (j, z) l ].
  { constructor. }

  constructor.
  - now apply cons in H.
  - now apply fst_smaller_than_snd in H.
Qed.

Lemma in_le {A: Type} (i j: nat) (x y: A) (l: list (nat * A)):
  t ((i, x) :: l) -> In (j, y) ((i, x) :: l) -> i <= j.
Proof.
  intros Hsort Hin.
  induction l as [| (k, z) l IH ].
  { destruct Hin.
    all: now inversion H. }

  destruct Hin as [ Heq | Hin ].
  { now inversion Heq. }

  destruct Hin as [ Heq | Hin ].
  { inversion Heq; subst.
    apply fst_smaller_than_snd in Hsort.
    simpl in Hsort.
    lia. }

  apply IH.
  - now apply cons_cons in Hsort.
  - now right.
Qed.

Lemma not_twice {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  t ((i, x) :: l) ->
  ~ In i (List.map fst l).
Proof.
  intros H.
  induction l as [ | (j, y) l IH ].
  - inversion 1.
  - intros [ Heq | Hin ].
    + subst.
      apply fst_smaller_than_snd in H.
      simpl in H.
      apply PeanoNat.Nat.lt_irrefl with (x := j).
      assumption.
    + apply IH; [ | assumption ].
      inversion H.
      subst.
      destruct l as [ | (k, z) l ]; [ constructor | ].
      constructor.
      * do 2 apply cons in H.
        assumption.
      * apply fst_smaller_than_snd in H as Hlt1.
        apply cons in H.
        apply fst_smaller_than_snd in H as Hlt2.
        simpl in Hlt1, Hlt2.
        apply PeanoNat.Nat.lt_trans with (m := j); assumption.
Qed.

(** *** Find *)

Lemma find_some_is_in {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  find i l = Some x -> In (i, x) l.
Proof.
  intros H.
  induction l as [ | (j, y) l IH ].
  - inversion H.
  - simpl in *.
    destruct (i =? j) eqn: Hcomp.
    + inversion H.
      apply PeanoNat.Nat.eqb_eq in Hcomp.
      left.
      subst.
      reflexivity.
    + right.
      apply IH.
      assumption.
Qed.

Lemma in_find_some {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  t l ->
  In (i, x) l ->
    find i l = Some x.
Proof.
  intros Hsort Hin.
  induction l as [ | (j, y) l IH ]; [ inversion Hin | ].
  destruct Hin as [ Heq | Hin ].
  - inversion Heq.
    subst.
    simpl.
    rewrite PeanoNat.Nat.eqb_refl.
    reflexivity.
  - simpl.
    destruct (i =? j) eqn: Hcomp.
    + exfalso.
      apply PeanoNat.Nat.eqb_eq in Hcomp.
      subst.
      apply not_twice with (i := j) (x := y) (l := l); [ assumption | ].
      change (In (fst (j, x)) (List.map fst l)).
      apply in_map with (f := fst).
      assumption.
    + apply IH.
      * apply cons in Hsort.
        assumption.
      * assumption.
Qed.

(** *** Add *)

Lemma add_sorted {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  t l -> t (add i x l).
Proof.
  intros Hsort.

  induction l as [| (j, y) l IH ]; simpl.
  { constructor. }

  destruct (i ?= j) eqn: Hcomp.
  - apply Comparison.eq_is_eq in Hcomp; subst.
    now apply change_fst_element_right_side with (x := y).

  - constructor; [ assumption |].
    now apply Comparison.lt_is_lt.

  - destruct l as [| (k, z) l ]; simpl in *.
    { constructor; [ constructor |].
      now apply Comparison.gt_is_gt. }

    destruct (i ?= k).
    all: constructor.
    all: try apply IH.
    all: try now apply cons in Hsort.

    + now apply Comparison.gt_is_gt.
    + now apply Comparison.gt_is_gt.
    + now apply fst_smaller_than_snd in Hsort.
Defined.

Lemma add_find_new_element {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  find i (add i x l) = Some x.
Proof.
  induction l as [| (j, y) l IH ]; simpl.
  { now rewrite PeanoNat.Nat.eqb_refl. }

  destruct (i ?= j) eqn: Hcomp; simpl.
  + now rewrite PeanoNat.Nat.eqb_refl.
  + now rewrite PeanoNat.Nat.eqb_refl.
  + assert (i <> j).
    { apply Comparison.gt_is_gt in Hcomp; lia. }

    apply PeanoNat.Nat.eqb_neq in H.
    now rewrite H.
Qed.

Lemma add_find_other_element {A: Type} (i j: nat) (x: option A) (y: A) (l: list (nat * A)):
  find i (add j y l) = x ->
  i <> j ->
  find i l = x.
Proof.
  intros Hfind Hne.

  induction l as [| (k, z) l IH ].
  { destruct x; [| reflexivity ].
    apply PeanoNat.Nat.eqb_neq in Hne.
    simpl in Hfind.
    now rewrite Hne in Hfind. }

  simpl in Hfind.

  destruct (i =? k) eqn: Heq.
  - apply PeanoNat.Nat.eqb_eq in Heq.
    rewrite Heq in *.

    destruct (j ?= k) eqn: Hcomp; simpl in Hfind |- *.
    * apply Comparison.eq_is_eq in Hcomp; subst.
      contradiction.
    * apply PeanoNat.Nat.eqb_neq in Hne.
      now rewrite Hne in Hfind.
    * now rewrite PeanoNat.Nat.eqb_refl in Hfind |- *.

  - destruct (j ?= k) eqn: Hcomp; simpl in Hfind |- *.
    * apply Comparison.eq_is_eq in Hcomp.
      rewrite Hcomp in *.
      now rewrite Heq in Hfind |- *.
    * apply PeanoNat.Nat.eqb_neq in Hne.
      rewrite Heq in Hfind |- *.
      now rewrite Hne in Hfind.
    * rewrite Heq in Hfind |- *.
      now apply IH.
Qed.

Lemma find_other_added_element {A: Type} (i j: nat) (x y: A) (l: list (nat * A)):
  find i l = Some x ->
  i <> j ->
    find i (add j y l) = Some x.
Proof.
  intros Hfind Hne.
  apply PeanoNat.Nat.eqb_neq in Hne.
  induction l as [ | (k, z) l IH ]; [ discriminate | ].
  simpl in *.
  destruct (j ?= k) eqn: Hcomp.
  - simpl.
    apply Comparison.eq_is_eq in Hcomp.
    subst.
    rewrite Hne in *.
    assumption.
  - simpl.
    rewrite Hne.
    assumption.
  - simpl.
    destruct (i =? k); [ assumption | ].
    apply IH.
    assumption.
Qed.

(** *** Remove *)

Lemma remove_sorted {A: Type} (i: nat) (l: list (nat * A)):
  Sorted.t l ->
  Sorted.t (Sorted.remove i l).
Proof.
  intros H.
  revert i.
  induction l as [ | (j, x) l IH ]; intros i; [ constructor | ].
  apply Sorted.cons in H as Hinner.
  simpl.
  destruct (i =? j); [ assumption | ].
  destruct l as [ | (k, z) l ]; [ constructor | ].
  specialize (IH Hinner i).
  simpl in *.
  destruct (i =? k).
  - apply Sorted.cons_cons in H.
    assumption.
  - constructor; [ assumption | ].
    apply Sorted.fst_smaller_than_snd in H.
    assumption.
Defined.

(** *** Map *)

Lemma map_sorted {A B: Type} (f: A -> B) (l: list (nat * A)):
  t l -> t (map f l).
Proof.
  intros Hsort.
  simpl.
  induction l as [ | (i, x) l IH ]; [ constructor | ].
  destruct l as [ | (j, y) l ]; [ constructor | ].
  simpl.
  constructor.
  - apply IH.
    apply Sorted.cons in Hsort.
    assumption.
  - apply Sorted.fst_smaller_than_snd in Hsort.
    assumption.
Defined.

(** *** Minimum *)

Lemma sorted_min {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  t ((i, x) :: l) ->
  min ((i, x) :: l) = Some i.
Proof.
  intros Hsort.
  revert i x Hsort.
  induction l as [ | (j, y) l IH ]; intros i x Hsort; [ reflexivity | ].
  simpl in *.
  destruct (min l).
  - f_equal.
    assert (Some (Nat.min j n) = Some j).
    + apply IH with (x := y).
      apply cons in Hsort.
      assumption.
    + inversion H.
      rewrite H1.
      rewrite H1.
      apply PeanoNat.Nat.min_l.
      apply PeanoNat.Nat.lt_le_incl.
      apply fst_smaller_than_snd in Hsort.
      assumption.
  - apply fst_smaller_than_snd in Hsort.
    f_equal.
    apply PeanoNat.Nat.min_l.
    apply PeanoNat.Nat.lt_le_incl.
    assumption.
Qed.

(** *** Inclusion in sorted lists *)

Lemma lt_not_le_stt (n m: nat):
  n < m -> ~ m <= n.
Proof. lia. Qed.

Lemma incl_cons_same_elt {A: Type} (i: nat) (x: A) (l1 l2: list (nat * A)):
  incl ((i, x) :: l1) ((i, x) :: l2) ->
  t ((i, x) :: l1) ->
  t ((i, x) :: l2) ->
  incl l1 l2.
Proof.
  intros Hincl Hsort1 Hsort2 (j, y) Hin.
  destruct l1 as [ | (k, z) l1 ]; [ inversion Hin | ].
  pose proof Hincl as H.
  specialize (H (j, y) (in_cons _ _ _ Hin)) as [ Heq | H ]; [ | assumption ].
  exfalso.
  inversion Heq.
  subst.
  clear Heq.
  apply lt_not_le_stt with (n := j) (m := k).
  - apply Sorted.fst_smaller_than_snd in Hsort1.
    assumption.
  - apply in_le in Hin; [ assumption | ].
    apply cons in Hsort1.
    assumption.
Qed.

(** *** No duplicate *)

Lemma no_dup_left_handside {A: Type} (l: list (nat * A)):
  Sorted.t l ->
  NoDup (List.map fst l).
Proof.
  intros Hsort.
  simpl.
  induction l as [ | (i, x) l IH ]; [ constructor | ].
  simpl.
  constructor.
  - apply Sorted.not_twice with (x := x).
    assumption.
  - apply IH.
    apply Sorted.cons in Hsort.
    assumption.
Qed.

(** *** Equivalence *)

Lemma equivalence_head {A: Type} (i j: nat) (x y: A) (l1 l2: list (nat * A)):
  incl ((i, x) :: l1) ((j, y) :: l2) ->
  incl ((j, y) :: l2) ((i, x) :: l1) ->
  Sorted.t ((i, x) :: l1) ->
  Sorted.t ((j, y) :: l2) ->
    (i, x) = (j, y).
Proof.
  intros Hincl1 Hincl2 Hsort1 Hsort2.
  apply Sorted.sorted_min in Hsort1 as Hmin1.
  apply Sorted.sorted_min in Hsort2 as Hmin2.
  specialize (Hincl1 (i, x) (in_eq _ _)).
  pose proof (Sorted.in_le _ _ _ _ _ Hsort2 Hincl1) as Hle1.
  specialize (Hincl2 (j, y) (in_eq _ _)).
  pose proof (Sorted.in_le _ _ _ _ _ Hsort1 Hincl2) as Hle2.
  pose proof (PeanoNat.Nat.le_antisymm i j Hle2 Hle1).
  subst.
  destruct Hincl1 as [ Heq | Hin ]; [ auto | ].
  exfalso.
  pose proof (no_dup_left_handside ((j, y) :: l2) Hsort2).
  simpl in H.
  apply NoDup_cons_iff in H as [ H _ ].
  apply H.
  apply in_map with (f := fst) in Hin.
  assumption.
Qed.

Lemma equivalence_is_eq {A: Type} (l1 l2: list (nat * A)):
  incl l1 l2 ->
  incl l2 l1 ->
  Sorted.t l1 ->
  Sorted.t l2 ->
    l1 = l2.
Proof.
  intros Hincl1 Hincl2 Hsort1 Hsort2.
  revert l2 Hincl1 Hincl2 Hsort2.
  induction l1 as [ | (i, x) l1 IH ]; intros l2 Hincl1 Hincl2 Hsort2.
  - symmetry.
    apply incl_l_nil.
    assumption.
  - destruct l2 as [ | (j, y) l2 ].
    + apply incl_l_nil in Hincl1.
      discriminate.
    + f_equal.
      * apply equivalence_head with (l1 := l1) (l2 := l2); assumption.
      * apply IH.
        -- apply Sorted.cons in Hsort1.
           assumption.
        -- assert ((i, x)  = (j, y)) as H.
           { apply equivalence_head with (l1 := l1) (l2 := l2); assumption. }
           inversion H.
           subst.
           apply Sorted.incl_cons_same_elt with (i := j) (x := y); assumption.
        -- assert ((i, x)  = (j, y)) as H.
           { apply equivalence_head with (l1 := l1) (l2 := l2); assumption. }
           inversion H.
           subst.
           apply Sorted.incl_cons_same_elt with (i := j) (x := y); assumption.
        -- apply Sorted.cons in Hsort2.
           assumption.
Qed.
