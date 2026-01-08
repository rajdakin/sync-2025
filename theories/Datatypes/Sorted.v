Set Default Goal Selector "!".

From Reactive.Props Require Comparison.

From Stdlib Require Import Nat List Lia.
From Stdlib Require Export Sorting.

Import ListNotations.


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

Fixpoint index_inb (i: nat) (l: list nat): bool :=
  match l with
  | [] => false
  | j :: p =>
    if i =? j then true else index_inb i p
  end.

Fixpoint filter {A: Type} (elems: list nat) (l: list (nat * A)): list (nat * A) :=
  match l with
  | [] => []
  | (j, x) :: p => if index_inb j elems then (j, x) :: (filter elems p) else filter elems p
  end.

(** ** Proofs *)

(** *** Relations between elements *)

Lemma in_map_fst {A B} (y: A) (xs: list (A * B)):
  In y (List.map fst xs) ->
    exists ys, In (y, ys) xs.
Proof.
  induction xs as [| x xs IHxs ].
  { inversion 1. }

  intros [ | HIn ].
  - subst.
    exists (snd x).
    left.
    destruct x.
    reflexivity.
  - destruct (IHxs HIn) as [ ys HIn' ].
    exists ys.
    right.
    assumption.
Qed.

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

  induction l as [| (j, y) l IH ].
  { inversion 1. }

  intros [ <- | Hin ].
  { apply fst_smaller_than_snd in H.
    simpl in H.
    lia. }

  apply IH; [| assumption ].
  inversion H; subst.
  now apply cons_cons with (j, y).
Qed.

(** *** Find *)

Lemma find_some_is_in {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  find i l = Some x -> In (i, x) l.
Proof.
  intros H.

  induction l as [| (j, y) l IH ].
  { inversion H. }

  simpl in *.
  destruct (i =? j) eqn: Hcomp.
  - left.
    inversion H.
    f_equal; symmetry.
    now apply PeanoNat.Nat.eqb_eq.

  - right.
    now apply IH.
Qed.

Lemma in_find_some {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  t l ->
  In (i, x) l ->
  find i l = Some x.
Proof.
  intros Hsort Hin.

  induction l as [| (j, y) l IH ].
  { inversion Hin. }

  destruct Hin as [ -> | Hin ]; simpl.
  { now rewrite PeanoNat.Nat.eqb_refl. }

  destruct (i =? j) eqn: Hcomp.
  2: { apply cons in Hsort. now apply IH. }

  exfalso.
  apply PeanoNat.Nat.eqb_eq in Hcomp; subst.
  apply not_twice with (i := j) (x := y) (l := l); [ assumption |].
  change (In (fst (j, x)) (List.map fst l)).
  now apply in_map with (f := fst).
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

  induction l as [| (k, z) l IH ].
  { discriminate. }

  simpl in Hfind |- *.
  destruct (j ?= k) eqn: Hcomp; simpl.
  - apply Comparison.eq_is_eq in Hcomp; subst.
    now rewrite Hne in Hfind |- *.
  - now rewrite Hne.
  - destruct (i =? k); [ assumption |].
    now apply IH.
Qed.

(** *** Remove *)

Lemma remove_sorted {A: Type} (i: nat) (l: list (nat * A)):
  t l ->
  t (remove i l).
Proof.
  intros H.
  revert i.

  induction l as [| (j, x) l IH ]; intros i.
  { constructor. }

  apply cons in H as Hinner; simpl.
  destruct (i =? j); [ assumption |].

  destruct l as [| (k, z) l ].
  { constructor. }

  specialize (IH Hinner i); simpl in *.
  destruct (i =? k).
  - now apply cons_cons in H.
  - constructor; [ assumption |].
    now apply fst_smaller_than_snd in H.
Defined.

(** *** Filter *)
Lemma in_filter {A: Type} (elems: list nat) (l: list (nat * A)) (v: nat * A):
  In v (filter elems l) -> In v l.
Proof.
  revert v elems.
  induction l as [| (j, a) l IH].
  all: intros v elem.
  1: tauto.
  simpl.
  destruct (index_inb j elem).
  1: simpl.
  1: destruct 1 as [|].
  1: left; assumption.
  1: right; apply (IH v elem H).
  intro inv.
  right.
  apply (IH v elem inv).
Qed.

Lemma filter_sorted {A: Type} (elems: list nat) (l: list (nat * A)):
  t l -> t (filter elems l).
Proof.
  intros H.

  induction l as [| (j, x) l IH].
  1: constructor.

  apply cons in H as Hinner; simpl.
  specialize (IH Hinner).

  destruct (index_inb j elems).
  2: assumption.
  destruct (filter elems l) eqn: eqfilt.
  1: constructor.
  constructor.
  1: assumption.
  destruct p as [jj].
  assert (isinl : In (jj, a) l).
  {
    apply (in_filter elems).
    rewrite eqfilt.
    left.
    reflexivity.
  }
  clear - H isinl.
  induction l.
  1: contradiction.
  specialize (IHl (cons_cons _ _ _ H)).
  simpl in isinl.
  destruct isinl as [iseq | isinl].
  2: apply (IHl isinl).
  inversion H; subst.
  assumption.
Qed.


(** *** Map *)

Lemma map_sorted {A B: Type} (f: A -> B) (l: list (nat * A)):
  t l -> t (map f l).
Proof.
  intros Hsort.

  induction l as [| (i, x) l IH ].
  { constructor. }

  destruct l as [| (j, y) l ]; simpl.
  { constructor. }

  constructor.
  + apply IH.
    now apply cons in Hsort.
  + now apply fst_smaller_than_snd in Hsort.
Defined.

(** *** Minimum *)

Lemma sorted_min {A: Type} (i: nat) (x: A) (l: list (nat * A)):
  t ((i, x) :: l) ->
  min ((i, x) :: l) = Some i.
Proof.
  revert i x.

  induction l as [| (j, y) l IH ]; intros i x Hsort.
  { reflexivity. }

  simpl in *.
  destruct (min l).
  - assert (Some (Nat.min j n) = Some j).
    { apply IH with (x := y).
      now apply cons in Hsort. }

    inversion H.
    apply fst_smaller_than_snd in Hsort.
    simpl in Hsort.
    f_equal.
    lia.

  - apply fst_smaller_than_snd in Hsort.
    simpl in Hsort.
    f_equal.
    lia.
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

  destruct l1 as [| (k, z) l1 ].
  { inversion Hin. }

  pose proof Hincl as H.
  specialize (H (j, y) (in_cons _ _ _ Hin)) as [ Heq | H ]; [| assumption ].

  exfalso.
  inversion Heq; subst.
  apply lt_not_le_stt with (n := j) (m := k).
  - now apply fst_smaller_than_snd in Hsort1.
  - apply in_le in Hin; [ assumption |].
    now apply cons in Hsort1.
Qed.

(** *** No duplicate *)

Lemma no_dup_left_handside {A: Type} (l: list (nat * A)):
  t l ->
  NoDup (List.map fst l).
Proof.
  intros Hsort.

  induction l as [| (i, x) l IH ].
  { constructor. }

  simpl.
  constructor.
  - now apply not_twice with (x := x).
  - apply cons in Hsort.
    now apply IH.
Qed.

(** *** Equivalence *)

Lemma equivalence_head {A: Type} (i j: nat) (x y: A) (l1 l2: list (nat * A)):
  incl ((i, x) :: l1) ((j, y) :: l2) ->
  incl ((j, y) :: l2) ((i, x) :: l1) ->
  t ((i, x) :: l1) ->
  t ((j, y) :: l2) ->
    (i, x) = (j, y).
Proof.
  intros Hincl1 Hincl2 Hsort1 Hsort2.
  apply sorted_min in Hsort1 as Hmin1.
  apply sorted_min in Hsort2 as Hmin2.

  specialize (Hincl1 (i, x) (in_eq _ _)).
  pose proof (in_le _ _ _ _ _ Hsort2 Hincl1) as Hle1.
  specialize (Hincl2 (j, y) (in_eq _ _)).
  pose proof (in_le _ _ _ _ _ Hsort1 Hincl2) as Hle2.
  pose proof (PeanoNat.Nat.le_antisymm i j Hle2 Hle1).
  subst.

  destruct Hincl1 as [ Heq | Hin ]; [ now symmetry |].
  exfalso.
  pose proof (no_dup_left_handside ((j, y) :: l2) Hsort2).
  simpl in H.
  apply NoDup_cons_iff in H as [ H _ ].
  apply H.
  now apply in_map with (f := fst) in Hin.
Qed.

Lemma equivalence_is_eq {A: Type} (l1 l2: list (nat * A)):
  incl l1 l2 ->
  incl l2 l1 ->
  t l1 ->
  t l2 ->
    l1 = l2.
Proof.
  intros Hincl1 Hincl2 Hsort1.
  revert l2 Hincl1 Hincl2.

  induction l1 as [| (i, x) l1 IH ]; intros l2 Hincl1 Hincl2 Hsort2.
  { symmetry. now apply incl_l_nil. }

  destruct l2 as [| (j, y) l2 ].
  { now apply incl_l_nil in Hincl1. }

  f_equal.
  { now apply equivalence_head with (l1 := l1) (l2 := l2). }

  assert ((i, x) = (j, y)) as H.
  { now apply equivalence_head with (l1 := l1) (l2 := l2). }
  inversion H; subst.

  apply IH.
  - now apply cons in Hsort1.
  - now apply incl_cons_same_elt with (i := j) (x := y).
  - now apply incl_cons_same_elt with (i := j) (x := y).
  - now apply cons in Hsort2.
Qed.
