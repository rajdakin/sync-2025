From Reactive Require Import Base.

Inductive Sublist {A: Type} : list A -> list A -> Prop :=
  | Sublist_nil : forall (l : list A), Sublist [] l
  | Sublist_tl : forall (x: A) (l1 l2 : list A), Sublist l1 l2 -> Sublist l1 (x::l2)
  | Sublist_hd : forall (x : A) (l1 l2 : list A), Sublist l1 l2 -> Sublist (x::l1) (x::l2)
.

Lemma sublist_nil {A} (l: list A):
  Sublist l [] <-> l = [].
Proof.
  split.
  - inversion 1.
    reflexivity.
  - intro.
    subst.
    constructor.
Qed.

Lemma sublist_refl {A} (l: list A):
  Sublist l l.
Proof.
  induction l.
  - constructor.
  - constructor 3.
    assumption.
Qed.

Lemma sublist_cons {A} (x: A) (l1 l2: list A):
  Sublist (x::l1) l2 -> Sublist l1 l2.
Proof.
  intros H.
  remember (x::l1) as l' eqn:eql'.
  generalize dependent l1; generalize dependent x; induction H as [l2|x l1 l2 H IH|x l1 l2 H IH]; intros x' l1' eql'.
  - discriminate eql'.
  - subst.
    specialize (IH _ _ eq_refl).
    constructor 2; assumption.
  - injection eql' as <- <-.
    constructor 2; assumption.
Qed.

Lemma sublist_trans {A} (l1 l2 l3: list A):
  Sublist l1 l2 -> Sublist l2 l3 -> Sublist l1 l3.
Proof.
  intros s13 s23.
  revert l1 s13.
  induction s23 as [ | x l2 l3 s23 IH | x l2 l3 s23 IH ].
  - intros l1 subnil.
    apply sublist_nil in subnil.
    subst.
    constructor.
  - intros.
    constructor 2.
    apply IH.
    assumption.
  - intros l1 s1x2.
    inversion s1x2; subst.
    + constructor.
    + constructor 2.
      apply IH.
      assumption.
    + constructor 3.
      apply IH.
      assumption.
Qed.

Lemma sublist_app_l {A} (l1 l2: list A):
  Sublist l1 (l1 ++ l2).
Proof.
  induction l1.
  - constructor 1.
  - simpl.
    constructor 3.
    assumption.
Qed.

Lemma sublist_app_r {A} (l1 l2: list A):
  Sublist l2 (l1 ++ l2).
Proof.
  induction l1.
  - apply sublist_refl.
  - simpl.
    constructor 2.
    assumption.
Qed.

Lemma sublist_app_l_gen {A} (l1 l2 l: list A):
  Sublist l1 l2 -> Sublist l1 (l2 ++ l).
Proof.
  intro s12.
  eapply sublist_trans.
  - apply s12.
  - apply sublist_app_l.
Qed.

Lemma sublist_app_r_gen {A} (l1 l2 l: list A):
  Sublist l1 l2 -> Sublist l1 (l ++ l2).
Proof.
  intro s12.
  eapply sublist_trans.
  - apply s12.
  - apply sublist_app_r.
Qed.

Lemma sublist_app_cons {A} (x: A) (l1 l2: list A):
  Sublist (l1 ++ l2) (l1 ++ x :: l2).
Proof.
  induction l1.
  - constructor 2.
    apply sublist_refl.
  - constructor 3.
    assumption.
Qed.

Lemma list_app_cons_rewrite {A} (x: A) (l1 l2: list A):
  l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
Proof.
  induction l1.
  - reflexivity.
  - simpl.
    f_equal.
    assumption.
Qed.

Lemma sublist_app {A} (l1 l2 l1' l2': list A):
  Sublist l1 l1' -> Sublist l2 l2' -> Sublist (l1 ++ l2) (l1' ++ l2').
Proof.
  intros s1 s2.
  induction s2 as [ | x l2 l2' s2 H | x l2 l2' s2 H ] in l1, l1', s1 |- *.
  - rewrite app_nil_r.
    apply sublist_app_l_gen.
    assumption.
  - eapply sublist_trans.
    + eapply H.
      apply s1.
    + apply sublist_app_cons.
  - rewrite (list_app_cons_rewrite x l1 l2).
    rewrite (list_app_cons_rewrite x l1' l2').
    apply H.
    clear -s1.
    induction s1.
    + apply sublist_app_r.
    + simpl.
      constructor 2.
      assumption.
    + simpl.
      constructor 3.
      assumption.
Qed.

Lemma sublist_incl {A} (l1 l2: list A):
  Sublist l1 l2 -> incl l1 l2.
Proof.
  intro sub.
  induction sub.
  - apply incl_nil_l.
  - apply incl_tl.
    assumption.
  - apply incl_cons.
    + apply in_eq.
    + apply incl_tl.
      assumption.
Qed.