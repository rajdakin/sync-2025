Set Default Goal Selector "!".

From Stdlib Require Import List.

Import ListNotations.


Lemma incl_trans {A} (l1 l2 l3: list A):
  incl l1 l2 -> incl l2 l3 -> incl l1 l3.
Proof.
  unfold incl.
  intros in12 in23 a ain1.
  apply in23.
  apply in12.
  assumption.
Qed.

Lemma incl_trans_app_l {A} (l1 l2 l2' l3: list A):
  incl l1 (l2 ++ l3) -> incl l2 l2' -> incl l1 (l2' ++ l3).
Proof.
  unfold incl.
  intros intmp in22' a inapp.
  specialize (intmp a).
  specialize (in22' a).
  apply intmp in inapp.
  clear intmp.
  apply in_app_iff.
  apply in_app_iff in inapp.
  destruct inapp as [ina2 | ina3].
  all: tauto.
Qed.

Lemma incl_trans_app_r {A} (l1 l2 l3 l3': list A):
  incl l1 (l2 ++ l3) -> incl l3 l3' -> incl l1 (l2 ++ l3').
Proof.
  unfold incl.
  intros intmp in33' a inapp.
  specialize (intmp a).
  specialize (in33' a).
  apply intmp in inapp.
  clear intmp.
  apply in_app_iff.
  apply in_app_iff in inapp.
  destruct inapp as [ina2 | ina3].
  all: tauto.
Qed.

Lemma incl_app_swap {A} (l1 l2: list A):
  incl (l1 ++ l2) (l2 ++ l1).
Proof.
  intros x isin.
  apply in_or_app.
  apply in_app_or in isin.
  tauto.
Qed.

Lemma remove_notin {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a x: A) (l: list A):
  ~In x l -> ~In x (List.remove eq_dec a l).
Proof.
  intros notinl inremove.
  apply in_remove in inremove.
  apply notinl.
  tauto.
Qed.

Lemma remove_notinl {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a x: A) (l1 l2: list A):
  ~In x (l1 ++ l2) -> ~In x ((List.remove eq_dec a l1) ++ l2).
Proof.
  intros notinl inremove.
  apply notinl.
  apply in_or_app.
  rewrite in_app_iff in inremove.
  destruct inremove as [inremove|?].
  2: tauto.
  apply in_remove in inremove.
  tauto.
Qed.

Lemma remove_notinr {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a x: A) (l1 l2: list A):
  ~In x (l1 ++ l2) -> ~In x (l1 ++ (List.remove eq_dec a l2)).
Proof.
  intros notinl inremove.
  apply notinl.
  apply in_or_app.
  rewrite in_app_iff in inremove.
  destruct inremove as [?|inremove].
  1: tauto.
  apply in_remove in inremove.
  tauto.
Qed.

Lemma remove_map_notinl {A B} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a: A) (map_fn: A -> B) (x: B) (l1 l2: list A):
  ~In x (map map_fn (l1 ++ l2)) -> ~In x (map map_fn ((List.remove eq_dec a l1) ++ l2)).
Proof.
  do 2 rewrite map_app.
  intros notinl inremove.
  apply notinl.
  apply in_or_app.
  rewrite in_app_iff in inremove.
  destruct inremove as [inremove|?].
  2: tauto.
  rewrite in_map_iff in inremove.
  destruct inremove as [y [existing inremove]].
  apply in_remove in inremove.
  subst.
  left.
  apply in_map.
  tauto.
Qed.

Lemma remove_map_notinr {A B} (eq_dec: forall x y: A, {x = y} + {x <> y}) (a: A) (map_fn: A -> B) (x: B) (l1 l2: list A):
  ~In x (map map_fn (l1 ++ l2)) -> ~In x (map map_fn (l1 ++ (List.remove eq_dec a l2))).
Proof.
  do 2 rewrite map_app.
  intros notinl inremove.
  apply notinl.
  apply in_or_app.
  rewrite in_app_iff in inremove.
  destruct inremove as [?|inremove].
  1: tauto.
  rewrite in_map_iff in inremove.
  destruct inremove as [y [existing inremove]].
  apply in_remove in inremove.
  subst.
  right.
  apply in_map.
  tauto.
Qed.
