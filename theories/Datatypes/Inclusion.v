From Reactive Require Import Base.

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

Lemma In_app_inv {A} (x: A) (l1 l2: list A):
  In x (l1 ++ l2) -> In x (l2 ++ l1).
Proof.
  intro isin.
  apply in_or_app.
  apply in_app_or in isin.
  destruct isin.
  all: tauto.
Qed.