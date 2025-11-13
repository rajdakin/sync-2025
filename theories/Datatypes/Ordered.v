Set Default Goal Selector "!".

From Stdlib Require Import List.

Import ListNotations.


Inductive t {A B: Type}: list ((A * B) * list (A * B)) -> Prop :=
  | nil : t []
  | append (x: A) (y : B) (lx: list (A * B)) (l: list ((A * B) * list (A * B))):
      t l ->
      ~ In x (map (fun '(y, _, _) => y) l) ->
      (Forall (fun y => exists (ly: list (A * B)), In (y, ly) l) lx) ->
      t ((x, y, lx) :: l).


Lemma cons {A B: Type} (l: list ((A * B) * list (A * B))) (x: (A * B) * list (A * B)):
  t (x :: l) -> t l.
Proof.
  intros H.
  inversion H; subst.
  assumption.
Qed.

Lemma vars_no_dups {A B: Type} (l: list ((A * B) * list (A * B))) (x: A) (y: B) (lx: list (A * B)):
  t (((x, y), lx) :: l) ->
  ~ In x (map (fun '(y, _, _) => y) l).
Proof.
  intros Hord Hin.
  inversion Hord; subst; auto.
Qed.

Lemma var_cons_in_right_side {A B: Type} (x y: A) (a b: B) (lx: list (A * B)) (l: list ((A * B) * list (A * B))):
  t (((x, a), lx) :: l) ->
  In (y, b) lx ->
  exists ly: list (A * B), In ((y, b), ly) l.
Proof.
  intros Hord Hin.
  inversion Hord.
  subst.
  apply Forall_forall with (x := (y, b)) in H5; assumption.
Qed.

Lemma var_in_right_side {A B: Type} (x y: A) (a b: B) (lx: list (A * B)) (l: list ((A * B) * list (A * B))):
  t l ->
  In ((x, a), lx) l ->
  In (y, b) lx ->
  exists ly: list (A * B), In ((y, b), ly) l.
Proof.
  intros Hord Hx Hy.
  induction l as [ | (z, lz) l IH ]; [ inversion Hx | ].
  destruct Hx as [ Heq | Hx ].
  - inversion Heq.
    subst.
    apply var_cons_in_right_side with (y := y) (b := b) in Hord; [ | assumption].
    destruct Hord as [ ly Hly ].
    exists ly.
    right.
    assumption.
  - apply cons in Hord.
    specialize (IH Hord Hx) as [ ly Hly ].
    exists ly.
    right.
    assumption.
Qed.

Lemma vars_coherence {A B: Type} (xa ya: A) (xb yb: B) (xl yl: list (A * B)) (l: list ((A * B) * list (A * B))):
  t (((xa, xb), xl) :: l) ->
  In ((ya, yb), yl) l ->
  forall b: B, ~ In (xa, b) yl.
Proof.
  intros Hord Hin b Hnin.
  apply cons in Hord as Hord_inner.
  pose proof (var_in_right_side _ _ _ _ _ _ Hord_inner Hin Hnin) as [ lz Hlz ].
  apply vars_no_dups in Hord.
  apply Hord.
  apply in_map with (f := fun '(y, _, _) => y) in Hlz.
  assumption.
Qed.

Lemma var_not_need_itself {A B: Type} (x: A) (y: B) (lx: list (A * B)) (l: list ((A * B) * list (A * B))):
  t (((x, y), lx) :: l) ->
  forall b, ~ In (x, b) lx.
Proof.
  intros Hord b Hin.
  pose proof (var_cons_in_right_side _ _ _ _ _ _ Hord Hin) as [ ly Hly ].
  apply vars_no_dups in Hord.
  apply Hord.
  apply in_map with (f := fun '(y, _, _) => y) in Hly.
  assumption.
Qed.

Lemma app_right_side_l {A B: Type} (l: list ((A * B) * list (A * B))) (x: A) (y: B) (lx1 lx2: list (A * B)):
  t (((x, y), lx1 ++ lx2) :: l) ->
  t (((x, y), lx1) :: l).
Proof.
  intros Hord.
  revert lx1 lx2 Hord.
  induction l as [ | (x', ly) l IH ]; intros lx1 lx2 Hord.
  - constructor.
    + apply cons in Hord.
      assumption.
    + inversion 1.
    + inversion Hord.
      subst.
      apply incl_Forall with (l2 := lx1) in H5; [ assumption | ].
      apply incl_appl.
      apply incl_refl.
  - inversion Hord.
    subst.
    constructor; [ assumption.. | ].
    apply incl_Forall with (l1 := lx1 ++ lx2); [ | assumption ].
    apply incl_appl.
    apply incl_refl.
Qed.

Lemma app_right_side_r {A B: Type} (l: list ((A * B) * list (A * B))) (x: A) (y: B) (lx1 lx2: list (A * B)):
  t (((x, y), lx1 ++ lx2) :: l) ->
  t (((x, y), lx2) :: l).
Proof.
  intros Hord.
  revert lx1 lx2 Hord.
  induction l as [ | (x', ly) l IH ]; intros lx1 lx2 Hord.
  - constructor.
    + apply cons in Hord.
      assumption.
    + inversion 1.
    + inversion Hord.
      subst.
      apply incl_Forall with (l2 := lx2) in H5; [ assumption | ].
      apply incl_appr.
      apply incl_refl.
  - inversion Hord; subst.
    constructor; [ assumption.. | ].
    apply incl_Forall with (l1 := lx1 ++ lx2); [ | assumption ].
    apply incl_appr.
    apply incl_refl.
Qed.
