From Reactive Require Export Base.


Inductive t {A: Type}: list (A * list A) -> Prop :=
  | nil : t []
  | alone (x: A) (l: list (A * list A)):
      t l ->
      ~ In x (map fst l) ->
      t ((x, []) :: l)
  | append (x: A) (lx: list A) (l: list (A * list A)):
      t l ->
      ~ In x (map fst l) ->
      (Forall (fun y => exists ly: list A, In (y, ly) l) lx) ->
      t ((x, lx) :: l).


Lemma cons {A: Type} (l: list (A * list A)) (x: A * list A):
  t (x :: l) -> t l.
Proof.
  intros H.
  inversion H; subst.
  - assumption.
  - assumption.
Qed.

Lemma vars_no_dups {A: Type} (l: list (A * list A)) (x: A) (lx: list A):
  t ((x, lx) :: l) ->
  ~ In x (map fst l).
Proof.
  intros Hord Hin.
  inversion Hord; subst; auto.
Qed.

Lemma var_cons_in_right_side {A: Type} (x y: A) (lx: list A) (l: list (A * list A)):
  t ((x, lx) :: l) ->
  In y lx ->
  exists ly: list A, In (y, ly) l.
Proof.
  intros Hord Hin.
  inversion Hord; subst.
  - inversion Hin.
  - apply Forall_forall with (x := y) in H4; assumption.
Qed.

Lemma var_in_right_side {A: Type} (x y: A) (lx: list A) (l: list (A * list A)):
  t l ->
  In (x, lx) l ->
  In y lx ->
  exists ly: list A, In (y, ly) l.
Proof.
  intros Hord Hx Hy.
  induction l as [ | (z, lz) l IH ]; [ inversion Hx | ].
  destruct Hx as [ Heq | Hx ].
  - inversion Heq.
    subst.
    apply var_cons_in_right_side with (y := y) in Hord; [ | assumption].
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

Lemma vars_coherence {A: Type} (l: list (A * list A)) (x y: A) (lx ly: list A):
  t ((x, lx) :: l) ->
  In (y, ly) l ->
  ~ In x ly.
Proof.
  intros Hord Hin Hnin.
  apply cons in Hord as Hord_inner.
  pose proof (var_in_right_side _ _ _ _ Hord_inner Hin Hnin) as [ lz Hlz ].
  apply vars_no_dups in Hord.
  apply Hord.
  apply in_map with (f := fst) in Hlz.
  assumption.
Qed.

Lemma var_not_need_itself {A: Type} (x: A) (lx: list A) (l: list (A * list A)):
  t ((x, lx) :: l) ->
  ~ In x lx.
Proof.
  intros Hord Hin.
  pose proof (var_cons_in_right_side _ _ _ _ Hord Hin) as [ ly Hly ].
  apply vars_no_dups in Hord.
  apply Hord.
  apply in_map with (f := fst) in Hly.
  assumption.
Qed.
