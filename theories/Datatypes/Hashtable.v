Parameter raw : Type -> Type -> Type.
Parameter raw_create : forall A B, nat -> raw A B.
Parameter raw_add : forall {A B}, raw A B -> A -> B -> raw A B.
Axiom raw_In : forall {A B}, raw A B -> A -> Prop.
Parameter raw_find : forall {A B} (m : raw A B) (x : A), raw_In m x -> B.
Parameter raw_find_opt : forall {A B} (m : raw A B) (x : A), option B.

Axiom raw_In_create : forall {A B} [n x], ~ raw_In (raw_create A B n) x.
Axiom raw_In_add_pre : forall {A B} [m : raw A B] [z] [x y], raw_In m z -> raw_In (raw_add m x y) z.
Axiom raw_In_add_same : forall {A B} (m : raw A B) x y, raw_In (raw_add m x y) x.
Axiom raw_In_add_inv : forall {A B} [m : raw A B] [x y z], raw_In (raw_add m x y) z -> z = x \/ raw_In m z.

Axiom raw_find_add : forall {A B} [m : raw A B] [x y] H, raw_find (raw_add m x y) x H = y.
Axiom raw_find_ne : forall {A B} [m : raw A B] [x y z] H1 H2, z <> x -> raw_find (raw_add m x y) z H1 = raw_find m z H2.
Axiom raw_find_ext : forall {A B} (m : raw A B) x H1 H2, raw_find m x H1 = raw_find m x H2.
Axiom raw_find_opt_iff : forall {A B} (m : raw A B) x,
  match raw_find_opt m x with
  | None => ~ raw_In m x
  | Some y => exists H : raw_In m x, raw_find m x H = y
  end.

From Stdlib Require Import List.

Parameter t : Type -> Type -> Type.
Definition t' (A B : Type) := { ml : raw A B * list (A * B) |
  NoDup (map fst (snd ml)) /\
  exists h : forall x, raw_In (fst ml) x <-> In x (map fst (snd ml)),
  forall x y (Hx : In (x, y) (snd ml)), raw_find (fst ml) x (proj2 (h x) (in_map _ _ _ Hx)) = y }.
Axiom t_def : t = t'.
Definition t_def' A B : t A B = _ := eq_ind_r (fun t => t A B = _) eq_refl t_def.
Definition unfold_t {A B} (m : t A B) := eq_rect _ id m _ (t_def' _ _).
Definition fold_t {A B} m : t A B := eq_rect _ id m _ (eq_sym (t_def' _ _)).
Lemma fold_unfold_id : forall {A B} m, @fold_t A B (unfold_t m) = m.
Proof using.
  intros A B m; unfold fold_t, unfold_t, eq_rect, eq_sym.
  destruct (t_def' A B); exact eq_refl.
Qed.
Lemma unfold_fold_id : forall {A B} m, @unfold_t A B (fold_t m) = m.
Proof using.
  intros A B m; unfold fold_t, unfold_t, eq_rect, eq_sym.
  destruct (t_def' A B); exact eq_refl.
Qed.

Definition InMap' {A B : Type} (x : A) (ml : t' A B) := In x (map fst (snd (proj1_sig ml))).
Definition InMap {A B : Type} (x : A) (ml : t A B) := InMap' x (unfold_t ml).

Definition create (A B : Type) (n : nat) : t A B.
Proof using.
  apply fold_t.
  exists (raw_create A B n, nil).
  split.
  1: exact (NoDup_nil _).
  exists (fun z => conj (fun f => False_ind _ (raw_In_create f)) (False_ind _)).
  intros x y Hx; contradiction Hx.
Defined.

Definition add {A B : Type} (ml : t A B) (x : A) (y : B) (H : ~ InMap x ml) : t A B.
Proof using.
  apply fold_t; unfold id.
  unfold InMap in H.
  destruct (unfold_t ml) as [[m l] [H1 H2]] eqn:eqml; clear ml eqml.
  exists (raw_add m x y, (x, y) :: l).
  destruct H2 as [H2 H3].
  unfold proj1_sig, fst, snd in H1, H2, H |- *; fold (@fst A B) in *; split.
  1: constructor; assumption.
  unshelve eexists.
  1: intros z; split; intros Hz.
  1:  destruct (raw_In_add_inv Hz) as [zx|h].
  1:   left; exact (eq_sym zx).
  1:  right; exact (proj1 (H2 _) h).
  1: cbn in Hz; destruct Hz as [->|Hz].
  1:  exact (raw_In_add_same _ _ _).
  1: apply raw_In_add_pre, H2; exact Hz.
  cbn.
  intros z w [Hzw|Hzw].
  1: injection Hzw as <- <-; exact (raw_find_add _).
  refine (eq_trans (raw_find_ne _ _ _) (H3 _ _ Hzw)).
  intros ->; exact (H (in_map _ _ _ Hzw)).
Defined.

Definition find {A B : Type} (ml : t A B) (x : A) (H : InMap x ml) : B :=
  raw_find (fst (proj1_sig (unfold_t ml))) x
    (match unfold_t ml as p return InMap' x p -> raw_In (fst (proj1_sig p)) x with exist _ ml (conj _ (ex_intro _ H2 _)) => proj2 (H2 _) end H).

Lemma In_create : forall {A B} [n x], ~ InMap x (create A B n).
Proof using.
  unfold InMap, create, proj1_sig, snd; intros A B n x f.
  rewrite unfold_fold_id in f.
  exact f.
Qed.

Lemma In_add_pre : forall {A B} [m : t A B] [z] [x y] H, InMap z m -> InMap z (add m x y H).
Proof using.
  unfold InMap, add, proj1_sig, snd; intros A B ml.
  destruct (unfold_t ml) as [[m l] [H1 H2]]; clear ml; unfold fst, snd in H2.
  intros ? ? ? ?; rewrite unfold_fold_id; right; assumption.
Qed.

Lemma In_add_same : forall {A B} (m : t A B) x y H, InMap x (add m x y H).
Proof using.
  unfold InMap, add, proj1_sig, snd; intros A B ml; destruct (unfold_t ml) as [[m l] [H1 H2]]; clear ml; unfold fst, snd in H2.
  intros ? ? ?; rewrite unfold_fold_id; left; exact eq_refl.
Qed.

Lemma In_add_inv : forall {A B} [m : t A B] [x y z] H, InMap z (add m x y H) -> z = x \/ InMap z m.
Proof using.
  unfold InMap, add, proj1_sig, snd; intros A B ml x y z H h; destruct (unfold_t ml) as [[m l] [H1 [H2 H3]]]; clear ml; unfold fst, snd in H2.
  rewrite unfold_fold_id in h; cbn in h; clear y H.
  destruct h; [left; symmetry|right]; assumption.
Qed.

Lemma find_ext : forall {A B} (m : t A B) x H1 H2, find m x H1 = find m x H2.
Proof using.
  intros A B ml x H1 H2.
  exact (raw_find_ext _ _ _ _).
Qed.

Lemma find_add : forall {A B} [m : t A B] [x y] H1 H2, find (add m x y H1) x H2 = y.
Proof using.
  intros A B ml x y H1 H2.
  revert H2; unfold InMap, find, add in *; cbn; rewrite unfold_fold_id.
  destruct (unfold_t ml) as [[m l] [H3 [H4 H5]]]; cbn in *; intros H2.
  exact (raw_find_add _).
Qed.

Lemma find_ne : forall {A B} [m : t A B] [x y z] H1 H2 H3, find (add m x y H1) z H2 = find m z H3.
Proof using.
  intros A B ml x y z H1 H2 H3.
  revert H2 H3; unfold InMap, InMap', find, add in *; cbn; rewrite unfold_fold_id.
  destruct (unfold_t ml) as [[m l] [H4 [H5 H6]]]; cbn in *; intros H2 H3.
  refine (raw_find_ne _ _ _).
  intros ->; exact (H1 H3).
Qed.

Lemma find_ne' : forall {A B} [m : t A B] [x y z] H1 H2 (H3 : z <> x),
  find (add m x y H1) z H2 = find m z (or_ind (fun h => False_ind _ (H3 h)) id (In_add_inv _ H2)).
Proof using.
  intros A B ml x y z H1 H2 H3.
  exact (find_ne _ _ _).
Qed.

Definition find_opt {A B : Type} (ml : t A B) (x : A) : option B := raw_find_opt (fst (proj1_sig (unfold_t ml))) x.

Lemma find_opt_iff : forall {A B} (m : t A B) x,
  match find_opt m x with
  | None => ~ InMap x m
  | Some y => exists H, find m x H = y
  end.
Proof using.
  intros A B ml x; unfold find_opt, find, InMap; destruct (unfold_t ml) as [[m l] [H1 [H2 H3]]]; cbn in *.
  specialize (raw_find_opt_iff m x) as tmp.
  destruct (raw_find_opt m x) as [y|]; [destruct tmp as [Hin Hrf]|].
  1: refine (ex_intro _ _ (eq_trans (raw_find_ext _ _ _ _) Hrf)).
  1: apply H2; exact Hin.
  intros f; apply H2 in f; exact (tmp f).
Qed.

Lemma find_opt_In {A B} (m : t A B) x H : find_opt m x = Some (find m x H).
Proof using.
  specialize (find_opt_iff m x); destruct (find_opt m x) as [y|].
  2: intros f; contradiction (f H).
  intros [H2 <-]; exact (f_equal Some (find_ext _ _ _ _)).
Qed.

Lemma find_opt_Some {A B} (m : t A B) x y : find_opt m x = Some y -> exists H, find m x H = y.
Proof using.
  intros Heq; specialize (find_opt_iff m x); rewrite Heq; tauto.
Qed.

Lemma find_opt_Some_In {A B} (m : t A B) x y : find_opt m x = Some y -> InMap x m.
Proof using.
  intros Heq; apply find_opt_Some in Heq; destruct Heq as [H _]; exact H.
Qed.
Lemma find_opt_Some_eq {A B} (m : t A B) x y H : find m x (find_opt_Some_In m x y H) = y.
Proof using.
  apply find_opt_Some in H as Heq; destruct Heq as [H1 H2]; exact (eq_trans (find_ext _ _ _ _) H2).
Qed.

Lemma find_opt_None {A B} (m : t A B) x : find_opt m x = None <-> ~ InMap x m.
Proof using.
  specialize (find_opt_iff m x); destruct (find_opt m x); [intros [H <-]; split; [discriminate 1|tauto]|tauto].
Qed.

(* Doesn't seem useful due to the eq_refl *)
Lemma find_opt_iff' : forall {A B} (m : t A B) x,
  match find_opt m x as v return find_opt m x = v -> _ with
  | None => fun e => ~ InMap x m
  | Some y => fun e => find m x (find_opt_Some_In _ _ _ e) = y
  end eq_refl.
Proof using.
  intros A B m x.
  remember (eq_refl (find_opt m x)) as Heq eqn:eqHeq.
  pose (oy := find_opt m x).
  pose (tmp := Heq : find_opt m x = oy).
  refine (_ : match oy as v return find_opt m x = v -> _ with Some y => _ | None => _ end tmp).
  generalize dependent tmp; generalize dependent oy; clear Heq eqHeq.
  intros [y|]; [exact (find_opt_Some_eq _ _ _)|exact (proj1 (find_opt_None _ _))].
Qed.
