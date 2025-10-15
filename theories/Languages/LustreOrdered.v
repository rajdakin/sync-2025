From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require Lustre.

Module Lustre := Lustre.


Definition dag := list ((ident * Lustre.type) * list (ident * Lustre.type)).

Fixpoint equations_to_dag (equations: list Lustre.equation): dag :=
  match equations with
    | [] => []
    | (name, existT _ ty exp) :: remaining_eqs => ((name, ty), Lustre.var_of_exp exp) :: equations_to_dag remaining_eqs
  end.

Record node_ordered := mk_node_ordered {
  node_ordered_is_node :> Lustre.node;
  ordered: Ordered.t (equations_to_dag (Lustre.n_body node_ordered_is_node));
}.

(** Lemmas *)

Lemma dag_names (equations: list Lustre.equation):
  map Lustre.equation_dest equations = map fst (equations_to_dag equations).
Proof.
  induction equations as [ | [ i [ ty s ] ] equations IH ].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma dag_length (equations: list Lustre.equation):
  List.length equations = List.length (equations_to_dag equations).
Proof.
  induction equations as [ | [ i [ ty s ] ] equations IH ].
  - simpl.
    reflexivity.
  - simpl.
    apply f_equal.
    assumption.
Qed.

Lemma dag_nil (equations: list Lustre.equation):
  equations = [] <-> equations_to_dag equations = [].
Proof.
  split.
  - intros eq.
    pose proof (@f_equal _ _ (@List.length Lustre.equation) _ _ eq) as H.
    simpl in H.
    rewrite dag_length in H.
    apply length_zero_iff_nil.
    assumption.
  - intros eq.
    pose proof (@f_equal _ _ (@List.length _) _ _ eq) as H.
    rewrite <- dag_length in H.
    apply length_zero_iff_nil.
    assumption.
Qed.

Lemma equations_to_dag_is_map (equations: list Lustre.equation):
  equations_to_dag equations = map (fun '(name, existT _ ty exp) => ((name, ty), Lustre.var_of_exp exp)) equations.
Proof.
  induction equations as [ | (name, (ty, exp)) l IH ]; [ reflexivity | ].
  simpl.
  f_equal.
  assumption.
Qed.

(** Minimal history for correctness proof *)

Lemma Forall_impl_in {A: Type} (P Q: A -> Prop) (l: list A):
  (forall a : A, In a l -> P a -> Q a) ->
  Forall P l -> Forall Q l.
Proof.
  intros H Hforall.
  induction l as [ | x l ]; [ constructor | ].
  constructor.
  - apply H.
    + left.
      reflexivity.
    + apply Forall_inv with (l := l).
      assumption.
  - apply IHl.
    + intros a Hin HPa.
      apply H; [ | assumption ].
      right.
      assumption.
    + apply Forall_inv_tail with (a := x).
      assumption.
Qed.

Lemma sem_exp_with_useless_var {tys tye} (e: Lustre.exp tye) (h: Lustre.history) (name: ident) (v: Lustre.value _) (s: Stream.t (Lustre.value tys)):
  Lustre.sem_exp h e v ->
  (forall tyv, ~ In (name, tyv) (Lustre.var_of_exp e)) ->
  Lustre.sem_exp (Dict.add name (existT _ _ s) h) e v.
Proof.
  intros Hexp Hnin.
  revert v Hexp.
  induction e as [ ty c | b | (i, t) | ty tout op e IH | ty1 ty2 tout op e1 IH1 e2 IH2 | ty e1 IH1 e2 IH2 e3 IH3 ]; intros v Hexp.
  - inversion Hexp.
    apply Lustre.sig2T_eq_type in H2, H3.
    subst.
    apply Lustre.SeConst.
  - inversion Hexp.
    apply Lustre.sig2T_eq_type in H4.
    subst.
    apply Lustre.SeInput.
  - inversion Hexp.
    apply Lustre.sig2T_eq_type in H4.
    subst.
    unfold Lustre.var_of_exp in Hnin.
    simpl in Hnin.
    destruct b as [j tyi]; injection H3 as H3; subst j.
    apply Lustre.SeVar.
    simpl.
    apply Dict.maps_to_add; [ assumption | ].
    intros Heq.
    exact (Hnin tyi (or_introl _ (f_equal2 _ Heq eq_refl))).
  - inversion Hexp.
    apply Lustre.sig2T_eq_type in H3, H4, H5.
    apply Lustre.sig2T_eq_type in H3.
    subst.
    apply Lustre.SeUnop.
    apply IH; assumption.
  - inversion Hexp.
    subst ty3.
    apply Lustre.sig2T_eq_type in H4, H5, H6, H7.
    repeat apply Lustre.sig2T_eq_type in H4.
    subst.
    pose proof (Lustre.var_of_exp_not_in_binop e1 e2 name op Hnin) as tmp.
    pose proof (fun tyv => proj1 (tmp tyv)).
    pose proof (fun tyv => proj2 (tmp tyv)).
    apply Lustre.SeBinop.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - inversion Hexp.
    apply Lustre.sig2T_eq_type in H0, H1, H4.
    subst.
    pose proof (Lustre.var_of_exp_not_in_ifte e1 e2 e3 name Hnin) as tmp.
    pose proof (fun tyv => proj1 (tmp tyv)).
    pose proof (fun tyv => proj1 (proj2 (tmp tyv))).
    pose proof (fun tyv => proj2 (proj2 (tmp tyv))).
    apply Lustre.SeIfte.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

Lemma var_of_last_exp_in_body {ty} (body: list Lustre.equation) (name: ident) (exp: Lustre.exp ty):
  Ordered.t (equations_to_dag ((name, existT Lustre.exp _ exp) :: body)) ->
  Forall (fun v => In v (map Lustre.equation_dest body)) (Lustre.var_of_exp exp).
Proof.
  induction exp as [ ty c | b | (i, ty) | ty tout op e IH | ty1 ty2 tout op e1 IH1 e2 IH2 | ty e1 IH1 e2 IH2 e3 IH3 ]; intros Hord.
  - constructor.
  - constructor.
  - constructor; [ | constructor ].
    simpl in Hord.
    apply Ordered.var_cons_in_right_side with (y := i) (b := ty) in Hord.
    + destruct Hord as [ ly Hly ].
      apply in_map with (f := fst) in Hly.
      rewrite <- dag_names in Hly.
      assumption.
    + left.
      reflexivity.
  - apply IH.
    inversion Hord as [ | x lx l Hord' Hnin H ]; subst.
    constructor; assumption.
  - simpl in Hord.
    rewrite Lustre.var_of_exp_binop_eq in Hord |- *.
    apply Forall_app.
    split.
    + apply IH1.
      apply Ordered.app_right_side_l in Hord.
      inversion Hord; constructor; assumption.
    + apply IH2.
      apply Ordered.app_right_side_r in Hord.
      inversion Hord; constructor; assumption.
  - simpl in Hord.
    rewrite Lustre.var_of_exp_ifte_eq in Hord |- *.
    apply Forall_app.
    split.
    + apply Ordered.app_right_side_l in Hord.
      apply IH1.
      inversion Hord; constructor; assumption.
    + apply Ordered.app_right_side_r in Hord.
      apply Forall_app.
      split.
      * apply IH2.
        apply Ordered.app_right_side_l in Hord.
        assumption.
      * apply IH3.
        apply Ordered.app_right_side_r in Hord.
        assumption.
Qed.

Lemma minimal_history (body: list Lustre.equation):
  Ordered.t (equations_to_dag body) ->
  exists (h: Lustre.history),
    (forall (i: ident) ty, Lustre.in_history h (i, ty) <-> In (i, ty) (map Lustre.equation_dest body)) /\
    (Forall (fun '(n, existT _ ty eq) =>
      exists (v': Stream.t (Lustre.value ty)),
      Dict.maps_to n (existT _ ty v') h /\ Lustre.sem_exp h eq (Stream.hd v')
    ) body).
Proof.
  intros Hord.
  induction body as [ | (name, (ty, exp)) body IH ].
  - exists (Dict.empty _).
    split; [ | constructor ].
    intros i.
    split.
    2: { inversion 1. }
    intros Hi.
    inversion Hi.
  - specialize (IH (Ordered.cons _ _ Hord)) as ( h & IH1 & IH2 ).

    assert (Forall (Lustre.in_history h) (Lustre.var_of_exp exp)) as Hforall.
    { apply Forall_impl with (P := fun v => In v (map Lustre.equation_dest body)).
      - intros [ i tyv ]; apply IH1.
      - apply var_of_last_exp_in_body with (name := name).
        assumption. }

    pose proof (Lustre.exp_with_evaluable_vars_is_evaluable h exp Hforall) as [ v Hv ].
    
    exists (Dict.add name (existT _ _ (Stream.from v)) h).
    split.
    + intros i.
      split.
      * rewrite Lustre.in_history_iff.
        intros [ x Hx ].
        destruct (PeanoNat.Nat.eq_dec i name).
        { left.
          unfold Lustre.equation_dest; cbn; f_equal.
          1: symmetry; assumption.
          subst.
          match goal with Hx : Dict.find _ (Dict.add ?i ?v ?d) = _ |- _ =>
          rewrite (Dict.maps_to_last_added i v d) in Hx end.
          injection Hx as Hty _.
          assumption. }
        apply Dict.maps_to_not_last_added in Hx; [ | assumption ].
        right.
        apply IH1.
        apply Lustre.in_history_iff.
        exists x.
        assumption.
      * rewrite Lustre.in_history_iff.
        intros [ Heq | Hin ].
        { injection Heq as H1 H2.
          subst.
          exists (Stream.from v).
          simpl.
          apply Dict.maps_to_last_added. }

        assert (i <> name).
        { intros ieq; inversion Hord as [ | x y lx l H1 H2 H3 ]; subst.
          rewrite equations_to_dag_is_map in H2.
          apply H2.
          apply in_map with (f := fst) in Hin.
          refine (eq_ind _ _ Hin _ _).
          clear.
          induction body as [ | (y & ty & l) body IH ]; [ reflexivity | ].
          exact (f_equal _ IH). }

        apply IH1, Lustre.in_history_iff in Hin as [ x Hx ].
        exists x.
        apply Dict.maps_to_add; assumption.

    + constructor.
      * exists (Stream.from v).
        split.
        { apply Dict.maps_to_last_added. }
        apply Lustre.sem_eval_exp.
        simpl.
        apply Lustre.sem_eval_exp.
        apply sem_exp_with_useless_var.
        2: now apply Ordered.var_not_need_itself with (y := ty) (l := equations_to_dag body).
        now apply Lustre.sem_eval_exp.
      * refine (Forall_impl_in _ _ _ _ IH2).
        intros (i, (tyi, x)) Hin ( s & Hs1 & Hs2 ).
        simpl in *.
        
        destruct (PeanoNat.Nat.eq_dec i name).
        { exfalso.
          subst.
          specialize (IH1 name).
          assert (Lustre.in_history h (name, tyi)) as H.
          { unfold Lustre.in_history. rewrite Hs1. reflexivity. }
          apply IH1 in H.
          apply Ordered.vars_no_dups in Hord.
          rewrite dag_names in H.
          apply Hord; clear - H.
          induction body as [ | [ ? [ ? ? ] ] ? IH ]; [ contradiction H | ].
          destruct H as [ H | H ]; [ left; injection H as ? ?; assumption | right; apply IH; assumption ]. }
        
        exists s.
        split.
        { now apply Dict.maps_to_add. }

        apply sem_exp_with_useless_var; [ assumption | ].
        refine (Ordered.vars_coherence _ i _ tyi _ (Lustre.var_of_exp x) _ Hord _).
        apply in_map with (f := fun '(i, existT _ ty x) => ((i, ty), Lustre.var_of_exp x)) in Hin.
        rewrite equations_to_dag_is_map.
        assumption.
Qed.
