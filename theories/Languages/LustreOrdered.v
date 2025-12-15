Set Default Goal Selector "!".

From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require Lustre.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Identifier.

From Stdlib Require Import List.

Import ListNotations.

Module Lustre := Lustre.

Definition value := Lustre.value.
Definition unop := Lustre.unop.
Definition binop := Lustre.binop.
Definition exp := Lustre.exp.
Definition var_of_exp := @Lustre.var_of_exp.
Arguments var_of_exp {_} _.
Definition equation := Lustre.equation.
Definition equation_dest := Lustre.equation_dest.
Definition node := Lustre.node.
Definition history := Lustre.history.
Definition in_history := Lustre.in_history.
Definition in_history_iff := Lustre.in_history_iff.
Definition var_of_exp_binop_eq := @Lustre.var_of_exp_binop_eq.
Arguments var_of_exp_binop_eq {_ _ _} _ _ _.
Definition var_of_exp_ifte_eq := @Lustre.var_of_exp_ifte_eq.
Arguments var_of_exp_ifte_eq {_} _ _ _.
Definition var_of_exp_not_in_binop := @Lustre.var_of_exp_not_in_binop.
Arguments var_of_exp_not_in_binop _ {_ _ _} _ _ _ _ _.
Definition var_of_exp_not_in_ifte := @Lustre.var_of_exp_not_in_ifte.
Arguments var_of_exp_not_in_ifte _ {_} _ _ _ _ _.

Definition dag := list ((ident * type) * list (ident * type)).

Fixpoint equations_to_dag_aux (equations: list equation): dag :=
  match equations with
    | [] => []
    | (name, existT _ ty exp) :: remaining_eqs => ((name, ty), var_of_exp exp) :: equations_to_dag_aux remaining_eqs
  end.
Definition equations_to_dag equations n_in: dag := equations_to_dag_aux equations ++ List.map (fun ity => (ity, [])) n_in.

Record node_ordered := mk_node_ordered {
  node_ordered_is_node :> node;
  ordered: Ordered.t (equations_to_dag (Lustre.n_body node_ordered_is_node) (Lustre.n_in node_ordered_is_node));
}.

(** Lemmas *)

Lemma dag_names (equations: list equation):
  map equation_dest equations = map fst (equations_to_dag_aux equations).
Proof.
  induction equations as [ | [ i [ ty s ] ] equations IH ].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma dag_length (equations: list equation):
  List.length equations = List.length (equations_to_dag_aux equations).
Proof.
  induction equations as [ | [ i [ ty s ] ] equations IH ].
  - simpl.
    reflexivity.
  - simpl.
    apply f_equal.
    assumption.
Qed.

Lemma dag_nil (equations: list equation):
  equations = [] <-> equations_to_dag_aux equations = [].
Proof.
  split.
  - intros eq.
    pose proof (@f_equal _ _ (@List.length equation) _ _ eq) as H.
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

Lemma equations_to_dag_is_map (equations: list equation):
  equations_to_dag_aux equations = map (fun '(name, existT _ ty exp) => ((name, ty), var_of_exp exp)) equations.
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

Lemma sem_exp_with_useless_var {tys tye} (e: exp tye) (h: history) (name: ident) (v: value _) (s: Stream.t (value tys)):
  Lustre.sem_exp h e v ->
  (forall tyv, ~ In (name, tyv) (var_of_exp e)) ->
  Lustre.sem_exp (Dict.add name (existT _ _ s) h) e v.
Proof.
  intros Hexp Hnin.
  revert v Hexp.
  induction e as [ loc ty c | loc (i, t) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros v Hexp.
  - inversion Hexp.
    simpl_exist_type.
    subst.
    apply Lustre.SeConst.
  - inversion Hexp.
    simpl_exist_type.
    subst.
    unfold var_of_exp in Hnin.
    simpl in Hnin.
    destruct b as [j tyi]; injection H4 as H4; subst j.
    apply Lustre.SeVar.
    simpl.
    apply Dict.maps_to_add; [ assumption | ].
    intros Heq.
    exact (Hnin tyi (or_introl _ (f_equal2 _ Heq eq_refl))).
  - inversion Hexp.
    simpl_exist_type.
    subst.
    apply Lustre.SeUnop.
    apply IH; assumption.
  - inversion Hexp.
    subst ty3.
    simpl_exist_type.
    subst.
    pose proof (var_of_exp_not_in_binop _ e1 e2 name op Hnin) as tmp.
    pose proof (fun tyv => proj1 (tmp tyv)).
    pose proof (fun tyv => proj2 (tmp tyv)).
    apply Lustre.SeBinop.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - inversion Hexp.
    simpl_exist_type.
    subst.
    pose proof (var_of_exp_not_in_ifte _ e1 e2 e3 name Hnin) as tmp.
    pose proof (fun tyv => proj1 (tmp tyv)).
    pose proof (fun tyv => proj1 (proj2 (tmp tyv))).
    pose proof (fun tyv => proj2 (proj2 (tmp tyv))).
    apply Lustre.SeIfte.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

Lemma var_of_last_exp_in_body {ty} (body: list equation) (name: ident) (e: exp ty) n_in:
  Ordered.t (equations_to_dag ((name, existT exp _ e) :: body) n_in) ->
  Forall (fun v => In v (map equation_dest body) \/ In v n_in) (var_of_exp e).
Proof.
  induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros Hord.
  - constructor.
  - constructor; [ | constructor ].
    simpl in Hord.
    cbn in Hord.
    apply Ordered.var_cons_in_right_side with (y := i) (b := ty) in Hord.
    + destruct Hord as [ ly Hly ].
      apply in_map with (f := fst) in Hly.
      rewrite map_app, map_map, map_id in Hly.
      rewrite <- dag_names in Hly.
      apply in_app_or in Hly.
      assumption.
    + left.
      reflexivity.
  - apply IH.
    inversion Hord as [ | x lx l Hord' Hnin H ]; subst.
    constructor; assumption.
  - unfold equations_to_dag in Hord.
    simpl in Hord.
    rewrite var_of_exp_binop_eq in Hord |- *.
    apply Forall_app.
    split.
    + apply IH1.
      apply Ordered.app_right_side_l in Hord.
      inversion Hord; constructor; assumption.
    + apply IH2.
      apply Ordered.app_right_side_r in Hord.
      inversion Hord; constructor; assumption.
  - unfold equations_to_dag in Hord.
    simpl in Hord.
    rewrite var_of_exp_ifte_eq in Hord |- *.
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

Lemma minimal_history (body: list equation) n_in h0:
  (forall (i: ident) ty, in_history h0 (i, ty) <-> In (i, ty) n_in) ->
  Ordered.t (equations_to_dag body n_in) ->
  exists (h: history),
    Dict.inclusion h0 h /\
    (forall (i: ident) ty, in_history h (i, ty) <-> In (i, ty) (map equation_dest body ++ n_in)) /\
    (Forall (fun '(n, existT _ ty eq) =>
      exists (v': Stream.t (value ty)),
      Dict.maps_to n (existT _ ty v') h /\ Lustre.sem_exp h eq (Stream.hd v')
    ) body).
Proof.
  intros Hhist0 Hord.
  induction body as [ | (name, (ty, exp)) body IH ].
  - exists h0.
    split; [ intros ? ? h; exact h | split; [ | constructor ] ].
    unfold equations_to_dag, equations_to_dag_aux, app in Hord.
    intros i ty.
    exact (Hhist0 i ty).
  - specialize (IH (Ordered.cons _ _ Hord)) as ( h & IH1 & IH2 & IH3 ).

    assert (Forall (in_history h) (var_of_exp exp)) as Hforall.
    { apply Forall_impl with (P := fun v => In v (map equation_dest body ++ n_in)).
      - intros [ i tyv ]; apply IH2.
      - refine (Forall_impl _ (fun v => in_or_app _ _ _) _).
        apply var_of_last_exp_in_body with (name := name).
        assumption. }

    pose proof (Lustre.exp_with_evaluable_vars_is_evaluable h exp Hforall) as [ v Hv ].
    
    exists (Dict.add name (existT _ _ (Stream.from v)) h).
    split; [|split].
    + intros i [ty' e] H.
      refine (Dict.maps_to_add _ _ _ _ _ (IH1 _ _ H) _).
      intros <-.
      cbn in Hord; refine (Ordered.vars_no_dups _ _ _ _ Hord _).
      rewrite map_app, map_map.
      refine (in_or_app _ _ _ (or_intror (in_map _ _ (_, _) (proj1 (Hhist0 i ty') _)))).
      unfold in_history, Lustre.in_history.
      rewrite H; exact eq_refl.
    + intros i.
      split.
      * rewrite in_history_iff.
        intros [ x Hx ].
        destruct (PeanoNat.Nat.eq_dec i name).
        { left.
          unfold equation_dest, Lustre.equation_dest; cbn; f_equal.
          1: symmetry; assumption.
          subst.
          match goal with Hx : Dict.find _ (Dict.add ?i ?v ?d) = _ |- _ =>
          rewrite (Dict.maps_to_last_added i v d) in Hx end.
          injection Hx as Hty _.
          assumption. }
        apply Dict.maps_to_not_last_added in Hx; [ | assumption ].
        right.
        apply IH2.
        apply in_history_iff.
        exists x.
        assumption.
      * rewrite in_history_iff.
        intros [ Heq | Hin ].
        { injection Heq as H1 H2.
          subst.
          exists (Stream.from v).
          simpl.
          apply Dict.maps_to_last_added. }

        assert (i <> name).
        { intros ieq; inversion Hord as [ | x y lx l H1 H2 H3 ]; subst.
          apply H2.
          apply in_map with (f := fst) in Hin.
          rewrite map_app.
          refine (eq_ind _ _ Hin _ _).
          clear.
          induction body as [ | (y & ty & l) body IH ]; [ rewrite map_map; exact eq_refl | exact (f_equal _ IH) ]. }

        apply IH2, in_history_iff in Hin as [ x Hx ].
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
        2: now apply Ordered.var_not_need_itself with (y := ty) (l := equations_to_dag body n_in).
        now apply Lustre.sem_eval_exp.
      * refine (Forall_impl_in _ _ _ _ IH3).
        intros (i, (tyi, x)) Hin ( s & Hs1 & Hs2 ).
        simpl in *.
        
        destruct (PeanoNat.Nat.eq_dec i name).
        { exfalso.
          subst.
          specialize (IH1 name).
          assert (in_history h (name, tyi)) as H.
          { unfold in_history, Lustre.in_history. rewrite Hs1. reflexivity. }
          apply IH2 in H.
          cbn in Hord; apply Ordered.vars_no_dups in Hord.
          rewrite dag_names in H.
          apply Hord; clear - H.
          rewrite map_app, map_map; fold (@fst ident type).
          refine (eq_ind _ _ (in_map fst _ _ H) _ _).
          rewrite map_app, map_map; f_equal; apply map_ext.
          intros [[]]; exact eq_refl. }
        
        exists s.
        split.
        { now apply Dict.maps_to_add. }

        apply sem_exp_with_useless_var; [ assumption | ].
        cbn in Hord.
        refine (Ordered.vars_coherence _ i _ tyi _ (var_of_exp x) _ Hord _).
        refine (in_or_app _ _ _ (or_introl _)).
        clear - Hin.
        induction body as [|[n [ty e]] tl IH]; [exact Hin|].
        destruct Hin as [[=-> -> H]|H]; [apply sig2T_eq_type in H; subst; left; exact eq_refl|].
        right; exact (IH H).
Qed.
