Set Default Goal Selector "!".

From Stdlib Require Import List String.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require LustreTiming.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Identifier.

Import ListNotations.

Module Source := LustreTiming.

Definition unop := Source.unop.
Definition binop := Source.binop.
Definition exp := Source.comb_exp.
Definition var_of_exp := @Source.var_of_exp.
Arguments var_of_exp {_} _.
Definition equation := Source.equation.
Definition equation_dest := Source.equation_dest.
Definition node := Source.node.
Definition sem_unop := @Source.sem_unop.
Arguments sem_unop {_} {_} _ _ _.
Definition sem_binop := @Source.sem_binop.
Arguments sem_binop {_} {_} {_} _ _ _ _.
Definition sem_exp := @Source.sem_comb_exp.
Arguments sem_exp _ _ {_} _ _.
Definition sem_node := Source.sem_node.

Definition dag := list (binder * list binder).

Definition equations_to_dag_aux (equations: list equation): dag := map (fun eq => (equation_dest eq, var_of_exp (projT2 (snd eq)))) equations.
Definition equations_to_dag equations n_in: dag := equations_to_dag_aux equations ++ List.map (fun ity => (ity, [])) n_in.

Definition binder_to_orderable (b: binder): ident * (string * type) := (binder_id b, (binder_name b, binder_ty b)).
Definition dag_to_orderable (dag: dag): list ((ident * (string * type)) * list (ident * (string * type))) :=
  List.map (fun '(b, deps) => (binder_to_orderable b, List.map binder_to_orderable deps)) dag.

Record node_ordered := mk_node_ordered {
  node_ordered_is_node :> node;
  ordered_init: Ordered.t (dag_to_orderable (equations_to_dag (Source.n_init node_ordered_is_node) (Source.n_in node_ordered_is_node)));
  ordered_step: Ordered.t (dag_to_orderable (equations_to_dag (Source.n_step node_ordered_is_node)
                                                              (Source.n_in node_ordered_is_node ++ map fst (Source.n_pre node_ordered_is_node))));
}.

(** Lemmas *)

Lemma dag_names (equations: list equation):
  map equation_dest equations = map fst (equations_to_dag_aux equations).
Proof.
  exact (eq_sym (map_map _ _ _)).
Qed.

Lemma dag_length (equations: list equation):
  List.length (equations_to_dag_aux equations) = List.length equations.
Proof.
  exact (length_map _ _).
Qed.

Lemma dag_nil (equations: list equation):
  equations = [] <-> equations_to_dag_aux equations = [].
Proof.
  split.
  1: intros ->; exact eq_refl.
  intros H; exact (map_eq_nil _ _ H).
Qed.

(** Minimal history for correctness proof *)

Lemma sem_exp_with_useless_var {tys tye} (h: history) (t: nat) (e: exp tye) (v: value _) (i: ident) (s: Stream.t (value tys)):
  sem_exp h t e v ->
  (forall b', binder_id b' = i -> ~ In b' (var_of_exp e)) ->
  sem_exp (Dict.add i (existT _ _ s) h) t e v.
Proof.
  intros Hexp Hnin.
  revert v Hexp.
  induction e as [ loc ty c | loc b | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros v Hexp.
  - inversion Hexp.
    simpl_exist_type.
    subst.
    apply Source.SeConst.
  - inversion Hexp as [| | | |b' s' Hmaps l' eqty1 eqty2 Hv].
    simpl_exist_type.
    subst.
    clear eqty1 eqty2.
    unfold var_of_exp, Source.var_of_exp, Source.var_of_exp_aux in Hnin.
    apply Source.SeVar.
    apply Dict.maps_to_add; [exact Hmaps|].
    intros f; exact (Hnin _ f (or_introl eq_refl)).
  - inversion Hexp.
    simpl_exist_type.
    subst.
    eapply Source.SeUnop; [|eassumption].
    apply IH; assumption.
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    eapply Source.SeBinop; [apply IH1|apply IH2|eassumption].
    2,4: assumption.
    all: clear - Hnin; intros b' H1 H2; refine (Hnin _ H1 _).
    all: cbn; rewrite Source.var_of_exp_aux_eq; apply in_or_app.
    1: left; exact H2.
    right; exact H2.
  - inversion Hexp.
    simpl_exist_type.
    subst.
    eapply Source.SeIfte; [apply IH1|apply IH2|apply IH3].
    2,4,6: assumption.
    all: clear - Hnin; intros b' H1 H2; refine (Hnin _ H1 _).
    all: cbn; rewrite 2!Source.var_of_exp_aux_eq, !in_app_iff.
    1: left; exact H2.
    all: right.
    1: left; exact H2.
    right; exact H2.
Qed.

Lemma var_of_last_exp_in_body {ty} (body: list equation) (name: string * ident) (e: exp ty) n_in:
  Ordered.t (dag_to_orderable (equations_to_dag ((name, existT exp _ e) :: body) n_in)) ->
  Forall (fun v => In v (map equation_dest body) \/ In v n_in) (var_of_exp e).
Proof.
  destruct name as [n i].
  induction e as [ loc ty c | loc b | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros Hord.
  - constructor.
  - constructor; [ | constructor ].
    simpl in Hord.
    apply Ordered.var_cons_in_right_side with (y := binder_id b) (b := (binder_name b, binder_ty b)) in Hord.
    + destruct Hord as [ ly Hly ].
      apply in_map with (f := fst) in Hly.
      cbn in Hly; unfold dag_to_orderable in Hly.
      apply (in_map (fun '(i, (n, ty)) => {| binder_name := n; binder_id := i; binder_ty := ty |})) in Hly.
      rewrite !map_map in Hly.
      rewrite (map_ext _ fst) in Hly.
      2: clear; intros [[n i t] deps]; exact eq_refl.
      match type of Hly with In ?b0 _ => assert (tmp : b0 = b) by (destruct b; exact eq_refl); rewrite tmp in Hly; clear tmp end.
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
    rewrite (Source.var_of_exp_aux_eq e1 _ : var_of_exp (Source.EBinop _ _ _ _) = var_of_exp _ ++ var_of_exp _) in Hord |- *.
    rewrite map_app in Hord.
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
    rewrite (Source.var_of_exp_aux_eq e1 _ : var_of_exp (Source.EIfte _ _ _ _) = var_of_exp _ ++ Source.var_of_exp_aux _ (var_of_exp _)) in Hord |- *.
    rewrite (Source.var_of_exp_aux_eq e2 _ : Source.var_of_exp_aux _ _ = var_of_exp _ ++ var_of_exp _) in Hord |- *.
    rewrite !map_app in Hord.
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

(* False in the case of partial semantics *)
(* Lemma minimal_history (body: list equation) n_in h0:
  (forall (i: ident) ty, in_history h0 (i, ty) <-> In (i, ty) n_in) ->
  Ordered.t (equations_to_dag body n_in) ->
  exists (h: history),
    Dict.inclusion h0 h /\
    (forall (i: ident) ty, in_history h (i, ty) <-> In (i, ty) (map equation_dest body ++ n_in)) /\
    (Forall (fun '(n, existT _ ty eq) =>
      exists (v': Stream.t (value ty)),
      Dict.maps_to n (existT _ ty v') h /\ sem_exp h eq (Stream.hd v')
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

    pose proof (Source.exp_with_evaluable_vars_is_evaluable h exp Hforall) as [ v Hv ].
    
    exists (Dict.add name (existT _ _ (Stream.from v)) h).
    split; [|split].
    + intros i [ty' e] H.
      refine (Dict.maps_to_add _ _ _ _ _ (IH1 _ _ H) _).
      intros <-.
      cbn in Hord; refine (Ordered.vars_no_dups _ _ _ _ Hord _).
      rewrite map_app, map_map.
      refine (in_or_app _ _ _ (or_intror (in_map _ _ (_, _) (proj1 (Hhist0 i ty') _)))).
      unfold in_history, Source.in_history.
      rewrite H; exact eq_refl.
    + intros i.
      split.
      * rewrite in_history_iff.
        intros [ x Hx ].
        destruct (PeanoNat.Nat.eq_dec i name).
        { left.
          unfold equation_dest, Source.equation_dest; cbn; f_equal.
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
        apply Source.sem_eval_exp.
        simpl.
        apply Source.sem_eval_exp.
        apply sem_exp_with_useless_var.
        2: now apply Ordered.var_not_need_itself with (y := ty) (l := equations_to_dag body n_in).
        now apply Source.sem_eval_exp.
      * refine (Forall_impl_in _ _ _ _ IH3).
        intros (i, (tyi, x)) Hin ( s & Hs1 & Hs2 ).
        simpl in *.
        
        destruct (PeanoNat.Nat.eq_dec i name).
        { exfalso.
          subst.
          specialize (IH1 name).
          assert (in_history h (name, tyi)) as H.
          { unfold in_history, Source.in_history. rewrite Hs1. reflexivity. }
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
Qed. *)
