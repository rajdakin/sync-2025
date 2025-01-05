From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require LustreAst Lustre.

Module Lustre := Lustre.


Definition dag := list (prod ident (list ident)).

Fixpoint equations_to_dag (equations: list LustreAst.equation): dag :=
  match equations with
    | [] => []
    | (name, exp) :: remaining_eqs => (name, LustreAst.var_of_exp exp) :: equations_to_dag remaining_eqs
  end.

Record node_ordered := mk_node_ordered {
  node_ordered_is_node :> Lustre.node;
  ordered: Ordered.t (equations_to_dag (Lustre.n_body node_ordered_is_node));
}.

(** Lemmas *)

Lemma dag_names (equations: list LustreAst.equation):
  map fst equations = map fst (equations_to_dag equations).
Proof.
  induction equations.
  - reflexivity.
  - destruct a.
    simpl.
    rewrite IHequations.
    reflexivity.
Qed.

Lemma dag_length (equations: list LustreAst.equation):
  List.length equations = List.length (equations_to_dag equations).
Proof.
  induction equations.
  - simpl.
    reflexivity.
  - destruct a.
    simpl.
    apply f_equal.
    assumption.
Qed.

Lemma dag_nil (equations: list LustreAst.equation):
  equations = [] <-> equations_to_dag equations = [].
Proof.
  split.
  - intros eq.
    pose proof (@f_equal _ _ (@List.length LustreAst.equation) _ _ eq) as H.
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

Lemma equations_to_dag_is_map (equations: list LustreAst.equation):
  equations_to_dag equations = map (fun '(name, exp) => (name, LustreAst.var_of_exp exp)) equations.
Proof.
  induction equations as [ | (name, exp) l IH ]; [ reflexivity | ].
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

Lemma sem_exp_with_useless_var (e: Lustre.exp) (h: Lustre.history) (name: ident) (v: Lustre.value) (s: Stream.t Lustre.value):
  Lustre.sem_exp h e v ->
  ~ In name (LustreAst.var_of_exp e) ->
  Lustre.sem_exp (Dict.add name s h) e v.
Proof.
  intros Hexp Hnin.
  revert v Hexp.
  induction e as [ c | | (i, t) | op e IH | op e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 ]; intros v Hexp.
  - inversion Hexp.
    subst.
    apply Lustre.SeConst.
  - inversion Hexp.
    subst.
    apply Lustre.SeInput.
  - inversion Hexp.
    subst.
    unfold LustreAst.var_of_exp in Hnin.
    simpl in Hnin.
    apply Lustre.SeVar.
    simpl.
    apply Dict.maps_to_add; [ assumption | ].
    intros Heq.
    apply Hnin.
    left.
    assumption.
  - inversion Hexp.
    subst.
    apply Lustre.SeUnop.
    apply IH; assumption.
  - inversion Hexp.
    subst.
    pose proof (Lustre.var_of_exp_not_in_binop e1 e2 name op) as [ H1' H2' ]; [ assumption | ].
    apply Lustre.SeBinop.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - inversion Hexp.
    subst.
    pose proof (Lustre.var_of_exp_not_in_ifte e1 e2 e3 name) as ( H1' & H2' & H3' ); [ assumption | ].
    apply Lustre.SeIfte.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

Lemma var_of_last_exp_in_body (body: list LustreAst.equation) (name: ident) (exp: Lustre.exp):
  Ordered.t (equations_to_dag ((name, exp) :: body)) ->
  Forall (fun x => In x (map fst body)) (LustreAst.var_of_exp exp).
Proof.
  intros Hord.
  induction exp as [ c | | (i, t) | op e IH | op e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 ].
  - constructor.
  - constructor.
  - constructor; [ | constructor ].
    simpl in Hord.
    apply Ordered.var_cons_in_right_side with (y := i) in Hord.
    + destruct Hord as [ ly Hly ].
      apply in_map with (f := fst) in Hly.
      rewrite <- dag_names in Hly.
      assumption.
    + left.
      reflexivity.
  - apply IH.
    assumption.
  - simpl in Hord.
    rewrite Lustre.var_of_exp_binop_eq in Hord |- *.
    apply Forall_app.
    split.
    + apply IH1.
      apply Ordered.app_right_side_l in Hord.
      assumption.
    + apply IH2.
      apply Ordered.app_right_side_r in Hord.
      assumption.
  - simpl in Hord.
    rewrite Lustre.var_of_exp_ifte_eq in Hord |- *.
    apply Forall_app.
    split.
    + apply Ordered.app_right_side_l in Hord.
      apply IH1.
      assumption.
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

Lemma minimal_history (body: list LustreAst.equation):
  Ordered.t (equations_to_dag body) ->
  exists (h: Lustre.history),
    (forall (i: ident), Dict.is_in i h <-> In i (map fst body)) /\
    (Forall (fun eq =>
      exists (v': Stream.t Lustre.value),
      Dict.maps_to (fst eq) v' h /\ Lustre.sem_exp h (snd eq) (Stream.hd v')
    ) body).
Proof.
  intros Hord.
  induction body as [ | (name, exp) body IH ].
  - exists (Dict.empty _).
    split; [ | constructor ].
    intros i.
    split.
    2: { inversion 1. }
    intros Hi.
    inversion Hi.
    inversion H.
  - specialize (IH (Ordered.cons _ _ Hord)) as ( h & IH1 & IH2 ).

    assert (Forall (fun v => Dict.is_in v h) (LustreAst.var_of_exp exp)) as Hforall.
    { apply Forall_impl with (P := fun v => In v (map fst body)).
      - apply IH1.
      - apply var_of_last_exp_in_body with (name := name).
        assumption. }

    pose proof (Lustre.exp_with_evaluable_vars_is_evaluable exp h Hforall) as [ v Hv ].
    
    exists (Dict.add name (Stream.from v) h).
    split.
    + intros i.
      split.
      * intros [ x Hx ].
        destruct (PeanoNat.Nat.eq_dec i name).
        { left. symmetry. assumption. }
        apply Dict.maps_to_not_last_added in Hx; [ | assumption ].
        right.
        apply IH1.
        exists x.
        assumption.
      * intros [ Heq | Hin ].
        { simpl in Heq.
          subst.
          exists (Stream.from v).
          simpl.
          apply Dict.maps_to_last_added. }

        destruct (PeanoNat.Nat.eq_dec i name).
        { subst. exists (Stream.from v). apply Dict.maps_to_last_added. }

        apply IH1 in Hin as [ x Hx ].
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
        2: now apply Ordered.var_not_need_itself with (l := equations_to_dag body).
        now apply Lustre.sem_eval_exp.
      * apply Forall_impl_in with (P := fun eq : nat * Lustre.exp => exists v' : Stream.t Lustre.value, Dict.maps_to (fst eq) v' h /\ Lustre.sem_exp h (snd eq) (Stream.hd v')); [ | assumption ].
        intros (i, x) Hin ( s & Hs1 & Hs2 ).
        simpl in *.
        
        destruct (PeanoNat.Nat.eq_dec i name).
        { exfalso.
          subst.
          specialize (IH1 name).
          assert (Dict.is_in name h) as H.
          { exists s. assumption. }
          apply IH1 in H.
          apply Ordered.vars_no_dups in Hord.
          rewrite <- dag_names in Hord.
          contradiction. }
        
        exists s.
        split.
        { now apply Dict.maps_to_add. }

        apply sem_exp_with_useless_var; [ assumption | ].
        apply Ordered.vars_coherence with (y := i) (ly := LustreAst.var_of_exp x) in Hord; [ assumption | ].
        apply in_map with (f := fun '(i, x) => (i, LustreAst.var_of_exp x)) in Hin.
        rewrite equations_to_dag_is_map.
        assumption.
Qed.
