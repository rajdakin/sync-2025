From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require Lustre.

Module Lustre := Lustre.


Definition dag := list (prod ident (list ident)).

Fixpoint equations_to_dag (equations: list Lustre.equation): dag :=
  match equations with
    | [] => []
    | (name, exp) :: remaining_eqs => (name, Lustre.var_of_exp exp) :: equations_to_dag remaining_eqs
  end.

Record node_ordered := mk_node_ordered {
  node_ordered_is_node :> Lustre.node;
  ordered: Ordered.t (equations_to_dag (Lustre.n_body node_ordered_is_node));
}.


(** Lemmas *)

Lemma dag_names (equations: list Lustre.equation):
  map fst equations = map fst (equations_to_dag equations).
Proof.
  induction equations.
  - reflexivity.
  - destruct a.
    simpl.
    rewrite IHequations.
    reflexivity.
Qed.

Lemma dag_length (equations: list Lustre.equation):
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
  equations_to_dag equations = map (fun '(name, exp) => (name, Lustre.var_of_exp exp)) equations.
Proof.
  induction equations as [ | (name, exp) l IH ]; [ reflexivity | ].
  simpl.
  f_equal.
  assumption.
Qed.
