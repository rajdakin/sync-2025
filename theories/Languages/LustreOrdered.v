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
