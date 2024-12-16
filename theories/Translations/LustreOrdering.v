From Reactive Require Import Base.

From Reactive.Datatypes Require List Result.
From Reactive.Languages Require Lustre LustreOrdered.

From Coq Require Import Sorting Permutation.


Module Source := Lustre.
Module Target := LustreOrdered.


Parameter node_ordering: Source.node -> Result.t (Source.node).

Scheme Equality for list.

Module EquationOrder <: Orders.TotalLeBool.
  Local Coercion is_true : bool >-> Sortclass.

  Definition t := Source.equation.

  Definition leb (x y: Source.equation): bool := Nat.leb (fst x) (fst y).
  Infix "<=?" := leb (at level 70, no associativity).

  Theorem leb_total: forall x y, x <=? y \/ y <=? x.
  Proof.
    intros [] [].
    unfold leb; simpl.

    revert i i0.
    induction i; destruct i0; simpl; auto.
  Qed.
End EquationOrder.

Module Import EquationSort := Sort EquationOrder.


Lemma binder_dec (x y: Source.binder): {x = y} + {x <> y}.
Proof.
  destruct x, y.
  destruct t, t0.

  pose proof (PeanoNat.Nat.eq_dec i i0).
  destruct H.
  { now left; f_equal. }

  right.
  intros H.
  inversion H.
  contradiction.
Qed.

Definition binder_eqb (x y: Source.binder) := fst x =? fst y.

Definition binder_eqb_to_eq (x y : Source.binder): binder_eqb x y = true -> x = y.
Proof. Admitted.

Definition binder_eq_to_eqb (x y : Source.binder): x = y -> binder_eqb x y = true.
Proof. Admitted.


Lemma equation_dec (x y: Source.equation): {x = y} + {x <> y}.
Proof.
  destruct x, y.
  destruct e, e0.
  all: try (right; inversion 1; fail).

  all: pose proof (PeanoNat.Nat.eq_dec i i0) as []; subst.
  all: try (right; inversion 1; contradiction).
Admitted.

Definition equation_eqb (x y: Source.equation) := true.

Definition equation_eqb_to_eq (x y : Source.equation): equation_eqb x y = true -> x = y.
Proof. Admitted.

Definition equation_eq_to_eqb (x y : Source.equation): x = y -> equation_eqb x y = true.
Proof. Admitted.


Definition check_eq_node (source guess: Source.node): Result.t (Source.node_eq source guess).
Proof.
  destruct source as [name1 in1 out1 locals1 body1].
  destruct guess as [name2 in2 out2 locals2 body2].
  unfold Source.node_eq; simpl.

  destruct (PeanoNat.Nat.eq_dec name1 name2).
  2: { apply Result.Err, "Node names are not equal". }

  destruct (list_eq_dec _ binder_eqb binder_eqb_to_eq binder_eq_to_eqb in1 in2).
  2: { apply Result.Err, "Node inputs are not equal". }

  destruct (binder_dec out1 out2).
  2: { apply Result.Err, "Node outputs are not equal". }

  destruct (list_eq_dec _ binder_eqb binder_eqb_to_eq binder_eq_to_eqb locals1 locals2).
  2: { apply Result.Err, "Node locals are not equal". }

  destruct (list_eq_dec _ equation_eqb equation_eqb_to_eq equation_eq_to_eqb (sort body1) (sort body2)).
  2: { apply Result.Err, "Node equations are not permutations". }

  apply Result.Ok; subst.
  repeat split; try (assumption || apply Permutation_refl).

  pose proof (Permuted_sort body1).
  pose proof (Permuted_sort body2).

  rewrite e3 in H.
  now apply perm_trans with (sort body2).
Defined.

Definition check_dag_ordered (guess: Target.dag): Result.t (Ordered.t guess).
Proof.
  induction guess as [| x xs IHguess ].
  { apply Result.Ok, Ordered.nil. }

  inversion IHguess as [| err ].
  2: { apply Result.Err, err. }

  destruct x as [i l].
  destruct (in_dec PeanoNat.Nat.eq_dec i (map fst xs)).
  { apply Result.Err, "Identifier is in list". }

  induction l as [| y ? IHl ].
  { apply Result.Ok, Ordered.alone; assumption. }

  inversion IHl as [ IHl' | err ].
  2: { apply Result.Err, err. }

  destruct (in_dec PeanoNat.Nat.eq_dec y (map fst xs)).
  2: { apply Result.Err, "Identifier not bound". }

  apply Result.Ok, Ordered.append.
  { assumption. }
  { assumption. }

  constructor.
  { now apply List.in_map_fst. }

  inversion IHl'.
  + constructor.
  + assumption.
Defined.


Import Result.notations.

Definition check_order (source guess: Source.node): Result.t Target.node_ordered :=
  let dag := Target.equations_to_dag (Source.n_body guess) in
  do _ <- check_eq_node source guess;
  do ordered <- check_dag_ordered dag;

  Result.Ok {|
    Target.node_ordered_is_node := guess;
    Target.ordered := ordered;
  |}.

Definition translate_node (source: Source.node): Result.t Target.node_ordered :=
  node_ordering source >>= check_order source.
