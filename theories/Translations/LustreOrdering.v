Set Default Goal Selector "!".

From Reactive.Datatypes Require Result Sorted.
From Reactive.Languages Require Lustre LustreOrdered.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Dec Identifier.

From Stdlib Require Import List Sorting Permutation String.

Import ListNotations.


Module Source := Lustre.
Module Target := LustreOrdered.

Parameter node_ordering: Source.node -> Result.t type (Source.node).


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


Definition list_eq_dec_binder :=
  List.list_eq_dec binder_dec.

Definition list_eq_dec_equation :=
  List.list_eq_dec Source.equation_dec.

Definition check_eq_node (source guess: Source.node): Result.t type (Source.node_eq source guess).
Proof.
  destruct source as [loc1 name1 in1 out1 locals1 body1].
  destruct guess as [loc2 name2 in2 out2 locals2 body2].
  unfold Source.node_eq; simpl.

  destruct (Source.name_dec name1 name2).
  2: { exact (Result.Err [(loc1, Result.InternalError "Node names are not equal")]). }

  destruct (list_eq_dec_binder in1 in2).
  2: { exact (Result.Err [(loc1, Result.InternalError "Node inputs are not equal")]). }

  destruct (list_eq_dec_binder out1 out2).
  2: { exact (Result.Err [(loc1, Result.InternalError "Node outputs are not equal")]). }

  destruct (list_eq_dec_binder locals1 locals2).
  2: { exact (Result.Err [(loc1, Result.InternalError "Node locals are not equal")]). }

  destruct (list_eq_dec_equation (sort body1) (sort body2)).
  2: { exact (Result.Err [(loc1, Result.InternalError "Node equations are not permutations")]). }

  apply Result.Ok; subst.
  repeat split; try (assumption || apply Permutation_refl).

  pose proof (Permuted_sort body1).
  pose proof (Permuted_sort body2).

  rewrite e3 in H.
  now apply perm_trans with (sort body2).
Defined.

Definition check_dag_ordered (loc: Result.location) (guess: Target.dag) (n_in: list (ident * type)):
  Result.t type (Ordered.t guess).
Proof.
  induction guess as [| [ [ i ty ] l ] xs IHguess ].
  { apply Result.Ok, Ordered.nil. }

  refine (Result.bind (Result.combine_prop (Result.combine_prop _ _) IHguess)
            (fun '(conj (conj H2 H3) H1) => Result.Ok (Ordered.append _ _ _ _ H1 H2 H3))); clear IHguess.

  1: exact (match in_dec PeanoNat.Nat.eq_dec _ _ with
      | left _ => Result.Err [(loc, Result.InternalError "Identifier is in list")]
      | right h => Result.Ok h end).

  induction l as [| [ y ty' ] ? IHl ].
  1: left; constructor.
  refine (Result.bind (Result.combine_prop _ IHl) (fun '(conj H1 H2) => Result.Ok (Forall_cons _ H1 H2))); clear IHl.

  destruct (in_dec (prod_dec PeanoNat.Nat.eq_dec type_dec) (y, ty') (map fst xs)).
  2: { exact (Result.Err [(loc, Result.InternalError "Identifier not bound")]). }

  apply Result.Ok.
  now apply Sorted.in_map_fst.
Defined.


Import Result.notations.

Definition check_order (source guess: Source.node): Result.t type Target.node_ordered :=
  let dag := Target.equations_to_dag (Source.n_body guess) (Source.n_in guess) in
  do _ <- check_eq_node source guess;
  do ordered <- check_dag_ordered (Source.n_loc source) dag (Source.n_in guess);

  Result.Ok {|
    Target.node_ordered_is_node := guess;
    Target.ordered := ordered;
  |}.

Definition translate_node (source: Source.node): Result.t type Target.node_ordered :=
  node_ordering source >>= check_order source.
