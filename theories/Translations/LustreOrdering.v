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

Definition list_eq_dec_equation : forall b1 b2, {Forall2 Source.equation_eq b1 b2} + {~ Forall2 Source.equation_eq b1 b2}.
Proof using.
  intros b1 b2.
  destruct (PeanoNat.Nat.eq_dec (List.length b1) (List.length b2)) as [eqlen|nelen].
  2: right; intros f; exact (nelen (Forall2_length f)).
  destruct (Forall_Exists_dec _ (fun p => Source.equation_dec (fst p) (snd p)) (combine b1 b2)) as [H|H]; [left|right].
  - revert b2 eqlen H; induction b1 as [|hd1 tl1 IH]; intros b2 eqlen H.
    1: destruct b2; [constructor|discriminate eqlen].
    destruct b2 as [|hd2 tl2]; [discriminate eqlen|].
    assert (Hhd := Forall_inv H : Source.equation_eq hd1 hd2).
    assert (Htl := Forall_inv_tail H : Forall _ (combine _ _)).
    constructor.
    1: exact Hhd.
    exact (IH _ (f_equal pred eqlen) Htl).
  - revert b2 eqlen H; induction b1 as [|hd1 tl1 IH]; intros b2 eqlen H.
    1: contradiction (proj1 (Exists_nil _) H).
    destruct b2 as [|hd2 tl2]; [discriminate eqlen|].
    cbn in H; apply Exists_cons in H; cbn in H.
    rewrite Forall2_cons_iff.
    intros [Hhd Htl].
    destruct H as [H|H].
    1: exact (H Hhd).
    exact (IH _ (f_equal pred eqlen) H Htl).
Defined.

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

  remember (sort body1) as body1'.
  remember (sort body2) as body2'.
  clear - f H H0.

  revert body1' body2' body2 H f H0; induction body1 as [|hd1 tl1 IH]; intros l2 l3 l4 H12 H23 H34.
  1: exists []; split; [exact (perm_nil _)|apply Permutation_nil in H12; subst; inversion H23; subst].
  1: apply Permutation_sym, Permutation_nil in H34; subst; constructor.
  assert (tmp := Permutation_in _ H12 (or_introl eq_refl)).
  apply in_split in tmp; destruct tmp as [l21 [l22 ->]].
  apply Permutation_cons_app_inv in H12.
  assert (tmp : exists l31 hd3 l32,
      l3 = l31 ++ hd3 :: l32 /\ Forall2 Source.equation_eq l21 l31 /\ Source.equation_eq hd1 hd3 /\ Forall2 Source.equation_eq l22 l32).
  1:{ clear - H23.
    revert l3 H23; induction l21 as [|hd tl IH]; (intros [|hd' tl'] H; [inversion H|]).
    1: exists [], hd', tl'; split; [exact eq_refl|split; [constructor|apply Forall2_cons_iff in H; exact H]].
    cbn in H; apply Forall2_cons_iff in H; destruct H as [H1 H2].
    specialize (IH _ H2) as [l1 [h [l2 [Heq [IH1 IH2]]]]].
    exists (hd' :: l1), h, l2; split; [exact (f_equal (cons _) Heq)|split; [exact (Forall2_cons _ _ H1 IH1)|exact IH2]].
  }
  destruct tmp as [l31 [hd3 [l32 (-> & H231 & H232 & H233)]]].
  assert (tmp := Permutation_in _ (Permutation_sym H34) (in_or_app _ (_ :: _) _ (or_intror (or_introl eq_refl)))).
  apply in_split in tmp; destruct tmp as [l41 [l42 ->]].
  apply Permutation_app_inv in H34.
  specialize (IH _ _ _ H12 (Forall2_app H231 H233) H34) as [IHb [IH1 IH2]].
  apply Forall2_app_inv_r in IH2; destruct IH2 as [IHb1 [IHb2 (IH21 & IH22 & ->)]].
  exists (IHb1 ++ hd1 :: IHb2); split.
  1: apply Permutation_cons_app; exact IH1.
  exact (Forall2_app IH21 (Forall2_cons _ _ H232 IH22)).
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
