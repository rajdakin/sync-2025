From Reactive Require Import Base.

From Reactive.Datatypes Require Result.
From Reactive.Languages Require LustreAst Lustre.

From Stdlib Require Import ListDec Bool Sorting Permutation.

Module Source := LustreAst.
Module Target := Lustre.

Definition nvars (entry: Source.node) :=
  Source.n_in entry ++ (Source.n_out entry) :: (Source.n_locals entry).

Definition n_assigned_vars (entry: Source.node) :=
  map fst (Source.n_body entry).

Open Scope string_scope.

Definition check_assigned_vars_are_vars (entry: Source.node): Result.t (incl (n_assigned_vars entry) (map fst (nvars entry))).
Proof.
  destruct entry.
  induction n_body.
  - apply Result.Ok.
    apply incl_nil_l.
  - inversion IHn_body.
    + destruct (ListDec.incl_dec PeanoNat.Nat.eq_dec (map fst (a::n_body)) (map fst (n_in ++ n_out :: n_locals)) ).
      * apply Result.Ok. assumption.
      * apply Result.Err, "A variable is never defined".
    + apply Result.Err, H.
Defined.

Scheme Equality for list.

Module EquationOrder <: Orders.TotalLeBool.
  Local Coercion is_true : bool >-> Sortclass.

  Definition t := LustreAst.equation.

  Definition leb (x y: LustreAst.equation): bool := Nat.leb (fst x) (fst y).
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
  list_eq_dec _ LustreAst.binder_eqb LustreAst.binder_eqb_to_eq LustreAst.binder_eq_to_eqb.

Definition list_eq_dec_equation :=
  list_eq_dec _ LustreAst.equation_eqb LustreAst.equation_eqb_to_eq LustreAst.equation_eq_to_eqb.

Definition check_assigned_out (entry: Source.node): Result.t (In (fst (LustreAst.n_out entry)) (n_assigned_vars entry)).
Proof.
  destruct entry.
  induction n_body.
  - apply Result.Err, "The output variable is never assigned".
  - destruct (ListDec.In_dec PeanoNat.Nat.eq_dec (fst n_out) (map fst (a::n_body))).
    + simpl.
      apply Result.Ok; assumption.
    + apply Result.Err, "The output variable is never assigned".
Defined.

Definition n_out_is_not_an_input (entry: Source.node) :
  Result.t (~ In (LustreAst.n_out entry) (LustreAst.n_in entry)).
Proof.
  destruct entry.
  induction n_in.
  - simpl. apply Result.Ok.
    auto.
  - simpl in *.
    inversion IHn_in as [| err].
    2: apply Result.Err, err.
    destruct (LustreAst.binder_dec a n_out).
    + apply Result.Err, "a variable in out is in input".
    + apply Result.Ok.
      unfold not.
      intro or_eq_in.
      destruct or_eq_in.
      all: auto.
Defined.


Definition n_inputs_equations (entry: Source.node):
  Result.t (incl (List.map (fun b => (fst b, LustreAst.EInput b)) (LustreAst.n_in entry)) (LustreAst.n_body entry)).
Proof.
  destruct entry.
  simpl.
  remember (map (fun b : ident * LustreAst.type => (fst b, LustreAst.EInput b)) n_in) as map_in.
  destruct (ListDec.incl_dec LustreAst.equation_dec map_in (n_body) ).
  - apply Result.Ok; assumption.
  - apply Result.Err, "some inputs are not present in equations".
Defined.


Definition n_no_einputs_in_other (entry: Source.node):
  Result.t (Forall (fun '(name, exp) => ~ In name (map fst (LustreAst.n_in entry)) -> LustreAst.has_einput exp = false) (LustreAst.n_body entry)).
Proof.
  destruct entry.
  simpl.
  induction n_body.
  - apply Result.Ok.
    apply Forall_nil.
  - inversion IHn_body as [| err].
    2: apply Result.Err, err.
    + destruct a as ( a_name & a_exp ).
      destruct (in_dec PeanoNat.Nat.eq_dec a_name (map fst n_in)).
      * apply Result.Ok.
        apply Forall_cons.
        -- intros.
           exfalso.
           auto.
        -- assumption.
      * destruct (Bool.bool_dec (LustreAst.has_einput a_exp) false).
        -- apply Result.Ok.
           apply Forall_cons.
           ++ intros.
              assumption.
           ++ assumption.
        -- apply Result.Err, "a variable not present in inputs as a EInput expression".
Defined.

Import Result.notations.

Definition check_node_prop (entry: Source.node): Result.t Target.node :=
  let assigned_vars := n_assigned_vars entry in
  do assigned_vars_are_vars <- check_assigned_vars_are_vars entry;
  do check_assigned <- check_assigned_out entry;
  do n_out_is_not_an_input <- n_out_is_not_an_input entry;
  do n_inputs_equations <- n_inputs_equations entry;
  do n_no_einputs_in_other <- n_no_einputs_in_other entry;
  Result.Ok {|
      Target.node_ast := entry;
      Target.n_assigned_vars_are_vars := assigned_vars_are_vars;
      Target.n_assigned_out := check_assigned;
      Target.n_out_is_not_an_input := n_out_is_not_an_input;
      Target.n_inputs_equations := n_inputs_equations;
      Target.n_no_einputs_in_other := n_no_einputs_in_other
    |}.
