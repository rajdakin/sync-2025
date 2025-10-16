From Reactive Require Import Base.

From Reactive.Datatypes Require Result.
From Reactive.Languages Require LustreAst Lustre.

From Stdlib Require Import ListDec Bool Sorting Permutation.

Module Source := LustreAst.
Module Target := Lustre.

Definition convert_type (t : Source.type) : Target.type := match t with
  | Source.TVoid => Target.TVoid
  | Source.TBool => Target.TBool
  | Source.TInt => Target.TInt
end.
Definition convert_binder '((n, t) : Source.binder) : Target.binder := (n, convert_type t).

Definition nvars (entry: Source.node) :=
  map convert_binder (Source.n_in entry) ++ convert_binder (Source.n_out entry) :: map convert_binder (Source.n_locals entry).

Open Scope string_scope.

Fixpoint check_exp (env: Dict.t Target.type) (e: Source.exp): Result.t (sigT Target.exp).
Proof.
  destruct e as [ c | (n, ty') | (n, ty') | op e | op e1 e2 | e1 e2 e3 ].
  - left.
    destruct c as [ | b | n ].
    + exists Target.TVoid.
      exact (Target.EConst Target.CVoid).
    + exists Target.TBool.
      exact (Target.EConst (Target.CBool b)).
    + exists Target.TInt.
      exact (Target.EConst (Target.CInt n)).
  - destruct (Dict.find n env) as [ ty | ].
    2: right; exact "An input variable is not declared".
    destruct (Target.type_dec (convert_type ty') ty).
    2: right; exact "An input variable is used with the wrong type".
    left.
    exists ty.
    exact (Target.EInput (n, ty)).
  - destruct (Dict.find n env) as [ ty | ].
    2: right; exact "A variable is not declared".
    destruct (Target.type_dec (convert_type ty') ty).
    2: right; exact "A variable is used with the wrong type".
    left.
    exists ty.
    exact (Target.EInput (n, ty)).
  - refine (Result.bind (check_exp env e) _).
    intros e'.
    exact (match op, e' with
      | Source.Uop_neg, existT _ Target.TInt e => Result.Ok (existT _ _ (Target.EUnop Target.Uop_neg e))
      | Source.Uop_not, existT _ Target.TInt e => Result.Ok (existT _ _ (Target.EUnop Target.Uop_not e))
      | _, _ => Result.Err "Untypeable expression"
    end).
  - refine (Result.bind (check_exp env e1) _).
    intros e1'.
    refine (Result.bind (check_exp env e2) _).
    intros e2'.
    exact (match op, e1', e2' with
      | Source.Bop_and, existT _ Target.TBool e1, existT _ Target.TBool e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_and e1 e2))
      | Source.Bop_or, existT _ Target.TBool e1, existT _ Target.TBool e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_or e1 e2))
      | Source.Bop_xor, existT _ Target.TBool e1, existT _ Target.TBool e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_xor e1 e2))
      | Source.Bop_plus, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_plus e1 e2))
      | Source.Bop_minus, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_minus e1 e2))
      | Source.Bop_mult, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_mult e1 e2))
      | Source.Bop_div, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_div e1 e2))
      | Source.Bop_eq, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_eq e1 e2))
      | Source.Bop_le, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_le e1 e2))
      | Source.Bop_lt, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_lt e1 e2))
      | Source.Bop_ge, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_ge e1 e2))
      | Source.Bop_gt, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_gt e1 e2))
      | _, _, _ => Result.Err "Untypeable expression"
    end).
  - refine (Result.bind (check_exp env e1) _).
    intros e1'.
    refine (Result.bind (check_exp env e2) _).
    intros e2'.
    refine (Result.bind (check_exp env e3) _).
    intros e3'.
    exact (match e1', e2', e3' with
      | existT _ Target.TBool e1, existT _ t2 e2, existT _ t3 e3 =>
          match Target.type_dec t2 t3 with
          | left e => Result.Ok (existT _ _ (Target.EIfte e1 (eq_rect _ _ e2 _ e) e3))
          | right _ => Result.Err "Untypeable expression"
          end
      | _, _, _ => Result.Err "Untypeable expression"
    end).
Defined.

Definition check_body (entry: Source.node): Result.t { body : list Target.equation | incl (map fst body) (map fst (nvars entry)) }.
Proof.
  pose (env := fold_left (fun d '(n, ty) => Dict.add n ty d) (nvars entry) (Dict.empty _)).
  destruct entry.
  induction n_body as [ | [ n e ] tl IH ].
  - left.
    exists [].
    exact (incl_nil_l _).
  - refine (Result.bind (check_exp env e) _).
    intros [ ty e' ].
    refine (Result.bind IH _); clear IH.
    intros [ eqs IH ].
    cbn.
    exact (match ListDec.incl_dec PeanoNat.Nat.eq_dec (n :: map fst eqs) _ with
      | left h => Result.Ok (exist (fun body => incl (map _ body) _) ((n, existT Target.exp ty e') :: eqs) (incl_cons (h _ (or_introl eq_refl)) IH))
      | right _ => Result.Err "A variable is never declared"
      end).
Defined.

Definition n_assigned_vars (body: list Target.equation) :=
  map fst body.

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
  list_eq_dec _ Source.binder_eqb Source.binder_eqb_to_eq Source.binder_eq_to_eqb.

Definition list_eq_dec_equation :=
  list_eq_dec _ Source.equation_eqb Source.equation_eqb_to_eq Source.equation_eq_to_eqb.

Definition check_assigned_out (entry: Source.node) body: Result.t (In (fst (convert_binder (Source.n_out entry))) (n_assigned_vars body)).
Proof.
  exact (match ListDec.In_dec PeanoNat.Nat.eq_dec _ _ with
    | left h => Result.Ok h
    | right h => Result.Err "The output variable is never assigned"
  end).
Defined.

Definition n_out_is_not_an_input (entry: Source.node) :
  Result.t (~ In (fst (convert_binder (Source.n_out entry))) (map fst (map convert_binder (Source.n_in entry)))).
Proof.
  exact (match ListDec.In_dec PeanoNat.Nat.eq_dec _ _ with
    | left h => Result.Err "The output variable is also an input"
    | right h => Result.Ok h
  end).
Defined.


Definition n_inputs_equations (entry: Source.node) body:
  Result.t (incl (List.map (fun '((n, ty) as b) => (n, existT Target.exp ty (Target.EInput b))) (map convert_binder (Source.n_in entry))) body).
Proof.
  refine (match ListDec.incl_dec _ _ _ with
    | left h => Result.Ok h
    | right h => Result.Err "The output variable is never assigned"
  end).
  intros [n1 [ty1 e1]] [n2 [ty2 e2]].
  destruct (PeanoNat.Nat.eq_dec n1 n2) as [ <- | n ]; [ | right; injection as e _; contradiction (n e) ].
  destruct (Target.type_dec ty1 ty2) as [ <- | n ]; [ | right; injection as _ e; contradiction (n (projT1_eq e)) ].
  destruct (Target.exp_dec e1 e2) as [ <- | n ]; [ left; reflexivity | ].
  right; intros [=f]; exact (n (Target.sig2T_eq_type f)).
Defined.


Definition n_no_einputs_in_other (entry: Source.node) (body: list Target.equation):
  Result.t (Forall (fun '(name, existT _ _ exp) => ~ In name (map fst (map convert_binder (Source.n_in entry))) -> Target.has_einput exp = false) body).
Proof.
  refine (match Forall_dec _ _ _ with
    | left h => Result.Ok h
    | right _ => Result.Err "A variable not present in inputs has an EInput subexpression"
  end).
  intros [n [ty e]].
  refine (match ListDec.In_dec PeanoNat.Nat.eq_dec _ _ with left h => left (fun f => False_ind _ (f h)) | right h => _ end).
  destruct (Target.has_einput); [ right | left; reflexivity ].
  intros f.
  apply f in h.
  discriminate h.
Defined.

Import Result.notations.

Definition check_node_prop (entry: Source.node): Result.t Target.node :=
  do '(exist _ n_body assigned_vars_are_vars) <- check_body entry;
  do check_assigned <- check_assigned_out entry n_body;
  do n_out_is_not_an_input <- n_out_is_not_an_input entry;
  do n_inputs_equations <- n_inputs_equations entry n_body;
  do n_no_einputs_in_other <- n_no_einputs_in_other entry n_body;
  Result.Ok {|
      Target.n_name := Source.n_name entry;
      Target.n_in := map convert_binder (Source.n_in entry);
      Target.n_out := convert_binder (Source.n_out entry);
      Target.n_locals := map convert_binder (Source.n_locals entry);
      Target.n_body := n_body;
      Target.n_assigned_vars_are_vars := assigned_vars_are_vars;
      Target.n_assigned_out := check_assigned;
      Target.n_out_is_not_an_input := n_out_is_not_an_input;
      Target.n_inputs_equations := n_inputs_equations;
      Target.n_no_einputs_in_other := n_no_einputs_in_other
    |}.
