From Reactive Require Import Base.
From Reactive.Datatypes Require Stream.

From Coq Require Import Permutation.


Inductive type :=
  | TBool.

Definition binder := prod ident type.

Inductive const :=
  | CBool: Stream.t bool -> const.

Inductive binop :=
  | Bop_and : binop
  | Bop_or : binop
  | Bop_xor : binop.

Inductive exp :=
  | EConst : const -> exp
  | EInput : binder -> exp
  | EVar : binder -> exp
  | EBinop : binop -> exp -> exp -> exp.

Fixpoint has_einput (e: exp): bool :=
  match e with
    | EInput _ => true
    | EConst _ | EVar _ => false
    | EBinop _ e1 e2 => has_einput e1 || has_einput e2
  end.

Definition equation := prod ident exp.

Record node := mk_node {
  n_name: ident;

  n_in: list binder;
  n_out: binder;
  n_locals: list binder;
  n_body: list equation;

  n_vars: list binder := n_in ++ n_out :: n_locals;
  n_assigned_vars: list ident := map fst n_body;

  n_assigned_vars_are_vars: incl n_assigned_vars (map fst n_vars);
  n_assigned_out: In (fst n_out) n_assigned_vars;
  n_inputs_equations: incl (List.map (fun b => (fst b, EInput b)) n_in) n_body;
  n_no_einputs_in_other: Forall (fun '(name, exp) => ~ In name (map fst n_in) -> has_einput exp = false) n_body;
}.

Definition node_eq (n1 n2: node) :=
  n_name n1 = n_name n2 /\
  Permutation (n_in n1) (n_in n2) /\
  n_out n1 = n_out n2 /\
  Permutation (n_locals n1) (n_locals n2) /\
  Permutation (n_body n1) (n_body n2).


Definition var_bool := (0, TBool).

Fixpoint var_of_exp_aux (e: exp) (acc: list ident): list ident :=
  match e with
    | EConst _ => acc
    | EInput _ => acc
    | EVar (name, _) => name :: acc
    | EBinop _ e1 e2 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 acc)
  end.

Definition var_of_exp (e: exp): list ident :=
  var_of_exp_aux e [].


(** ** Equality of binders *)

Definition type_eqb (x y: type): bool :=
  match x, y with
    | TBool, TBool => true
  end.

Definition binder_eqb (x y: binder): bool :=
  andb (fst x =? fst y) (type_eqb (snd x) (snd y)).

Lemma binder_dec (x y: binder): {x = y} + {x <> y}.
Proof.
  destruct x, y.
  destruct t, t0.

  pose proof (PeanoNat.Nat.eq_dec i i0).
  destruct H.
  { now left; f_equal. }

  right.
  inversion 1.
  contradiction.
Defined.

Definition binder_eqb_to_eq (x y : binder): binder_eqb x y = true -> x = y.
Proof.
  unfold binder_eqb, andb.
  destruct (fst x =? fst y) eqn:Heq; [| discriminate ].

  rewrite PeanoNat.Nat.eqb_eq in Heq.
  destruct x, y; simpl in Heq |- *.
  rewrite Heq.

  intros _.
  now destruct t, t0.
Qed.

Definition binder_eq_to_eqb (x y : binder): x = y -> binder_eqb x y = true.
Proof.
  unfold binder_eqb, andb.
  destruct x, y; simpl.

  inversion 1.

  rewrite PeanoNat.Nat.eqb_refl.
  now destruct t, t0.
Qed.


(** ** Equality of equations *)

Definition binop_eqb (x y: binop): bool :=
  match x, y with
    | Bop_and, Bop_and => true
    | Bop_or, Bop_or => true
    | Bop_xor, Bop_xor => true
    | _, _ => false
  end.

Definition const_eqb (x y: const): bool := false.

Definition exp_eqb (x y: exp): bool := false.

Definition exp_eqb_to_eq (x y : exp): exp_eqb x y = true -> x = y.
Proof. Admitted.

Definition equation_eqb (x y: equation): bool :=
  andb (fst x =? fst y) (exp_eqb (snd x) (snd y)).

Definition equation_eqb_to_eq (x y : equation): equation_eqb x y = true -> x = y.
Proof. Admitted.

Definition equation_eq_to_eqb (x y : equation): x = y -> equation_eqb x y = true.
Proof. Admitted.
