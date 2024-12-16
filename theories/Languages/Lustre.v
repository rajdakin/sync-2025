From Reactive Require Import Base.
From Reactive.Datatypes Require Stream.


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
