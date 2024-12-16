From Reactive Require Import Base.
From Reactive.Datatypes Require Dict Stream.

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

Lemma binder_eqb_to_eq (x y : binder): binder_eqb x y = true -> x = y.
Proof.
  unfold binder_eqb, andb.
  destruct (fst x =? fst y) eqn:Heq; [| discriminate ].

  rewrite PeanoNat.Nat.eqb_eq in Heq.
  destruct x, y; simpl in Heq |- *.
  rewrite Heq.

  intros _.
  now destruct t, t0.
Qed.

Lemma binder_eq_to_eqb (x y : binder): x = y -> binder_eqb x y = true.
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

Lemma exp_eqb_to_eq (x y: exp): exp_eqb x y = true -> x = y.
Proof. Admitted.

Definition equation_eqb (x y: equation): bool :=
  andb (fst x =? fst y) (exp_eqb (snd x) (snd y)).

Lemma equation_eqb_to_eq (x y: equation): equation_eqb x y = true -> x = y.
Proof. Admitted.

Lemma equation_eq_to_eqb (x y: equation): x = y -> equation_eqb x y = true.
Proof. Admitted.


(** ** Semantics *)

Inductive value :=
  | VConst : const -> value
  | VInput : binder -> value
  | VBinop : binop -> value -> value -> value.

Definition history := Dict.t value.

Inductive sem_exp: history -> exp -> value -> Prop :=
  | SeConst (h: history) (c: const):
      sem_exp h (EConst c) (VConst c)

  | SeInput (h: history) (b: binder):
      sem_exp h (EInput b) (VInput b)

  | SeVar (h: history) (b: binder) (v: value):
      Dict.maps_to (fst b) v h ->
      sem_exp h (EVar b) v

  | SeBinop (h: history) (op: binop) (e1 e2: exp) (v1 v2: value):
      sem_exp h e1 v1 ->
      sem_exp h e2 v2 ->
      sem_exp h (EBinop op e1 e2) (VBinop op v1 v2).


(** ** Properties *)

Fixpoint eval_exp (e: exp) (h: history): option value :=
  match e with
    | EConst c => Some (VConst c)
    | EInput b => Some (VInput b)
    | EVar (name, typ) => Dict.find name h
    | EBinop op e1 e2 => match eval_exp e1 h, eval_exp e2 h with
      | Some v1, Some v2 => Some (VBinop op v1 v2)
      | _, _ => None
    end
  end.

Definition is_evaluable (e: exp) (h: history): Prop :=
  exists v: value, eval_exp e h = Some v.


(** ** Lemmas *)

Lemma var_of_exp_aux_non_empty (e: exp) (l: list ident):
  l <> [] -> var_of_exp_aux e l <> [].
Proof.
  intros Hl He.
  revert l Hl He.
  induction e as [ | | v | op e1 IHe1 e2 IHe2 ]; intros l Hl He.
  - simpl in He.
    contradiction.
  - simpl in He.
    apply Hl.
    assumption.
  - destruct v.
    simpl in He.
    discriminate.
  - simpl in He.
    apply IHe1 with (l := var_of_exp_aux e2 l).
    + intros He2.
      apply IHe2 with (l := l); assumption.
    + assumption.
Qed.

Lemma var_of_exp_aux_empty (e: exp) (l: list ident):
  var_of_exp_aux e l = [] -> l = [].
Proof.
  revert l.
  induction e as [ | | v | op e1 IHe1 e2 IHe2 ]; intros l H.
  - simpl in H.
    assumption.
  - assumption.
  - destruct v.
    simpl in H.
    discriminate.
  - simpl in H.
    apply IHe2.
    apply IHe1.
    assumption.
Qed.

Lemma var_of_exp_aux_incl (e: exp) (l1 l2: list ident):
  incl l1 l2 -> incl (var_of_exp_aux e l1) (var_of_exp_aux e l2).
Proof.
  intros H x Hx.
  revert l1 l2 x H Hx.
  induction e; intros l1 l2 x H Hx; simpl in *.
  - apply H.
    assumption.
  - apply H.
    assumption.
  - destruct b as [ i t ].
    destruct Hx as [ Hx | Hx ].
    + left.
      assumption.
    + right.
      apply H.
      assumption.
  - apply IHe1 with (l1 := var_of_exp_aux e2 l1); [ | assumption ].
    intros y Hy.
    apply IHe2 with (l1 := l1); assumption.
Qed.

Lemma var_of_exp_aux_in_exp (e: exp) (l: list ident) (x: ident):
  In x (var_of_exp e) -> In x (var_of_exp_aux e l).
Proof.
  apply var_of_exp_aux_incl with (l1 := []).
  intros a Hin.
  destruct Hin.
Qed.

Lemma var_of_exp_aux_in_acc (e: exp) (l: list ident) (x: ident):
  In x l -> In x (var_of_exp_aux e l).
Proof.
  revert l.
  induction e; intros l H.
  - assumption.
  - assumption.
  - destruct b.
    right.
    assumption.
  - simpl.
    apply IHe1.
    apply IHe2.
    assumption.
Qed.

Lemma var_of_exp_aux_eq (e: exp) (l: list ident):
  var_of_exp_aux e l = var_of_exp e ++ l.
Proof.
  revert l.
  induction e as [ c | | (v, t) | op e1 IH1 e2 IH2 ]; intros l; [ reflexivity.. | ].
  unfold var_of_exp.
  simpl.
  rewrite IH1.
  rewrite IH1.
  rewrite IH2.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma var_of_exp_not_in_binop (exp1 exp2: exp) (x: ident) (b: binop):
  ~ In x (var_of_exp (EBinop b exp1 exp2)) ->
  ~ In x (var_of_exp exp1) /\ ~ In x (var_of_exp exp2).
Proof.
  intros Hnin.
  split.
  - intros Hin1.
    apply Hnin.
    unfold var_of_exp.
    simpl.
    apply var_of_exp_aux_in_exp.
    assumption.
  - intros Hin1.
    apply Hnin.
    unfold var_of_exp.
    simpl.
    apply var_of_exp_aux_in_acc.
    assumption.
Qed.

Lemma var_of_exp_binop_empty (exp1 exp2: exp) (b: binop):
  var_of_exp (EBinop b exp1 exp2) = [] ->
  var_of_exp exp1 = [] /\ var_of_exp exp2 = [].
Proof.
  intros H.
  split.
  - unfold var_of_exp in *.
    simpl in H.
    apply var_of_exp_aux_empty in H as H2.
    rewrite H2 in H.
    assumption.
  - unfold var_of_exp in *.
    simpl in H.
    apply var_of_exp_aux_empty in H as H2.
    assumption.
Qed.

Lemma var_of_exp_binop_eq (e1 e2: exp) (b: binop):
  var_of_exp (EBinop b e1 e2) = (var_of_exp e1) ++ (var_of_exp e2).
Proof.
  unfold var_of_exp.
  simpl.
  rewrite var_of_exp_aux_eq.
  reflexivity.
Qed.

Lemma exp_no_var_is_evaluable (e: exp) (h: history):
  var_of_exp e = [] ->
  is_evaluable e h.
Proof.
  intros H.
  induction e as [ c | b | (b, t) | op e1 IH1 e2 IH2 ].
  - exists (VConst c).
    reflexivity.
  - exists (VInput b).
    reflexivity.
  - unfold var_of_exp in H.
    discriminate.
  - apply var_of_exp_binop_empty in H as [ H1 H2 ].
    specialize (IH1 H1) as [ v1 Hv1 ].
    specialize (IH2 H2) as [ v2 Hv2 ].
    exists (VBinop op v1 v2).
    simpl.
    rewrite Hv1.
    rewrite Hv2.
    reflexivity.
Qed.

Lemma exp_with_evaluable_vars_is_evaluable (e: exp) (h: history):
  Forall (fun v => Dict.is_in v h) (var_of_exp e) ->
  exists v: value, eval_exp e h = Some v.
Proof.
  intros H.
  induction e as [ c | b | (b, t) | op e1 IH1 e2 IH2 ].
  - exists (VConst c).
    reflexivity.
  - exists (VInput b).
    reflexivity.
  - apply Forall_inv in H.
    destruct H as [ v Hv ].
    exists v.
    assumption.
  - rewrite var_of_exp_binop_eq in H.
    apply Forall_app in H as [ H1 H2 ].
    specialize (IH1 H1) as [ v1 Hv1 ].
    specialize (IH2 H2) as [ v2 Hv2 ].
    exists (VBinop op v1 v2).
    simpl.
    rewrite Hv1, Hv2.
    reflexivity.
Qed.

Lemma exp_evaluable_have_evaluable_vars (e: exp) (h: history) (v: value):
  eval_exp e h = Some v ->
  Forall (fun v => Dict.is_in v h) (var_of_exp e).
Proof.
  intros H.
  revert v H.
  induction e as [ c' | | (b, t) | op e1 IH1 e2 IH2 ]; intros c H.
  - constructor.
  - constructor.
  - constructor; [ | constructor ].
    simpl in H.
    exists c.
    assumption.
  - simpl in H.
    destruct (eval_exp e1 h) as [ v1 | ]; [ | discriminate ].
    destruct (eval_exp e2 h) as [ v2 | ]; [ | discriminate ].
    specialize (IH1 v1 eq_refl).
    specialize (IH2 v2 eq_refl).
    rewrite var_of_exp_binop_eq.
    apply Forall_app.
    split; assumption.
Qed.

Theorem sem_eval_exp (e: exp) (h: history) (v: value):
  eval_exp e h = Some v <-> sem_exp h e v.
Proof.
  split.
  - intros H.
    revert v H.
    induction e as [ c' | t | (v, t) | op e1 IH1 e2 IH2 ]; intros c H.
    + inversion H.
      apply SeConst.
    + inversion H.
      subst.
      apply SeInput.
    + inversion H.
      apply SeVar.
      assumption.
    + simpl in H.
      destruct (eval_exp e1 h) as [ v1 | ]; [ | discriminate ].
      destruct (eval_exp e2 h) as [ v2 | ]; [ | discriminate ].
      specialize (IH1 v1 eq_refl).
      specialize (IH2 v2 eq_refl).
      inversion H.
      apply SeBinop; assumption.
  - intros H.
    revert v H.
    induction e as [ c' | t | (v, t) | op e1 IH1 e2 IH2 ]; intros c H.
    + inversion H.
      reflexivity.
    + inversion H.
      subst.
      reflexivity.
    + inversion H; subst.
      simpl.
      assumption.
    + inversion H.
      subst.
      simpl.
      specialize (IH1 v1 H5).
      specialize (IH2 v2 H6).
      rewrite IH1, IH2.
      reflexivity.
Qed.
