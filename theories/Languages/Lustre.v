From Reactive Require Import Base.
From Reactive.Datatypes Require Dict Stream.

From Coq Require Import Permutation.


Inductive type :=
  | TBool.

Definition binder := prod ident type.

Inductive const :=
  | CBool: bool -> const.

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
  n_out_is_not_an_input: ~ In n_out n_in;
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

Lemma type_eqb_refl (t: type):
  type_eqb t t = true.
Proof.
  destruct t.
  reflexivity.
Qed.

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

Lemma binder_eqb_refl (b: binder):
  binder_eqb b b = true.
Proof.
  destruct b as (i, t).
  apply andb_true_intro.
  split.
  - apply PeanoNat.Nat.eqb_refl.
  - apply type_eqb_refl.
Qed.

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

Definition const_eqb (c1 c2: const): bool :=
  match c1, c2 with
    | CBool b1, CBool b2 => Bool.eqb b1 b2
  end.

Fixpoint exp_eqb (e1 e2: exp): bool :=
  match e1, e2 with
    | EConst c1, EConst c2 => const_eqb c1 c2
    | EInput b1, EInput b2 => binder_eqb b1 b2
    | EVar b1, EVar b2 => binder_eqb b1 b2
    | EBinop op1 e11 e12, EBinop op2 e21 e22 =>
      (binop_eqb op1 op2) && (exp_eqb e11 e21) && (exp_eqb e12 e22)
    | _, _ => false
  end.

Lemma binop_eqb_refl (op: binop):
  binop_eqb op op = true.
Proof.
  destruct op; reflexivity.
Qed.

Lemma binop_eqb_to_eq (op1 op2: binop):
  binop_eqb op1 op2 = true -> op1 = op2.
Proof.
  intros H.
  destruct op1, op2; try reflexivity; try inversion H.
Qed.

Lemma const_eqb_refl (c: const):
  const_eqb c c = true.
Proof.
  destruct c.
  simpl.
  destruct b; reflexivity.
Qed.

Lemma const_eqb_to_eq (c1 c2: const):
  const_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros H.
  revert c2 H.
  induction c1 as [ b1 ]; intros c2 H.
  destruct c2.
  inversion H.
  apply Bool.eqb_prop in H1.
  subst.
  reflexivity.
Qed.

Lemma exp_eqb_refl (e: exp):
  exp_eqb e e = true.
Proof.
  induction e.
  - apply const_eqb_refl.
  - apply binder_eqb_refl.
  - apply binder_eqb_refl.
  - apply andb_true_intro.
    split; [ | assumption ].
    apply andb_true_intro.
    split; [ | assumption ].
    apply binop_eqb_refl.
Qed.

Lemma exp_eqb_to_eq (e1 e2: exp):
  exp_eqb e1 e2 = true -> e1 = e2.
Proof.
  intros H.
  revert e2 H.
  induction e1 as [ c1 | b1 | b1 | op1 e11 IH1 e12 IH2 ]; intros e2 H.
  - destruct e2; try inversion H.
    apply const_eqb_to_eq in H1.
    subst.
    reflexivity.
  - destruct e2; try inversion H.
    apply binder_eqb_to_eq in H1.
    subst.
    reflexivity.
  - destruct e2; try inversion H.
    apply binder_eqb_to_eq in H1.
    subst.
    reflexivity.
  - destruct e2; try inversion H.
    apply andb_prop in H1 as [ H1 H2 ].
    apply andb_prop in H1 as [ H3 H1 ].
    apply IH1 in H1.
    apply IH2 in H2.
    apply binop_eqb_to_eq in H3.
    rewrite H1, H2, H3.
    reflexivity.
Qed.

Definition equation_eqb (eq1 eq2: equation): bool :=
  (fst eq1 =? fst eq2) && (exp_eqb (snd eq1) (snd eq2)).

Lemma equation_eqb_to_eq (eq1 eq2: equation):
  equation_eqb eq1 eq2 = true -> eq1 = eq2.
Proof.
  intros H.
  destruct eq1, eq2.
  apply andb_prop in H as [ H1 H2 ].
  apply PeanoNat.Nat.eqb_eq in H1.
  apply exp_eqb_to_eq in H2.
  simpl in H1, H2.
  rewrite H1, H2.
  reflexivity.
Qed.

Lemma equation_eqb_refl (eq: equation):
  equation_eqb eq eq = true.
Proof.
  destruct eq as (i, e).
  apply andb_true_intro.
  split.
  - apply PeanoNat.Nat.eqb_refl.
  - apply exp_eqb_refl.
Qed.

Lemma equation_eq_to_eqb (eq1 eq2: equation):
  eq1 = eq2 -> equation_eqb eq1 eq2 = true.
Proof.
  intros H.
  rewrite H.
  apply equation_eqb_refl.
Qed.


(** ** Semantics *)

Inductive value :=
  | VConst : const -> value
  | VInput : binder -> value
  | VBinop : binop -> value -> value -> value.

Definition history := Dict.t (Stream.t value).

Inductive sem_exp: history -> exp -> value -> Prop :=
  | SeConst (h: history) (c: const):
      sem_exp h (EConst c) (VConst c)

  | SeInput (h: history) (b: binder):
      sem_exp h (EInput b) (VInput b)

  | SeVar (h: history) (b: binder) (v: Stream.t value):
      Dict.maps_to (fst b) v h ->
      sem_exp h (EVar b) (Stream.hd v)

  | SeBinop (h: history) (op: binop) (e1 e2: exp) (v1 v2: value):
      sem_exp h e1 v1 ->
      sem_exp h e2 v2 ->
      sem_exp h (EBinop op e1 e2) (VBinop op v1 v2).


(** ** Properties *)

Fixpoint eval_exp (e: exp) (h: history): option value :=
  match e with
    | EConst c => Some (VConst c)
    | EInput b => Some (VInput b)
    | EVar (name, typ) => option_map Stream.hd (Dict.find name h)
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
    exists (Stream.hd v).
    simpl.
    rewrite Hv.
    reflexivity.
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
    destruct (Dict.find b h) as [ s | ] eqn: Heq; [ | discriminate ].
    exists s.
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
      destruct (Dict.find v h) as [ s | ] eqn: Heq; [ | discriminate ].
      inversion H1.
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
      rewrite H2.
      reflexivity.
    + inversion H.
      subst.
      simpl.
      specialize (IH1 v1 H5).
      specialize (IH2 v2 H6).
      rewrite IH1, IH2.
      reflexivity.
Qed.
