From Reactive Require Import Base.
From Reactive.Datatypes Require Dict Stream.
From Reactive.Languages Require LustreAst.


From Stdlib Require Import Permutation String.

Module LustreAst := LustreAst.

Definition binder := LustreAst.binder.

Record node := mk_node {
  node_ast :> LustreAst.node;

  n_vars: list binder := LustreAst.n_in node_ast ++ (LustreAst.n_out node_ast) :: (LustreAst.n_locals node_ast);
  n_assigned_vars: list ident := map fst (LustreAst.n_body node_ast);

  n_assigned_vars_are_vars: incl n_assigned_vars (map fst n_vars);
  n_assigned_out: In (fst (LustreAst.n_out node_ast)) n_assigned_vars;
  n_out_is_not_an_input: ~ In (LustreAst.n_out node_ast) (LustreAst.n_in node_ast);
  n_inputs_equations: incl (List.map (fun b => (fst b, LustreAst.EInput b)) (LustreAst.n_in node_ast)) (LustreAst.n_body node_ast);
  n_no_einputs_in_other: Forall (fun '(name, exp) => ~ In name (map fst (LustreAst.n_in node_ast)) -> LustreAst.has_einput exp = false) (LustreAst.n_body node_ast);
}.



Definition n_name (n:node) := LustreAst.n_name (node_ast n).
Definition n_in (n:node) := LustreAst.n_in (node_ast n).
Definition n_out (n:node) := LustreAst.n_out (node_ast n).
Definition n_locals (n:node) := LustreAst.n_locals (node_ast n).
Definition n_body (n:node) := LustreAst.n_body (node_ast n).


Definition TBool := LustreAst.TBool.
Definition exp := LustreAst.exp.
Definition EConst := LustreAst.EConst.



Definition node_eq (n1 n2: node) :=
  n_name n1 = n_name n2 /\
  Permutation (n_in n1) (n_in n2) /\
  n_out n1 = n_out n2 /\
  Permutation (n_locals n1) (n_locals n2) /\
  Permutation (n_body n1) (n_body n2).

(** ** Semantics *)
Import LustreAst.
Inductive value :=
  | VConst : const -> value
  | VInput : binder -> value
  | VUnop: unop -> value -> value
  | VBinop: binop -> value -> value -> value
  | VIfte: value -> value -> value -> value.

Definition history := Dict.t (Stream.t value).

Inductive sem_exp: history -> exp -> value -> Prop :=
  | SeConst (h: history) (c: const):
      sem_exp h (EConst c) (VConst c)

  | SeInput (h: history) (b: binder):
      sem_exp h (EInput b) (VInput b)

  | SeVar (h: history) (b: binder) (v: Stream.t value):
      Dict.maps_to (fst b) v h ->
      sem_exp h (EVar b) (Stream.hd v)

  | SeUnop (h: history) (op: unop) (e: exp) (v: value):
      sem_exp h e v ->
      sem_exp h (EUnop op e) (VUnop op v)

  | SeBinop (h: history) (op: binop) (e1 e2: exp) (v1 v2: value):
      sem_exp h e1 v1 ->
      sem_exp h e2 v2 ->
      sem_exp h (EBinop op e1 e2) (VBinop op v1 v2)

  | SeIfte (h: history) (e1 e2 e3: exp) (v1 v2 v3: value):
      sem_exp h e1 v1 ->
      sem_exp h e2 v2 ->
      sem_exp h e3 v3 ->
      sem_exp h (EIfte e1 e2 e3) (VIfte v1 v2 v3).


(** ** Properties *)

Fixpoint eval_exp (e: exp) (h: history): option value :=
  match e with
    | EConst c => Some (VConst c)
    | EInput b => Some (VInput b)
    | EVar (name, typ) => option_map Stream.hd (Dict.find name h)
    | EUnop op e => match eval_exp e h with
      | Some v => Some (VUnop op v)
      | None => None
    end
    | EBinop op e1 e2 => match eval_exp e1 h, eval_exp e2 h with
      | Some v1, Some v2 => Some (VBinop op v1 v2)
      | _, _ => None
    end
    | EIfte e1 e2 e3 => match eval_exp e1 h, eval_exp e2 h, eval_exp e3 h with
      | Some v1, Some v2, Some v3 => Some (VIfte v1 v2 v3)
      | _, _, _ => None
    end
  end.

Definition is_evaluable (e: exp) (h: history): Prop :=
  exists v: value, eval_exp e h = Some v.


(** ** Lemmas *)

Lemma var_of_exp_aux_eq (e: exp) (l: list ident):
  var_of_exp_aux e l = var_of_exp e ++ l.
Proof.
  revert l.
  induction e as [ c | | (v, t) | op e IH | op e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 ]; intros l.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IH.
  - unfold var_of_exp.
    simpl.
    rewrite IH1, IH2, IH1, IH2.
    rewrite app_nil_r, app_assoc.
    reflexivity.
  - unfold var_of_exp.
    simpl.
    rewrite IH1, IH2, IH3, IH1, IH2, IH3.
    rewrite app_nil_r, app_assoc, app_assoc, app_assoc.
    reflexivity.
Qed.

Lemma var_of_exp_aux_empty (e: exp) (l: list ident):
  var_of_exp_aux e l = [] -> l = [].
Proof.
  intros H.
  rewrite var_of_exp_aux_eq in H.
  apply app_eq_nil in H as [ _ H ].
  assumption.
Qed.

Lemma var_of_exp_aux_incl (e: exp) (l1 l2: list ident):
  incl l1 l2 -> incl (var_of_exp_aux e l1) (var_of_exp_aux e l2).
Proof.
  intros H i Hi.
  rewrite var_of_exp_aux_eq in Hi |- *.
  apply in_or_app.
  apply in_app_or in Hi as [ Hin | Hin ]; auto.
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
  intros H.
  rewrite var_of_exp_aux_eq.
  apply in_or_app.
  auto.
Qed.

Lemma var_of_exp_binop_eq (e1 e2: exp) (b: binop):
  var_of_exp (EBinop b e1 e2) = (var_of_exp e1) ++ (var_of_exp e2).
Proof.
  unfold var_of_exp.
  simpl.
  rewrite var_of_exp_aux_eq.
  reflexivity.
Qed.

Lemma var_of_exp_ifte_eq (e1 e2 e3: exp):
  var_of_exp (EIfte e1 e2 e3) = (var_of_exp e1) ++ (var_of_exp e2) ++ (var_of_exp e3).
Proof.
  unfold var_of_exp.
  simpl.
  do 2 rewrite var_of_exp_aux_eq.
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

Lemma var_of_exp_not_in_ifte (e1 e2 e3: exp) (x: ident):
  ~ In x (var_of_exp (EIfte e1 e2 e3)) ->
  ~ In x (var_of_exp e1) /\ ~ In x (var_of_exp e2) /\ ~ In x (var_of_exp e3).
Proof.
  intros Hnin.
  split.
  - intros Hin.
    apply Hnin.
    unfold var_of_exp.
    simpl.
    apply var_of_exp_aux_in_exp.
    assumption.
  - split.
    + intros Hin.
      apply Hnin.
      unfold var_of_exp.
      simpl.
      apply var_of_exp_aux_in_acc.
      apply var_of_exp_aux_in_exp.
      assumption.
    + intros Hin.
      apply Hnin.
      unfold var_of_exp.
      simpl.
      apply var_of_exp_aux_in_acc.
      apply var_of_exp_aux_in_acc.
      assumption.
Qed.

Lemma exp_with_evaluable_vars_is_evaluable (e: exp) (h: history):
  Forall (fun v => Dict.is_in v h) (var_of_exp e) ->
  is_evaluable e h.
Proof.
  intros H.
  induction e as [ c | | (i, t) | op e IH | op e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 ].
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
  - unfold var_of_exp in H.
    simpl in H.
    apply IH in H as [ v Hv ].
    exists (VUnop op v).
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
  - rewrite var_of_exp_ifte_eq in H.
    apply Forall_app in H as [ H1 H2 ].
    apply Forall_app in H2 as [ H2 H3 ].
    apply IH1 in H1 as [ v1 Hv1 ].
    apply IH2 in H2 as [ v2 Hv2 ].
    apply IH3 in H3 as [ v3 Hv3 ].
    exists (VIfte v1 v2 v3).
    simpl.
    rewrite Hv1, Hv2, Hv3.
    reflexivity.
Qed.

Lemma exp_evaluable_have_evaluable_vars (e: exp) (h: history) (v: value):
  eval_exp e h = Some v ->
  Forall (fun v => Dict.is_in v h) (var_of_exp e).
Proof.
  intros H.
  revert v H.
  induction e as [ c | | (i, t) | op e IH | op e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 ]; intros v H.
  - constructor.
  - constructor.
  - constructor; [ | constructor ].
    simpl in H.
    destruct (Dict.find i h) as [ s | ] eqn: Heq; [ | discriminate ].
    exists s.
    assumption.
  - unfold var_of_exp.
    simpl in *.
    destruct (eval_exp e h); [ | discriminate ].
    apply IH with (v := v0).
    reflexivity.
  - simpl in H.
    destruct (eval_exp e1 h) as [ v1 | ]; [ | discriminate ].
    destruct (eval_exp e2 h) as [ v2 | ]; [ | discriminate ].
    specialize (IH1 v1 eq_refl).
    specialize (IH2 v2 eq_refl).
    rewrite var_of_exp_binop_eq.
    apply Forall_app.
    split; assumption.
  - simpl in H.
    destruct (eval_exp e1 h) as [ v1 | ]; [ | discriminate ].
    destruct (eval_exp e2 h) as [ v2 | ]; [ | discriminate ].
    destruct (eval_exp e3 h) as [ v3 | ]; [ | discriminate ].
    rewrite var_of_exp_ifte_eq.
    apply Forall_app.
    split.
    + apply IH1 with (v := v1).
      reflexivity.
    + apply Forall_app.
      split.
      * apply IH2 with (v := v2).
        reflexivity.
      * apply IH3 with (v := v3).
        reflexivity.
Qed.

Theorem sem_eval_exp (e: exp) (h: history) (v: value):
  eval_exp e h = Some v <-> sem_exp h e v.
Proof.
  split.
  - intros H.
    revert v H.
    induction e as [ c | | (i, t) | op e IH | op e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 ]; intros v H.
    + inversion H.
      apply SeConst.
    + inversion H.
      subst.
      apply SeInput.
    + inversion H.
      destruct (Dict.find i h) as [ s | ] eqn: Heq; [ | discriminate ].
      inversion H1.
      apply SeVar.
      assumption.
    + inversion H.
      destruct (eval_exp e h) as [ v' | ]; [ | discriminate ].
      specialize (IH v' eq_refl).
      inversion H1.
      apply SeUnop.
      assumption.
    + simpl in H.
      destruct (eval_exp e1 h) as [ v1 | ]; [ | discriminate ].
      destruct (eval_exp e2 h) as [ v2 | ]; [ | discriminate ].
      specialize (IH1 v1 eq_refl).
      specialize (IH2 v2 eq_refl).
      inversion H.
      apply SeBinop; assumption.
    + simpl in H.
      destruct (eval_exp e1 h) as [ v1 | ]; [ | discriminate ].
      destruct (eval_exp e2 h) as [ v2 | ]; [ | discriminate ].
      destruct (eval_exp e3 h) as [ v3 | ]; [ | discriminate ].
      specialize (IH1 v1 eq_refl).
      specialize (IH2 v2 eq_refl).
      specialize (IH3 v3 eq_refl).
      inversion H.
      apply SeIfte; assumption.
  - intros H.
    revert v H.
    induction e as [ c | | (i, t) | op e IH | op e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 ]; intros v H.
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
      specialize (IH v0 H4).
      rewrite IH.
      reflexivity.
    + inversion H.
      subst.
      simpl.
      specialize (IH1 v1 H5).
      specialize (IH2 v2 H6).
      rewrite IH1, IH2.
      reflexivity.
    + inversion H.
      subst.
      simpl.
      specialize (IH1 _ H4).
      specialize (IH2 _ H6).
      specialize (IH3 _ H7).
      rewrite IH1, IH2, IH3.
      reflexivity.
Qed.
