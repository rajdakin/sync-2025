From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require LustreOrdered Imp.

Module Source := LustreOrdered.Lustre.
Module Target := Imp.


Definition translate_const (c: Source.const): Target.const :=
  match c with
  | Source.CBool b => Target.CBool (Stream.hd b)
  end.

Definition translate_type (t: Source.type): Target.type :=
  match t with
  | Source.TBool => Target.TBool
  end.

Definition translate_binder (b: Source.binder): Target.binder :=
  (fst b, translate_type (snd b)).

Definition translate_binop (op: Source.binop): Target.binop :=
  match op with
  | Source.Bop_and => Target.Bop_and
  | Source.Bop_or => Target.Bop_or
  | Source.Bop_xor => Target.Bop_xor
  end.

Fixpoint translate_value (v: Source.value): Target.value :=
  match v with
  | Source.VConst c => Target.VConst (translate_const c)
  | Source.VInput b => Target.VInput (translate_binder b)
  | Source.VBinop op v1 v2 => Target.VBinop (translate_binop op) (translate_value v1) (translate_value v2)
  end.

Fixpoint translate_exp (e: Source.exp): Target.exp :=
  match e with
  | Source.EConst c => Target.EConst (translate_const c)
  | Source.EInput b => Target.EInput (translate_binder b)
  | Source.EVar b => Target.EVar (translate_binder b)
  | Source.EBinop op e1 e2 => Target.EBinop (translate_binop op) (translate_exp e1) (translate_exp e2)
  end.

Definition translate_equation (eq: Source.equation): Target.stmt :=
  Target.SAssign (fst eq) (translate_exp (snd eq)).

Definition translate_history (h: Source.history): Target.stack :=
  Dict.map (fun x => translate_value x) h.

Definition translate_node_body (body: list Source.equation): Target.stmt :=
  fold_right (fun acc x => Target.SSeq x acc) Target.SNop (List.map translate_equation body).

Lemma in_fst_has_snd {A B: Type} (x: A) (l: list (A * B)):
  In x (map fst l) ->
    exists y: B, In (x, y) l.
Proof.
  intros Hin.
  induction l as [ | (y, ly) l IH ]; [ inversion Hin | ].
  destruct Hin as [ Heq | Hin ].
  - subst.
    exists ly.
    left.
    reflexivity.
  - specialize (IH Hin) as [ lx Hlx ].
    exists lx.
    right.
    assumption.
Qed.

Lemma lustre_assignment_is_substmt (n: LustreOrdered.node_ordered) (name: ident) (exp: Source.exp):
  In (name, exp) (Source.n_body (LustreOrdered.node_ordered_is_node n)) ->
  Target.is_substmt (Target.SAssign name (translate_exp exp)) (translate_node_body (Source.n_body (LustreOrdered.node_ordered_is_node n))) = true.
Proof.
  destruct n.
  destruct node_ordered_is_node.
  simpl in *.
  intros Hin.
  clear n_assigned_out n_inputs_equations n_no_einputs_in_other.
  induction n_body as [ | (eq_left, eq_right) body IH ]; [ inversion Hin | ].
  simpl.
  apply Bool.orb_true_intro.
  destruct Hin as [ Heq | Hin ].
  - inversion Heq.
    subst.
    right.
    rewrite (PeanoNat.Nat.eqb_refl).
    simpl.
    rewrite Target.exp_eqb_refl.
    reflexivity.
  - left.
    apply IH.
    + intros i Hi.
      pose proof (in_cons eq_left _ _ Hi) as H.
      apply n_assigned_vars_are_vars in H.
      assumption.
    + apply Ordered.cons in ordered.
      assumption.
    + assumption.
Qed.

Definition translate_node (n: LustreOrdered.node_ordered): Target.method.
Proof.
  pose n as n'.
  destruct n.
  destruct node_ordered_is_node.
  simpl in *.

  refine ({|
    Target.m_name := n_name;

    Target.m_in := map translate_binder n_in;
    Target.m_out := translate_binder n_out;
    Target.m_vars := map translate_binder n_vars;

    Target.m_body := translate_node_body n_body
  |}).

  apply in_fst_has_snd in n_assigned_out as Hexp.
  destruct Hexp as [ exp Hexp ].
  exists (translate_exp exp).
  replace n_body with (Source.n_body (LustreOrdered.node_ordered_is_node n')); [ | reflexivity ].
  apply lustre_assignment_is_substmt.
  assumption.
Defined.


(** Lemmas *)

Lemma correctness_exp (e: Source.exp) (h: Source.history) (out: Source.value):
  Source.sem_exp h e out ->
    Target.sem_exp (translate_history h) (translate_exp e) (translate_value out).
Proof.
  induction 1.

  - (* EConst *)
    apply Target.SeConst.

  - (* EInput *)
    apply Target.SeInput.

  - (* EVar *)
    apply Target.SeVar; simpl.

    pose (fun e => translate_const (Stream.hd e)) as f.
    now apply Dict.maps_to_map.

  - (* EAnd *)
    simpl.

    apply Target.SeBinop.
    + apply IHsem_exp1.
    + apply IHsem_exp2.
Qed.

Lemma sem_exp_without_useless_var (e: Source.exp) (h: Source.history) (name: ident) (v: Source.value):
  Source.sem_exp h e v ->
  ~ In name (Source.var_of_exp e) ->
    Source.sem_exp (Dict.remove name h) e v.
Proof.
  intros Hexp Hnin.
  revert v Hexp.
  induction e as [ c | t | [ b t ] | op e1 IH1 e2 IH2 ]; intros v Hexp.
  - inversion Hexp.
    subst.
    apply Source.SeConst.
  - inversion Hexp.
    subst.
    apply Source.SeInput.
  - inversion Hexp.
    subst.
    unfold Source.var_of_exp in Hnin.
    simpl in Hnin.
    apply Source.SeVar.
    simpl.
    apply Dict.maps_to_not_removed; [ assumption | ].
    intros Heq.
    apply Hnin.
    left.
    assumption.
  - inversion Hexp.
    subst.
    apply Source.SeBinop.
    + apply IH1; [ | assumption ].
      pose proof (Source.var_of_exp_not_in_binop e1 e2 name op) as [ H _ ]; assumption.
    + apply IH2; [ | assumption ].
      pose proof (Source.var_of_exp_not_in_binop e1 e2 name op) as [ _ H ]; assumption.
Qed.

Definition evaluable_equations (s: Target.stack) (l: list Source.equation): Prop :=
  Forall (fun eq => exists v: Target.value, Target.sem_exp s (translate_exp (snd eq)) v) l.

Lemma Forall_impl_in {A: Type} (P Q: A -> Prop) (l: list A):
  (forall a : A, In a l -> P a -> Q a) ->
  Forall P l -> Forall Q l.
Proof.
  intros H Hforall.
  induction l as [ | x l ]; [ constructor | ].
  constructor.
  - apply H.
    + left.
      reflexivity.
    + apply Forall_inv with (l := l).
      assumption.
  - apply IHl.
    + intros a Hin HPa.
      apply H; [ | assumption ].
      right.
      assumption.
    + apply Forall_inv_tail with (a := x).
      assumption.
Qed.

Lemma ordered_equations_are_evaluable (h: Source.history) (l: list Source.equation):
  (Forall (fun eq =>
      exists (v': Source.value),
      Dict.maps_to (fst eq) v' h /\ Source.sem_exp h (snd eq) v'
    ) l
  ) ->
  Ordered.t (LustreOrdered.equations_to_dag l) -> evaluable_equations (translate_history h) l.
Proof.
  intros Hhist Hord.
  remember (LustreOrdered.equations_to_dag l) as dag.
  revert l Hhist Heqdag.
  induction Hord as [ | x l' | x lx l' ]; intros l Hhist Heqdag.
  - symmetry in Heqdag.
    apply LustreOrdered.dag_nil in Heqdag.
    rewrite Heqdag.
    constructor.
  - destruct l as [ | eq l ]; [ constructor | ].
    simpl in Heqdag.
    destruct eq as [ eq_left eq_right ].
    inversion Heqdag.
    subst.
    symmetry in H2.
    apply Source.exp_no_var_is_evaluable with (h := h) in H2 as [ c Hc ].
    constructor.
    + exists (translate_value c).
      apply correctness_exp.
      apply Source.sem_eval_exp.
      assumption.
    + apply Forall_inv_tail in Hhist.
      apply Forall_impl with (P := fun eq => exists v', Dict.maps_to (fst eq) v' h /\ Source.sem_exp h (snd eq) v'); [ | assumption ].
      intros (name, exp) [ v' [ Hmaps Hsem ] ].
      exists (translate_value v').
      apply correctness_exp.
      assumption.
  - destruct l as [ | eq l ]; [ constructor | ].
    simpl in Heqdag.
    destruct eq as [ eq_left eq_right ].
    inversion Heqdag.
    subst.
    constructor.
    + assert (Forall (fun v => Dict.is_in v h) (Source.var_of_exp eq_right)) as Hvars.
      * apply Forall_impl_in with (P := fun y => exists ly, In (y, ly) (LustreOrdered.equations_to_dag l)); [ | assumption ].
        intros name Hin [ vars Hvars ].
        apply Forall_inv in Hhist as [ v' [ Hmaps Hsem ] ].
        apply Source.sem_eval_exp in Hsem.
        pose proof (Source.exp_evaluable_have_evaluable_vars _ _ _ Hsem) as H'.
        apply Forall_forall with (x := name) in H'; assumption.
      * pose proof (Source.exp_with_evaluable_vars_is_evaluable _ _ Hvars) as [ c Hc ].
        exists (translate_value c).
        apply correctness_exp.
        apply Source.sem_eval_exp.
        assumption.
    + apply Forall_inv_tail in Hhist.
      apply Forall_impl with (P := fun eq => exists v', Dict.maps_to (fst eq) v' h /\ Source.sem_exp h (snd eq) v'); [ | assumption ].
      intros (name, exp) [ v' [ Hmaps Hsem ] ].
      exists (translate_value v').
      apply correctness_exp.
      assumption.
Qed.

Lemma translation_ordered_body (body: list Source.equation) (h: Source.history):
  Ordered.t (LustreOrdered.equations_to_dag body) ->
  (Forall (fun eq =>
      exists (v': Source.value),
      Dict.maps_to (fst eq) v' h /\ Source.sem_exp h (snd eq) v'
  ) body ) ->
  Forall (fun '(name, exp) => exists (v: Target.value), Target.sem_exp (translate_history h) (translate_exp exp) v) body.
Proof.
  intros H Hhist.
  induction body; [ constructor | ].
  constructor.
  - destruct a.
    apply ordered_equations_are_evaluable with (h := h) in H; [ | assumption ].
    apply Forall_inv in H.
    destruct H as [ c Hc ].
    simpl in *.
    exists c.
    assumption.
  - destruct a.
    simpl in H.
    apply IHbody.
    + apply Ordered.cons in H.
      assumption.
    + apply Forall_inv_tail in Hhist.
      assumption.
Qed.

Lemma translation_history_element_removal (h: Source.history) (name: ident):
  Dict.remove name (translate_history h) = translate_history (Dict.remove name h).
Proof.
  apply Dict.equivalence_is_eq.
  destruct h as [ l Hsort ].
  split.
  - intros i x H.
    unfold Dict.map, Dict.maps_to, Dict.remove, Dict.find in *.
    simpl in *.
    induction l as [ | (j, y) l IH ]; [ discriminate | ].
    simpl in *.
    destruct (name =? j) eqn: Heq.
    + apply PeanoNat.Nat.eqb_eq in Heq.
      subst.
      assumption.
    + apply PeanoNat.Nat.eqb_neq in Heq.
      simpl in *.
      destruct (i =? j) eqn: Heq'; [ assumption | ].
      apply IH.
      * apply Sorted.cons in Hsort.
        assumption.
      * apply PeanoNat.Nat.eqb_neq in Heq'.
        assumption.
  - intros i x H.
    unfold Dict.map, Dict.maps_to, Dict.remove, Dict.find in *.
    simpl in *.
    induction l as [ | (j, y) l IH ]; [ discriminate | ].
    simpl in *.
    destruct (name =? j) eqn: Heq.
    + apply PeanoNat.Nat.eqb_eq in Heq.
      subst.
      assumption.
    + apply PeanoNat.Nat.eqb_neq in Heq.
      simpl in *.
      destruct (i =? j) eqn: Heq'; [ assumption | ].
      apply IH.
      * apply Sorted.cons in Hsort.
        assumption.
      * apply PeanoNat.Nat.eqb_neq in Heq'.
        assumption.
Qed.

Lemma correctness_translation_equation (h: Source.history) (name: ident) (exp: Source.exp) (v: Source.value):
  Source.sem_exp h exp v ->
  Dict.maps_to name v h ->
  ~ In name (Source.var_of_exp exp) ->
  Target.sem_stmt (translate_history (Dict.remove name h)) (translate_equation (name, exp)) (translate_history h).
Proof.
  intros Hexp Hmaps Hnin.
  unfold translate_equation.
  simpl.
  rewrite Dict.remove_then_add_same_elt with (i := name) (x := translate_value v).
  - rewrite translation_history_element_removal.
    apply Target.SeAssign.
    apply correctness_exp.
    apply sem_exp_without_useless_var; assumption.
  - apply Dict.maps_to_map.
    assumption.
Qed.

Theorem correctness_node (n: LustreOrdered.node_ordered) (m: Target.method) (h: Source.history) (v: Stream.t Source.const):
  (forall (i: ident), Dict.is_in i h <-> In i (map fst (Source.n_body (LustreOrdered.node_ordered_is_node n)))) ->
  (Forall (fun eq =>
      exists (v': Source.value),
      Dict.maps_to (fst eq) v' h /\ Source.sem_exp h (snd eq) v'
    ) (Source.n_body (LustreOrdered.node_ordered_is_node n))
  ) ->
    Target.sem_stmt (Dict.empty _) (Target.m_body (translate_node n)) (translate_history h).
Proof.
  intros Hhist Hsource.
  destruct n.
  destruct node_ordered_is_node.
  simpl in *.
  clear n_assigned_out n_inputs_equations n_no_einputs_in_other.
  revert h Hhist Hsource.
  induction n_body as [ | (eq_left, eq_right) n_body IH ]; intros h Hhist Hsource.
  - simpl.

    assert (h = Dict.empty _).
    { apply Dict.no_element_is_empty.
      destruct h as [ h_elements Hsort ].
      simpl.
      destruct h_elements as [ | (i, x) h_elements ]; [ reflexivity | ].
      exfalso.
      apply Hhist with (i := i).
      exists x.
      unfold Dict.maps_to, Dict.find.
      simpl.
      rewrite PeanoNat.Nat.eqb_refl.
      reflexivity. }

    subst.
    unfold translate_node_body; simpl.
    apply Target.SeNop.
  - apply Ordered.cons in ordered as H.
    apply Ordered.cons in ordered as ordered_inner_body.
    fold LustreOrdered.equations_to_dag in ordered_inner_body.
    apply translation_ordered_body with (h := h) in ordered as Htrans; [ | assumption ].

    assert (incl (map fst n_body) (map fst n_vars)) as Hincl.
    { intros x Hx.
      apply n_assigned_vars_are_vars.
      right.
      assumption. }

    apply Forall_inv_tail in Hsource as Hsource_tail.

    pose (Dict.remove eq_left h) as hprev.
    pose proof (IH Hincl ordered_inner_body hprev) as IHprev.
    unfold translate_node_body.
    simpl.
    apply Forall_inv in Hsource.
    destruct Hsource as [ v' [ Hv'1 Hv'2 ] ].
    apply Forall_inv in Htrans as [ w Hw ].
    apply Target.SeSeq with (s2 := translate_history hprev).
    2: { unfold translate_equation, hprev.
      simpl.
      apply correctness_translation_equation with (v := v'); [ assumption | assumption | ].
      apply Ordered.var_not_need_itself in ordered.
      assumption. }

    apply IHprev.
    * intros i.
      split.
      -- intros [ x Hix ].
         unfold hprev in Hix.
         apply Dict.maps_to_with_removal in Hix as Hih.
         apply Dict.maps_to_imp_is_in in Hih.
         specialize (Hhist i) as Hi.
         destruct Hi as [ Hi1 Hi2].
         specialize (Hi1 Hih) as [ Heq | Hin ]; [ | assumption ].
         exfalso.
         simpl in Heq.
         subst.
         apply Dict.removed_element_not_in with (i := i) (d := h).
         exists x.
         assumption.
      -- intros Hi.
         specialize (Hhist i) as Hhisti.
         destruct Hhisti as [ Hi1 Hi2].
         unfold hprev.
         destruct (PeanoNat.Nat.eq_dec i eq_left).
         ++ subst.
            exfalso.
            apply Ordered.vars_no_dups in ordered.
            apply ordered.
            rewrite <- LustreOrdered.dag_names.
            assumption.
         ++ specialize (Hi2 (in_cons _ _ _ Hi)).
            destruct Hi2 as [ x Hx ].
            apply Dict.maps_to_not_removed with (j := eq_left) in Hx; [ | assumption ].
            exists x.
            assumption.
    * apply Forall_forall.
      intros (i, x) Hin.
      apply Forall_forall with (x := (i, x)) in Hsource_tail as Hix; [ | assumption ].
      destruct Hix as [ w' [ Hw'1 Hw'2 ] ].
      exists w'.
      split.
      -- simpl in *.
         unfold hprev.
         destruct (PeanoNat.Nat.eq_dec i eq_left).
         ++ subst.
            exfalso.
            apply Ordered.vars_no_dups in ordered.
            apply ordered.
            rewrite <- LustreOrdered.dag_names.
            apply in_map with (f := fst) in Hin.
            assumption.
         ++ apply Dict.maps_to_not_removed; assumption.
      -- simpl in *.
         unfold hprev.
         apply sem_exp_without_useless_var; [ assumption | ].
         apply Ordered.vars_coherence with (l := LustreOrdered.equations_to_dag n_body) (y := i) (lx := Source.var_of_exp eq_right); [ assumption | ].
         apply in_map with (f := fun '(i, x) => (i, Source.var_of_exp x)) in Hin.
         rewrite LustreOrdered.equations_to_dag_is_map.
         assumption.
Qed.
