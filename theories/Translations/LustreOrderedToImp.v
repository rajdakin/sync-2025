From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require LustreOrdered Imp.

Module Source := LustreOrdered.
Module Target := Imp.


Definition translate_type (ty: Source.type): Target.type :=
  match ty with
  | Source.Lustre.TVoid => Target.TVoid
  | Source.Lustre.TBool => Target.TBool
  | Source.Lustre.TInt => Target.TInt
  end.

Definition translate_const {ty} (c: Source.const ty): Target.const (translate_type ty) :=
  match c with
  | Source.Lustre.CVoid => Target.CVoid
  | Source.Lustre.CBool b => Target.CBool b
  | Source.Lustre.CInt n => Target.CInt n
  end.

Definition translate_binder (b: Source.binder): Target.binder :=
  (fst b, translate_type (snd b)).

Definition translate_unop {ty tout} (op: Source.unop ty tout): Target.unop (translate_type ty) (translate_type tout) :=
  match op with
  | Source.Lustre.Uop_not => Target.Uop_not
  | Source.Lustre.Uop_neg => Target.Uop_neg
  end.

Definition translate_binop {ty1 ty2 tout} (op: Source.binop ty1 ty2 tout):
    match op with Source.Lustre.Bop_and | Source.Lustre.Bop_or => False | _ => True end ->
    Target.binop (translate_type ty1) (translate_type ty2) (translate_type tout) :=
  match op with
  | Source.Lustre.Bop_and => fun f => False_rect _ f
  | Source.Lustre.Bop_or => fun f => False_rect _ f
  | Source.Lustre.Bop_xor => fun _ => Target.Bop_xor
  | Source.Lustre.Bop_plus => fun _ => Target.Bop_plus
  | Source.Lustre.Bop_minus => fun _ => Target.Bop_minus
  | Source.Lustre.Bop_mult => fun _ => Target.Bop_mult
  | Source.Lustre.Bop_div => fun _ => Target.Bop_div
  | Source.Lustre.Bop_eq => fun _ => Target.Bop_eq
  | Source.Lustre.Bop_lt => fun _ => Target.Bop_lt
  | Source.Lustre.Bop_le => fun _ => Target.Bop_le
  | Source.Lustre.Bop_gt => fun _ => Target.Bop_gt
  | Source.Lustre.Bop_ge => fun _ => Target.Bop_ge
  end.

Fixpoint translate_value {ty} (v: Source.value ty): Target.value (translate_type ty) :=
  match v with
  | Source.Lustre.VConst c => Target.VConst (translate_const c)
  | Source.Lustre.VInput b => Target.VInput (translate_binder b)
  | Source.Lustre.VUnop op v => Target.VUnop (translate_unop op) (translate_value v)
  | Source.Lustre.VBinop op v1 v2 =>
      (match op in Source.Lustre.binop ty1 ty2 tout
                return Target.value (translate_type ty1) -> Target.value (translate_type ty2) -> Target.value (translate_type tout) with
      | Source.Lustre.Bop_and => fun v1 v2 =>
          match v1 with
          | Target.VConst (Target.CBool false) => Target.VConst (Target.CBool false)
          | Target.VConst (Target.CBool true) => v2
          | _ => Target.VBAnd v1 v2
          end
      | Source.Lustre.Bop_or => fun v1 v2 =>
          match v1 with
          | Target.VConst (Target.CBool false) => v2
          | Target.VConst (Target.CBool true) => Target.VConst (Target.CBool true)
          | _ => Target.VBOr v1 v2
          end
      | op => fun v1 v2 => Target.VBinop (translate_binop op I) v1 v2
      end) (translate_value v1) (translate_value v2)
  | Source.Lustre.VIfte v1 v2 v3 => Target.VIfte (translate_value v1) (translate_value v2) (translate_value v3)
  end.

Fixpoint translate_exp {ty} (e: Source.exp ty): Target.exp (translate_type ty) :=
  match e with
  | Source.Lustre.EConst c => Target.EConst (translate_const c)
  | Source.Lustre.EInput b => Target.EInput (translate_binder b)
  | Source.Lustre.EVar b => Target.EVar (translate_binder b)
  | Source.Lustre.EUnop op e => Target.EUnop (translate_unop op) (translate_exp e)
  | Source.Lustre.EBinop op e1 e2 =>
      (match op in Source.Lustre.binop ty1 ty2 tout return Source.exp ty1 -> Source.exp ty2 -> Target.exp (translate_type tout) with
      | Source.Lustre.Bop_and => fun e1 e2 => Target.EBAnd (translate_exp e1) (translate_exp e2)
      | Source.Lustre.Bop_or => fun e1 e2 => Target.EBOr (translate_exp e1) (translate_exp e2)
      | op => fun e1 e2 => Target.EBinop (translate_binop op I) (translate_exp e1) (translate_exp e2)
      end) e1 e2
  | Source.Lustre.EIfte e1 e2 e3 => Target.EIfte (translate_exp e1) (translate_exp e2) (translate_exp e3)
  end.

Definition translate_equation (eq: Source.equation): Target.stmt :=
  Target.SAssign (fst eq, translate_type (projT1 (snd eq))) (translate_exp (projT2 (snd eq))).

Definition translate_history (h: Source.history): Target.stack :=
  Dict.map (fun x => existT Target.value (translate_type (projT1 x)) (translate_value (Stream.hd (projT2 x)))) h.

Definition translate_node_body (body: list Source.equation): Target.stmt :=
  fold_right (fun acc x => Target.SSeq x acc) Target.SNop (List.map translate_equation body).

Lemma lustre_assignment_is_substmt (n: Source.node_ordered) (name: ident) (ty: Source.type) (exp: Source.exp ty):
  let body := Source.Lustre.n_body (Source.node_ordered_is_node n) in
  In (name, existT Source.exp ty exp) body ->
  Target.is_substmt (Target.SAssign (name, translate_type ty) (translate_exp exp)) (translate_node_body body) = true.
Proof.
  destruct n.
  destruct node_ordered_is_node as [].
  unfold Source.Lustre.n_body in *.
  simpl in *.
  intros Hin.
  clear n_assigned_out n_inputs_equations n_no_einputs_in_other.
  induction n_body as [ | (eq_left, (ty', eq_right)) body IH ]; [ inversion Hin | ].
  simpl.
  apply Bool.orb_true_intro.
  destruct Hin as [ Heq | Hin ].
  - injection Heq as eql eqt eqr.
    subst.
    apply Source.sig2T_eq_type in eqr.
    subst.
    right.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite Target.exp_eqb_refl.
    reflexivity.
  - left.
    apply IH.
    + intros i Hi.
      pose proof (in_cons (eq_left, ty') _ _ Hi) as H.
      apply n_assigned_vars_are_vars in H.
      assumption.
    + apply Ordered.cons in ordered.
      assumption.
    + assumption.
Qed.

Lemma in_map_fstsnd {A B} {C : B -> Type} (y: A * B) (xs: list (A * sigT C)):
  In y (List.map (fun '(x, existT _ y _) => (x, y)) xs) ->
    exists ys, In (fst y, existT C (snd y) ys) xs.
Proof.
  induction xs as [| x xs IHxs ].
  { intros []. }

  intros [ Heq | HIn ].
  - subst.
    destruct x as [ a [ b c ] ].
    cbn in *.
    exists c.
    left.
    reflexivity.
  - destruct (IHxs HIn) as [ ys HIn' ].
    exists ys.
    right.
    assumption.
Qed.

Definition translate_node (n: Source.node_ordered): Target.method.
Proof.
  pose n as n'.
  destruct n.
  destruct node_ordered_is_node as [].
  simpl in *.

  refine ({|
    Target.m_name := n_name;

    Target.m_in := map translate_binder n_in;
    Target.m_out := translate_binder n_out;
    Target.m_vars := map translate_binder n_vars;

    Target.m_body := translate_node_body n_body
  |}).

  apply in_map_fstsnd in n_assigned_out as Hexp.
  destruct Hexp as [ exp Hexp ].
  exists (translate_exp exp).
  replace n_body with (Source.Lustre.n_body (Source.node_ordered_is_node n')); [ | reflexivity ].
  apply lustre_assignment_is_substmt.
  assumption.
Defined.


(** Lemmas *)

Lemma correctness_exp (h: Source.history) {ty} (e: Source.exp ty) (out: Source.value ty):
  Source.Lustre.sem_exp h e out ->
    Target.sem_exp (translate_history h) (translate_exp e) (translate_value out).
Proof.
  induction 1 as [| | | |h ty1 ty2 tout op e1 e2 v1 v2 H1 IH1 H2 IH2|].

  - (* EConst *)
    apply Target.SeConst.

  - (* EInput *)
    apply Target.SeInput with (b := translate_binder b).

  - (* EVar *)
    apply Target.SeVar with (b := translate_binder b); simpl.

    exact (Dict.maps_to_map _ _ _ _ H).

  - (* EUnop *)
    simpl.
    apply Target.SeUnop.
    assumption.

  - (* EBinop *)
    simpl.

    destruct op; try solve [apply Target.SeBinop; assumption].
    all: clear H1 H2.
    all: remember (translate_history h) as th eqn:eqh.
    all: remember (translate_exp e1) as te1 eqn:eqe1.
    all: remember (translate_exp e2) as te2 eqn:eqe2.
    all: remember (translate_value v1) as tv1 eqn:eqv1.
    all: remember (translate_value v2) as tv2 eqn:eqv2.
    all: clear h e1 e2 v1 v2 eqh eqe1 eqe2 eqv1 eqv2.
    1,2: destruct (Target.value_inv tv1) as [ [ [ [ [ [
      (c' & ->) | (b' & eq1 & ->) ] | (tin & op & v1' & ->) ] | (e & v1' & v2' & ->) ] | (e & v1' & v2' & ->) ] |
      (ty1 & ty2 & op & v1' & v2' & ->) ] | (eb & et & ef & ->) ].
    2: destruct b'; cbn in eq1; subst t.
    4,5: rewrite (Eqdep_dec.UIP_dec Target.type_dec _ eq_refl) in *.
    2-7: apply Target.SeBAndDefer; try assumption; discriminate.
    3: destruct b'; cbn in eq1; subst t.
    5,6: rewrite (Eqdep_dec.UIP_dec Target.type_dec _ eq_refl) in *.
    3-8: apply Target.SeBOrDefer; try assumption; discriminate.
    1,2: destruct (Target.const_inv c') as [ [ (e & [|] & ->) | (f & _) ] | (f & _) ]; try discriminate f.
    1-4: rewrite (Eqdep_dec.UIP_dec Target.type_dec _ eq_refl) in *.
    1: apply Target.SeBAndConstT; assumption.
    1: apply Target.SeBAndConstF; assumption.
    1: apply Target.SeBOrConstT; assumption.
    1: apply Target.SeBOrConstF; assumption.

  - (* EIfte *)
    simpl.
    apply Target.SeIfte; assumption.
Qed.

Lemma sem_exp_without_useless_var (h: Source.history) (name: ident) {ty} (e: Source.exp ty) (v: Source.value ty):
  Source.Lustre.sem_exp h e v ->
  (forall tyv, ~ In (name, tyv) (Source.var_of_exp e)) ->
    Source.Lustre.sem_exp (Dict.remove name h) e v.
Proof.
  intros Hexp Hnin.
  revert v Hexp.
  induction e as [ ty c | (i, t) | (i, t) | ty tout op e IH | ty1 ty2 tout op e1 IH1 e2 IH2 | ty e1 IH1 e2 IH2 e3 IH3 ]; intros v Hexp.
  - inversion Hexp.
    subst.
    apply Source.sig2T_eq_type in H2, H3.
    subst.
    apply Source.Lustre.SeConst.
  - inversion Hexp.
    subst.
    apply Source.sig2T_eq_type in H4.
    subst.
    apply Source.Lustre.SeInput.
  - inversion Hexp.
    subst.
    apply Source.sig2T_eq_type in H4.
    subst.
    unfold Source.var_of_exp in Hnin.
    simpl in Hnin.
    destruct b.
    injection H3 as ->.
    apply Source.Lustre.SeVar.
    simpl.
    apply Dict.maps_to_not_removed; [ assumption | ].
    intros Heq.
    apply (Hnin t).
    left.
    f_equal.
    assumption.
  - inversion Hexp.
    subst.
    apply Source.sig2T_eq_type in H3, H4, H5.
    apply Source.sig2T_eq_type in H3.
    subst.
    apply Source.Lustre.SeUnop.
    apply IH; assumption.
  - inversion Hexp.
    subst.
    apply Source.sig2T_eq_type in H4, H5, H6, H7.
    do 2 apply Source.sig2T_eq_type in H4.
    subst.
    pose proof (Source.var_of_exp_not_in_binop e1 e2 name op) as tmp.
    pose proof (fun ty => proj1 (tmp Hnin ty)) as H1'.
    pose proof (fun ty => proj2 (tmp Hnin ty)) as H2'.
    clear tmp.
    apply Source.Lustre.SeBinop.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - inversion Hexp.
    subst.
    apply Source.sig2T_eq_type in H0, H1, H4.
    subst.
    pose proof (Source.var_of_exp_not_in_ifte e1 e2 e3 name) as tmp.
    pose proof (fun ty => proj1 (tmp Hnin ty)) as H1'.
    pose proof (fun ty => proj1 (proj2 (tmp Hnin ty))) as H2'.
    pose proof (fun ty => proj2 (proj2 (tmp Hnin ty))) as H3'.
    clear tmp.
    apply Source.Lustre.SeIfte.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

Definition evaluable_equations (s: Target.stack) (l: list Source.equation): Prop :=
  Forall (fun '(name, existT _ ty eq) => exists v: Target.value _, Target.sem_exp s (translate_exp eq) v) l.

Lemma ordered_equations_are_evaluable (h: Source.history) (l: list Source.equation):
  (Forall (fun '(name, existT _ ty eq) =>
      exists (v': Stream.t (Source.value _)),
      Dict.maps_to name (existT _ ty v') h /\ Source.Lustre.sem_exp h eq (Stream.hd v')
    ) l
  ) ->
  Ordered.t (Source.equations_to_dag l) -> evaluable_equations (translate_history h) l.
Proof.
  intros Hhist Hord.
  remember (Source.equations_to_dag l) as dag.
  revert l Hhist Heqdag.
  induction Hord as [ | x lx l' ls ]; intros l Hhist Heqdag.
  - symmetry in Heqdag.
    apply Source.dag_nil in Heqdag.
    rewrite Heqdag.
    constructor.
  - destruct l as [ | eq l ]; [ constructor | ].
    simpl in Heqdag.
    destruct eq as [ eq_left [ ty eq_right ] ].
    inversion Heqdag.
    subst.
    constructor.
    + assert (Forall (fun v => Source.Lustre.in_history h v) (Source.var_of_exp eq_right)) as Hvars.
      * apply Source.Forall_impl_in with (P := fun y => exists ly, In (y, ly) (Source.equations_to_dag l)); [ | assumption ].
        intros name Hin [ vars Hvars ].
        apply Forall_inv in Hhist as [ v' [ Hmaps Hsem ] ].
        apply Source.Lustre.sem_eval_exp in Hsem.
        pose proof (Source.Lustre.exp_evaluable_have_evaluable_vars _ _ _ Hsem) as H'.
        apply Forall_forall with (x := name) in H'; assumption.
      * pose proof (Source.Lustre.exp_with_evaluable_vars_is_evaluable _ _ Hvars) as [ c Hc ].
        exists (translate_value c).
        apply correctness_exp.
        apply Source.Lustre.sem_eval_exp.
        assumption.
    + apply Forall_inv_tail in Hhist.
      refine (Forall_impl _ _ Hhist).
      intros (name, (tyv, exp)) [ v' [ Hmaps Hsem ] ].
      exists (translate_value (Stream.hd v')).
      apply correctness_exp.
      assumption.
Qed.

Lemma translation_ordered_body (body: list Source.equation) (h: Source.history):
  Ordered.t (Source.equations_to_dag body) ->
  (Forall (fun '(name, existT _ ty eq) =>
      exists (v': Stream.t (Source.value _)),
      Dict.maps_to name (existT _ _ v') h /\ Source.Lustre.sem_exp h eq (Stream.hd v')
  ) body ) ->
  Forall (fun '(name, existT _ ty exp) => exists (v: Target.value _), Target.sem_exp (translate_history h) (translate_exp exp) v) body.
Proof.
  intros H Hhist.
  induction body; [ constructor | ].
  constructor.
  - destruct a.
    apply ordered_equations_are_evaluable with (h := h) in H; [ | assumption ].
    apply Forall_inv in H.
    destruct s.
    destruct H as [ c Hc ].
    simpl in *.
    exists c.
    assumption.
  - destruct a.
    simpl in H.
    apply IHbody.
    + destruct s.
      apply Ordered.cons in H.
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

Lemma correctness_translation_equation (h: Source.history) (name: ident) {ty} (exp: Source.exp ty) (v: Stream.t (Source.value _)):
  Source.Lustre.sem_exp h exp (Stream.hd v) ->
  Dict.maps_to name (existT _ ty v) h ->
  (forall tyv, ~ In (name, tyv) (Source.var_of_exp exp)) ->
  Target.sem_stmt (translate_history (Dict.remove name h)) (translate_equation (name, existT _ _ exp)) (translate_history h).
Proof.
  intros Hexp Hmaps Hnin.
  unfold translate_equation.
  simpl.
  rewrite Dict.remove_then_add_same_elt with (i := name) (x := existT Target.value _ (translate_value (Stream.hd v))).
  - rewrite translation_history_element_removal.
    apply Target.SeAssign.
    apply correctness_exp.
    apply sem_exp_without_useless_var; assumption.
  - apply Dict.maps_to_map with (f := fun x => existT Target.value _ (translate_value (Stream.hd (projT2 x)))) in Hmaps.
    assumption.
Qed.

Lemma correctness_node_under_history_assumptions (n: Source.node_ordered) (h: Source.history):
  (forall (i: ident), Dict.is_in i h <-> In i (map fst (Source.Lustre.n_body (Source.node_ordered_is_node n)))) ->
  (Forall (fun '(n, existT _ ty eq) =>
      exists (v': Stream.t (Source.value _)),
      Dict.maps_to n (existT _ ty v') h /\ Source.Lustre.sem_exp h eq (Stream.hd v')
    ) (Source.Lustre.n_body (Source.node_ordered_is_node n))
  ) ->
  Target.sem_stmt (Dict.empty _) (Target.m_body (translate_node n)) (translate_history h).
Proof.
  intros Hhist Hsource.
  destruct n.
  destruct node_ordered_is_node as [].
  unfold Source.Lustre.n_body in *.
  simpl in *.
  clear n_assigned_out n_inputs_equations n_no_einputs_in_other.
  revert h Hhist Hsource.
  induction n_body as [ | (eq_left, (ty, eq_right)) n_body IH ]; intros h Hhist Hsource.
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
    fold Source.equations_to_dag in ordered_inner_body.
    apply translation_ordered_body with (h := h) in ordered as Htrans; [ | assumption ].

    assert (incl (map (fun '(n, existT _ ty _) => (n, ty)) n_body) n_vars) as Hincl.
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
      intros tyv.
      apply Ordered.var_not_need_itself with (b := tyv) in ordered.
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
            assert (tmp : forall l : list (ident * Source.type * list (ident * Source.type)), map (fun '(y, _, _) => y) l = map fst (map fst l))
             by (clear; induction l as [|[[a b] c] tl IH]; [reflexivity|exact (f_equal _ IH)]).
            rewrite tmp, <- Source.dag_names, map_map.
            assumption.
         ++ specialize (Hi2 (in_cons _ _ _ Hi)).
            destruct Hi2 as [ x Hx ].
            apply Dict.maps_to_not_removed with (j := eq_left) in Hx; [ | assumption ].
            exists x.
            assumption.
    * apply Forall_forall.
      intros (i, (tyv, eq)) Hin.
      apply (fun H => proj1 (Forall_forall _ _) H (i, existT _ tyv eq)) in Hsource_tail as Hix; [ | assumption ].
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
            assert (tmp : forall l : list (ident * Source.type * list (ident * Source.type)), map (fun '(y, _, _) => y) l = map fst (map fst l))
             by (clear; induction l as [|[[a b] c] tl IH]; [reflexivity|exact (f_equal _ IH)]).
            rewrite tmp, <- Source.dag_names, map_map.
            apply in_map with (f := fst) in Hin.
            assumption.
         ++ apply Dict.maps_to_not_removed; assumption.
      -- simpl in *.
         unfold hprev.
         apply sem_exp_without_useless_var; [ assumption | ].
         intros tyv'.
         apply (Ordered.vars_coherence _ i _ tyv _ _ _ ordered).
         rewrite Source.equations_to_dag_is_map.
         apply in_map with (f := fun '(i, existT _ ty e) => (i, ty, Source.var_of_exp e)) in Hin.
         assumption.
Qed.

Theorem correctness_node (n: Source.node_ordered):
  exists h: Source.history,
  Target.sem_stmt (Dict.empty _) (Target.m_body (translate_node n)) (translate_history h).
Proof.
  pose proof (Source.minimal_history (Source.Lustre.n_body (Source.node_ordered_is_node n)) (Source.ordered n)) as ( h & H1 & H2 ).
  exists h.
  apply correctness_node_under_history_assumptions; [ clear H2 | assumption ].
  intros i; specialize (H1 i).
  cbn in H1.
  split.
  - intros [ [ ty s ] Hin ].
    specialize (H1 ty).
    rewrite Hin in H1.
    apply proj1 in H1.
    specialize (H1 eq_refl).
    apply (in_map fst) in H1.
    rewrite map_map in H1.
    exact H1.
  - intros Hin.
    apply Sorted.in_map_fst in Hin.
    destruct Hin as [ [ ty e ] Hin ].
    apply (in_map Source.equation_dest) in Hin as Hin'.
    apply H1 in Hin'.
    destruct (Dict.find i h) as [ [ ty' s ] | ] eqn:Hfind; [ | contradiction Hin' ].
    cbn in Hin'; subst ty'.
    exists (existT _ ty s).
    assumption.
Qed.
