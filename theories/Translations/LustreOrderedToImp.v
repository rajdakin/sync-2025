Set Default Goal Selector "!".

From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require LustreOrdered Imp.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Axioms Identifier.

From Stdlib Require Import List Nat.


Module Source := LustreOrdered.
Module Target := Imp.

Definition translate_unop {ty tout} (op: Source.unop ty tout): Target.unop ty tout :=
  match op with
  | Source.Lustre.Uop_not => Target.Uop_not
  | Source.Lustre.Uop_neg => Target.Uop_neg
  | Source.Lustre.Uop_pre => ABORT_FIXME _ tt
  end.

Definition translate_binop {ty1 ty2 tout} (op: Source.binop ty1 ty2 tout):
    match op with Source.Lustre.Bop_and | Source.Lustre.Bop_or => False | _ => True end ->
    Target.binop ty1 ty2 tout :=
  match op with
  | Source.Lustre.Bop_and => fun f => False_rect _ f
  | Source.Lustre.Bop_or => fun f => False_rect _ f
  | Source.Lustre.Bop_xor => fun _ => Target.Bop_xor
  | Source.Lustre.Bop_plus => fun _ => Target.Bop_plus
  | Source.Lustre.Bop_minus => fun _ => Target.Bop_minus
  | Source.Lustre.Bop_mult => fun _ => Target.Bop_mult
  | Source.Lustre.Bop_div => fun _ => Target.Bop_div
  | Source.Lustre.Bop_eq => fun _ => Target.Bop_eq
  | Source.Lustre.Bop_neq => fun _ => Target.Bop_neq
  | Source.Lustre.Bop_lt => fun _ => Target.Bop_lt
  | Source.Lustre.Bop_le => fun _ => Target.Bop_le
  | Source.Lustre.Bop_gt => fun _ => Target.Bop_gt
  | Source.Lustre.Bop_ge => fun _ => Target.Bop_ge
  | Source.Lustre.Bop_arrow => fun _ => ABORT_FIXME _ tt
  end.

Fixpoint translate_value {ty} (v: Source.value ty): Target.value ty :=
  match v with
  | Source.Lustre.VConst c => Target.VConst c
  | Source.Lustre.VUnop op v => Target.VUnop (translate_unop op) (translate_value v)
  | Source.Lustre.VBinop op v1 v2 =>
      (match op in Source.Lustre.binop ty1 ty2 tout
                return Target.value ty1 -> Target.value ty2 -> Target.value tout with
      | Source.Lustre.Bop_and => fun v1 v2 =>
          match v1 with
          | Target.VConst (CBool false) => Target.VConst (CBool false)
          | Target.VConst (CBool true) => v2
          | _ => Target.VBAnd v1 v2
          end
      | Source.Lustre.Bop_or => fun v1 v2 =>
          match v1 with
          | Target.VConst (CBool false) => v2
          | Target.VConst (CBool true) => Target.VConst (CBool true)
          | _ => Target.VBOr v1 v2
          end
      | op => fun v1 v2 => Target.VBinop (translate_binop op I) v1 v2
      end) (translate_value v1) (translate_value v2)
  | Source.Lustre.VIfte v1 v2 v3 => Target.VIfte (translate_value v1) (translate_value v2) (translate_value v3)
  end.

Fixpoint translate_exp {ty} (e: Source.exp ty): Target.exp ty :=
  match e with
  | Source.Lustre.EConst _ c => Target.EConst c
  | Source.Lustre.EVar _ b => Target.EVar b
  | Source.Lustre.EUnop _ op e => Target.EUnop (translate_unop op) (translate_exp e)
  | Source.Lustre.EBinop _ op e1 e2 =>
      (match op in Source.Lustre.binop ty1 ty2 tout return Source.exp ty1 -> Source.exp ty2 -> Target.exp tout with
      | Source.Lustre.Bop_and => fun e1 e2 => Target.EBAnd (translate_exp e1) (translate_exp e2)
      | Source.Lustre.Bop_or => fun e1 e2 => Target.EBOr (translate_exp e1) (translate_exp e2)
      | op => fun e1 e2 => Target.EBinop (translate_binop op I) (translate_exp e1) (translate_exp e2)
      end) e1 e2
  | Source.Lustre.EIfte _ e1 e2 e3 => Target.EIfte (translate_exp e1) (translate_exp e2) (translate_exp e3)
  end.

Definition translate_equation (eq: Source.equation): Target.stmt :=
  Target.SAssign (fst eq, projT1 (snd eq)) (translate_exp (projT2 (snd eq))).

Definition translate_history (h: Source.history): Target.stack :=
  Dict.map (fun x => existT Target.value  (projT1 x) (translate_value (Stream.hd (projT2 x)))) h.

Definition translate_node_body (body: list Source.equation): Target.stmt :=
  fold_right (fun acc x => Target.SSeq x acc) Target.SNop (List.map translate_equation body).

Lemma lustre_assignment_is_substmt (name: ident) (ty: type) (exp: Source.exp ty):
  forall body,
  In (name, existT Source.exp ty exp) body ->
  Target.is_substmt (Target.SAssign (name, ty) (translate_exp exp)) (translate_node_body body) = true.
Proof.
  intros n_body Hin.
  induction n_body as [ | (eq_left, (ty', eq_right)) body IH ]; [ inversion Hin | ].
  simpl.
  apply Bool.orb_true_intro.
  destruct Hin as [ Heq | Hin ].
  - injection Heq as eql eqt eqr.
    subst.
    simpl_exist_type.
    subst.
    right.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite Target.exp_eqb_refl.
    reflexivity.
  - left.
    apply (IH Hin).
Qed.

Lemma in_map_fstsnd y xs:
  In y (List.map Source.Lustre.equation_dest xs) ->
    exists ys, In (fst y, existT Source.Lustre.exp (snd y) ys) xs.
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

    Target.m_in := n_in;
    Target.m_out := n_out;
    Target.m_vars := n_vars;

    Target.m_body := translate_node_body n_body
  |}).

  intros b Hb.
  specialize (Permutation.Permutation_in _ (Permutation.Permutation_sym n_vars_all_assigned) (in_or_app _ _ _ (or_introl Hb)))
    as b_assigned.
  apply in_map_iff in b_assigned.
  destruct b_assigned as [ [ i [ ty' exp ] ] [ <- Hexp ] ].
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
  induction 1 as [| | |h loc ty1 ty2 tout op e1 e2 v1 v2 H1 IH1 H2 IH2|].

  - (* EConst *)
    apply Target.SeConst.

  - (* EVar *)
    apply Target.SeVar with (b := b); simpl.

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
    1,2: destruct (Target.value_inv tv1) as [ [ [ [ [
      (c' & ->) | (tin & op & v1' & ->) ] | (e & v1' & v2' & ->) ] | (e & v1' & v2' & ->) ] |
      (ty1 & ty2 & op & v1' & v2' & ->) ] | (eb & et & ef & ->) ].
    3,4: rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in *.
    2-6: apply Target.SeBAndDefer; try assumption; discriminate.
    4,5: rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in *.
    3-7: apply Target.SeBOrDefer; try assumption; discriminate.
    1,2: destruct (const_inv c') as [ [ (e & [|] & ->) | (f & _) ] | (f & _) ]; try discriminate f.
    1-4: rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in *.
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
  induction e as [ loc ty c | loc (i, t) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros v Hexp.
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    apply Source.Lustre.SeConst.
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    unfold Source.var_of_exp in Hnin.
    simpl in Hnin.
    destruct b.
    injection H4 as ->.
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
    simpl_exist_type.
    subst.
    apply Source.Lustre.SeUnop.
    apply IH; assumption.
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    pose proof (Source.var_of_exp_not_in_binop loc e1 e2 name op) as tmp.
    pose proof (fun ty => proj1 (tmp Hnin ty)) as H1'.
    pose proof (fun ty => proj2 (tmp Hnin ty)) as H2'.
    clear tmp.
    apply Source.Lustre.SeBinop.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    pose proof (Source.var_of_exp_not_in_ifte loc e1 e2 e3 name) as tmp.
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

Lemma ordered_equations_are_evaluable (h: Source.history) (l: list Source.equation) n_in:
  (Forall (fun '(name, existT _ ty eq) =>
      exists (v': Stream.t (Source.value _)),
      Dict.maps_to name (existT _ ty v') h /\ Source.Lustre.sem_exp h eq (Stream.hd v')
    ) l
  ) ->
  Ordered.t (Source.equations_to_dag l n_in) -> evaluable_equations (translate_history h) l.
Proof.
  intros Hhist Hord.
  unfold Source.equations_to_dag in Hord.
  remember (Source.equations_to_dag_aux l) as dag.
  revert n_in l Hhist Heqdag Hord.
  induction dag as [ | [ [ x lx ] l' ] ls IH ]; intros n_in l Hhist Heqdag Hord.
  - symmetry in Heqdag.
    apply Source.dag_nil in Heqdag.
    rewrite Heqdag.
    constructor.
  - destruct l as [ | eq l ]; [ constructor | ].
    simpl in Heqdag.
    destruct eq as [ eq_left [ ty eq_right ] ].
    injection Heqdag as <- -> -> ->.
    inversion Hord; subst.
    constructor.
    + assert (Forall (fun v => Source.Lustre.in_history h v) (Source.var_of_exp eq_right)) as Hvars.
      * apply Source.Forall_impl_in with (P := fun y => exists ly, In (y, ly) (Source.equations_to_dag l n_in)); [ | assumption ].
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

Lemma translation_ordered_body (body: list Source.equation) (h: Source.history) n_in:
  Ordered.t (Source.equations_to_dag body n_in) ->
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

Lemma correctness_node_under_history_assumptions (n: Source.node_ordered) (h0 h: Source.history):
  (forall (i: ident),
    Dict.is_in i h0 <->
    In i (map fst (Source.Lustre.n_in (Source.node_ordered_is_node n)))) ->
  Dict.inclusion h0 h ->
  (forall (i: ident),
    Dict.is_in i h <->
    In i (map fst (Source.Lustre.n_body (Source.node_ordered_is_node n)) ++ map fst (Source.Lustre.n_in (Source.node_ordered_is_node n)))) ->
  (Forall (fun '(n, existT _ ty eq) =>
      exists (v': Stream.t (Source.value _)),
      Dict.maps_to n (existT _ ty v') h /\ Source.Lustre.sem_exp h eq (Stream.hd v')
    ) (Source.Lustre.n_body (Source.node_ordered_is_node n))
  ) ->
  Target.sem_stmt (translate_history h0) (Target.m_body (translate_node n)) (translate_history h).
Proof.
  intros Hhist0 Hagree Hhist Hsource.
  destruct n.
  destruct node_ordered_is_node as [].
  unfold Source.Lustre.n_body in *.
  simpl in *.
  assert (assignments_wd : incl (map Source.Lustre.equation_dest n_body) (n_out ++ n_locals)).
  { intros x Hx.
    exact (Permutation.Permutation_in x n_vars_all_assigned Hx). }
  clear n_vars_all_assigned.
  revert h Hagree Hhist Hsource.
  induction n_body as [ | (eq_left, (ty, eq_right)) n_body IH ]; intros h Hagree Hhist Hsource.
  - simpl.
    refine (eq_ind _ (fun h => Target.sem_stmt _ _ (translate_history h)) (Target.SeNop _) _ _).
    apply Dict.equivalence_is_eq.
    split; [exact Hagree|].
    intros i x Hix.
    specialize (proj1 (Hhist _) (ex_intro _ x Hix)) as Hix'.
    apply Hhist0 in Hix'.
    destruct Hix' as [x' Hx'].
    apply Hagree in Hx' as H.
    unfold Dict.maps_to in H; rewrite Hix in H.
    injection H as <-.
    exact Hx'.
  - apply Ordered.cons in ordered as H.
    apply Ordered.cons in ordered as ordered_inner_body.
    fold Source.equations_to_dag in ordered_inner_body.
    apply translation_ordered_body with (h := h) in ordered as Htrans; [ | assumption ].

    assert (incl (map Source.Lustre.equation_dest n_body) (n_out ++ n_locals)) as Hincl.
    { intros x Hx.
      apply assignments_wd.
      right.
      assumption. }

    apply Forall_inv_tail in Hsource as Hsource_tail.

    pose (Dict.remove eq_left h) as hprev.
    pose proof (IH ordered_inner_body Hincl hprev) as IHprev.
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
    * intros i x Hi.
      refine (Dict.maps_to_not_removed _ _ _ _ (Hagree _ _ Hi) _).
      intros <-.
      cbn in ordered; refine (Ordered.vars_no_dups _ _ _ _ ordered _).
      rewrite map_app, map_map.
      refine (in_or_app _ _ _ (or_intror _)).
      exact (proj1 (Hhist0 i) (ex_intro _ x Hi)).
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
            assert (tmp : forall l : list (ident * type * list (ident * type)), map (fun '(y, _, _) => y) l = map fst (map fst l))
             by (clear; induction l as [|[[a b] c] tl IH]; [reflexivity|exact (f_equal _ IH)]).
            rewrite tmp, !map_app, <- Source.dag_names, !map_map.
            exact Hi.
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
            assert (tmp : forall l : list (ident * type * list (ident * type)), map (fun '(y, _, _) => y) l = map fst (map fst l))
             by (clear; induction l as [|[[a b] c] tl IH]; [reflexivity|exact (f_equal _ IH)]).
            rewrite tmp, !map_app, <- Source.dag_names, !map_map.
            refine (in_or_app _ _ _ (or_introl (eq_ind _ (In eq_left) (in_map fst _ _ Hin) _ (map_ext _ _ _ _)))).
            intros [[]]; exact eq_refl.
         ++ apply Dict.maps_to_not_removed; assumption.
      -- simpl in *.
         unfold hprev.
         apply sem_exp_without_useless_var; [ assumption | ].
         intros tyv'.
         cbn in ordered.
         apply (Ordered.vars_coherence _ i _ tyv _ _ _ ordered).
         rewrite Source.equations_to_dag_is_map.
         apply in_map with (f := fun '(i, existT _ ty e) => (i, ty, Source.var_of_exp e)) in Hin.
         exact (in_or_app _ _ _ (or_introl Hin)).
Qed.

Theorem correctness_node (n: Source.node_ordered):
  forall h0: Source.history,
  (forall (i: ident) ty,
    Source.in_history h0 (i, ty) <->
    In (i, ty) (Source.Lustre.n_in (Source.node_ordered_is_node n))) ->
  exists h: Source.history,
  Target.sem_stmt (translate_history h0) (Target.m_body (translate_node n)) (translate_history h).
Proof.
  intros h0 Hh0.
  pose proof (Source.minimal_history (Source.Lustre.n_body (Source.node_ordered_is_node n)) _ _ Hh0 (Source.ordered n)) as ( h & H1 & H2 & H3 ).
  exists h.
  assert (Hh0' : forall i, Dict.is_in i h0 <-> In i (map fst (Source.Lustre.n_in (Source.node_ordered_is_node n)))).
  { clear - Hh0; intros i; specialize (Hh0 i); split.
    - intros [[ty s] H]; refine (in_map _ _ _ (proj1 (Hh0 ty) _)).
      unfold Source.in_history, Source.Lustre.in_history.
      rewrite H; exact eq_refl.
    - intros H; apply in_map_iff in H; destruct H as [[i' ty] [<- H]].
      apply Hh0 in H.
      unfold Source.in_history, Source.Lustre.in_history in H.
      unfold Dict.is_in.
      destruct (Dict.find (fst (i', ty)) h0) as [[ty' s]|] eqn:eq; [subst|contradiction H].
      exists (existT _ ty s); exact eq. }
  apply (fun h => correctness_node_under_history_assumptions _ h0 h Hh0'); [ assumption | clear - H2 | assumption ].
  rename H2 into H1.
  intros i; specialize (H1 i).
  cbn in H1.
  split.
  - intros [ [ ty s ] Hin ].
    specialize (H1 ty).
    rewrite Hin in H1.
    apply proj1 in H1.
    specialize (H1 eq_refl).
    apply (in_map fst) in H1.
    rewrite map_app, map_map in H1.
    exact H1.
  - intros Hin.
    unfold Dict.is_in, Dict.maps_to.
    destruct (Dict.find i h) as [ x | ]; [exists x; exact eq_refl|exfalso].
    assert (tmp : forall l, map fst l = map fst (map Source.equation_dest l))
      by (clear; intros l; induction l as [|[? []] ? IH]; [exact eq_refl|exact (f_equal _ IH)]).
    rewrite tmp, <-map_app in Hin; clear tmp.
    apply Sorted.in_map_fst in Hin.
    destruct Hin as [ ty Hin ].
    rewrite <-H1 in Hin; exact Hin.
Qed.
