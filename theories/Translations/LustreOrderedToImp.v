Set Default Goal Selector "!".

From Stdlib Require Import List Nat String.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require LustreOrdered Imp.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Axioms Identifier.


Module Source := LustreOrdered.
Module Target := Imp.

Definition translate_unop {ty tout} (op: Source.unop ty tout): Target.unop ty tout :=
  match op with
  | Source.Source.Uop_not => Target.Uop_not
  | Source.Source.Uop_neg => Target.Uop_neg
  end.

Definition translate_binop {ty1 ty2 tout} (op: Source.binop ty1 ty2 tout):
    match op with
    | Source.Source.Bop_and | Source.Source.Bop_or => False
    | _ => True end ->
    Target.binop ty1 ty2 tout :=
  match op with
  | Source.Source.Bop_and => fun f => False_rect _ f
  | Source.Source.Bop_or => fun f => False_rect _ f
  | Source.Source.Bop_xor => fun _ => Target.Bop_xor
  | Source.Source.Bop_plus => fun _ => Target.Bop_plus
  | Source.Source.Bop_minus => fun _ => Target.Bop_minus
  | Source.Source.Bop_mult => fun _ => Target.Bop_mult
  | Source.Source.Bop_div => fun _ => Target.Bop_div
  | Source.Source.Bop_eq => fun _ => Target.Bop_eq
  | Source.Source.Bop_neq => fun _ => Target.Bop_neq
  | Source.Source.Bop_lt => fun _ => Target.Bop_lt
  | Source.Source.Bop_le => fun _ => Target.Bop_le
  | Source.Source.Bop_gt => fun _ => Target.Bop_gt
  | Source.Source.Bop_ge => fun _ => Target.Bop_ge
  end.

Fixpoint translate_exp {ty} (e: Source.exp ty): Target.exp ty :=
  match e with
  | Source.Source.EConst _ c => Target.EConst c
  | Source.Source.EVar _ b => Target.EVar b
  | Source.Source.EUnop _ op e => Target.EUnop (translate_unop op) (translate_exp e)
  | Source.Source.EBinop _ op e1 e2 =>
      (match op in Source.Source.binop ty1 ty2 tout
      return Source.exp ty1 -> Source.exp ty2 -> Target.exp tout
      with
      | Source.Source.Bop_and => fun e1 e2 => Target.EBAnd (translate_exp e1) (translate_exp e2)
      | Source.Source.Bop_or => fun e1 e2 => Target.EBOr (translate_exp e1) (translate_exp e2)
      | op => fun e1 e2 => Target.EBinop (translate_binop op I) (translate_exp e1) (translate_exp e2)
      end) e1 e2
  | Source.Source.EIfte _ e1 e2 e3 => Target.EIfte (translate_exp e1) (translate_exp e2) (translate_exp e3)
  end.

Definition translate_equation (eq: Source.equation): Target.stmt :=
  Target.SAssign {| binder_name := fst (fst eq); binder_id := snd (fst eq); binder_ty := projT1 (snd eq) |} (translate_exp (projT2 (snd eq))).

Definition translate_node_body (stmt: Target.stmt) (body: list Source.equation): Target.stmt :=
  fold_right (fun x acc => Target.SSeq acc (translate_equation x)) stmt body.

Definition translate_node_init (init: list Source.equation): Target.stmt := translate_node_body Target.SNop init.

Definition translate_node_step (pre: list (binder * (string * ident))) (step: list Source.equation): Target.stmt :=
  translate_node_body (
    fold_right (fun x acc => Target.SSeq acc (Target.SAssign (fst x) (Target.EVar {| binder_name := fst (snd x); binder_id := snd (snd x); binder_ty := binder_ty (fst x) |}))) Target.SNop pre) step.

Lemma lustre_assignment_is_substmt (b: binder) (exp: Source.exp (binder_ty b)):
  forall stmt body,
  In ((binder_name b, binder_id b), existT Source.exp _ exp) body ->
  Target.is_substmt (Target.SAssign b (translate_exp exp)) (translate_node_body stmt body) = true.
Proof.
  intros stmt n_body Hin.
  induction n_body as [ | (eq_left, (ty', eq_right)) body IH ]; [ inversion Hin | ].
  simpl.
  apply Bool.orb_true_intro.
  destruct Hin as [ Heq | Hin ].
  - injection Heq as eql eqt eqr.
    subst.
    simpl_exist_type.
    subst.
    right.
    destruct b as [n i t]; cbn.
    rewrite binder_eqb_refl.
    rewrite Target.exp_eqb_refl.
    reflexivity.
  - left.
    apply (IH Hin).
Qed.

Lemma in_map_fstsnd y xs:
  In y (List.map Source.Source.equation_dest xs) ->
    exists ys, In ((binder_name y, binder_id y), existT Source.exp (binder_ty y) ys) xs.
Proof.
  induction xs as [| x xs IHxs ].
  { intros []. }

  intros [ Heq | HIn ].
  - subst.
    destruct x as [ [ ? ? ] [ b c ] ].
    cbn in *.
    exists c.
    left.
    reflexivity.
  - destruct (IHxs HIn) as [ ys HIn' ].
    exists ys.
    right.
    assumption.
Qed.

Definition translate_node (n: Source.node_ordered): Target.method_pair.
Proof.
  pose n as n'.
  destruct n.
  destruct node_ordered_is_node as [].
  simpl in *.

  refine ({|
    Target.m_name := n_name;

    Target.m_in := n_in;
    Target.m_out := n_out;
    Target.m_locals := n_locals;
    Target.m_pre := map fst n_pre;

    Target.m_init := translate_node_init n_init;
    Target.m_step := translate_node_step n_pre n_step
  |}).

  all: intros b Hb.
  1: specialize (Permutation.Permutation_in _ (Permutation.Permutation_sym n_init_vars_all_assigned) (in_or_app _ _ _ (or_introl Hb)))
    as b_assigned.
  2: specialize (Permutation.Permutation_in _ (Permutation.Permutation_sym n_step_vars_all_assigned) (in_or_app _ _ _ (or_introl Hb)))
    as b_assigned.
  all: apply in_map_iff in b_assigned.
  all: destruct b_assigned as [ [ [ n i ] [ ty' exp ] ] [ <- Hexp ] ].
  all: exists (translate_exp exp).
  1: replace n_init with (Source.Source.n_init (Source.node_ordered_is_node n')); [ | reflexivity ].
  2: replace n_step with (Source.Source.n_step (Source.node_ordered_is_node n')); [ | reflexivity ].
  all: apply lustre_assignment_is_substmt.
  all: assumption.
Defined.


(** Lemmas *)

Lemma correctness_exp (h: history) (t: nat) {ty} (e: Source.exp ty) (out: value ty):
  Source.sem_exp h t e out -> Target.sem_exp (project_time h t) (translate_exp e) out.
Proof.
  induction 1 as [ty c loc|tyin tyout op e vin vout sem_e sem_target_e sem_op loc | ty1 ty2 tyout op e1 e2 v1 v2 vout sem_e1 sem_target_e1 sem_e2 sem_target_e2 sem_op loc | ty e1 e2 e3 vb v1 v2 sem_e1 target_sem_e1 sem_e2 target_sem_e2 sem_e3 target_sem_e3|].

  - (* EConst *)
    apply Target.SeConst.
  
  - (* EUnop *)
    simpl.
    apply (Target.SeUnop _ _ _ _ _ sem_target_e).
    destruct op.
    all: simpl; inversion sem_op.
    all: apply sig2T_eq_type in H, H0; subst.
    all: constructor.
  
  - (* EBinop *)
    destruct op.
    all: simpl.
    3-13: apply (Target.SeBinop _ _ _ _ _ _ _ sem_target_e1 sem_target_e2).
    3-13: inversion sem_op.
    3-13: apply sig2T_eq_type in H, H0, H1; subst.
    3-13: constructor.
    1-2: destruct (vbool_dec v1), (vbool_dec v2); subst.
    all: inversion sem_op.
    all: apply sig2T_eq_type in H, H0, H1; subst.
    all: simpl in sem_op.
    all: simpl.
    1-2: apply (Target.SeBAndConstT _ _ _ _ sem_target_e1).
    3-4: apply (Target.SeBAndConstF _ _ _ sem_target_e1).
    3-4: apply (Target.SeBOrConstT _ _ _ sem_target_e1).
    3-4: apply (Target.SeBOrConstF _ _ _ _ sem_target_e1).
    all: assumption.

  - (* EIfte*)
    simpl.
    constructor.
    all: assumption.

  - (* EVar *)
    apply Target.SeVar with (b := b); simpl.

    exact (Dict.maps_to_map _ _ _ _ H).
Qed.

Definition evaluable_equations (s: stack) (l: list Source.equation): Prop :=
  Forall (fun '(name, existT _ ty eq) => exists v: value _, Target.sem_exp s (translate_exp eq) v) l.

(* Lemma ordered_equations_are_evaluable (h: history) (l: list Source.equation) n_in:
  (Forall (fun '(name, existT _ ty eq) =>
      exists (v': Stream.t (value _)),
      Dict.maps_to name (existT _ ty v') h /\ Source.Source.sem_exp h eq (Stream.hd v')
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
    + assert (Forall (fun v => in_history h v) (Source.var_of_exp eq_right)) as Hvars.
      * apply Source.Forall_impl_in with (P := fun y => exists ly, In (y, ly) (Source.equations_to_dag l n_in)); [ | assumption ].
        intros name Hin [ vars Hvars ].
        apply Forall_inv in Hhist as [ v' [ Hmaps Hsem ] ].
        apply Source.Source.sem_eval_exp in Hsem.
        pose proof (Source.exp_evaluable_have_evaluable_vars _ _ _ Hsem) as H'.
        apply Forall_forall with (x := name) in H'; assumption.
      * pose proof (Source.exp_with_evaluable_vars_is_evaluable _ _ Hvars) as [ c Hc ].
        exists (translate_value c).
        apply correctness_exp.
        apply Source.Source.sem_eval_exp.
        assumption.
    + apply Forall_inv_tail in Hhist.
      refine (Forall_impl _ _ Hhist).
      intros (name, (tyv, exp)) [ v' [ Hmaps Hsem ] ].
      exists (translate_value (Stream.hd v')).
      apply correctness_exp.
      assumption.
Qed. *)

(* Lemma translation_ordered_body (body: list Source.equation) (h: history) n_in:
  Ordered.t (Source.equations_to_dag body n_in) ->
  (Forall (fun '(name, existT _ ty eq) =>
      exists (v': Stream.t (value _)),
      Dict.maps_to name (existT _ _ v') h /\ Source.Source.sem_exp h eq (Stream.hd v')
  ) body ) ->
  Forall (fun '(name, existT _ ty exp) => exists (v: value _), Target.sem_exp (translate_history h) (translate_exp exp) v) body.
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
Qed. *)

(* Lemma correctness_translation_equation (h: history) (name: ident) {ty} (exp: Source.exp ty) (v: Stream.t (value _)):
  Source.Source.sem_exp h exp (Stream.hd v) ->
  Dict.maps_to name (existT _ ty v) h ->
  (forall tyv, ~ In (name, tyv) (Source.var_of_exp exp)) ->
  Target.sem_stmt (Dict.remove name h) (translate_equation (name, existT _ _ exp)) h.
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
Qed. *)

(* Lemma correctness_node_under_history_assumptions (n: Source.node_ordered) (h0 h: history):
  (forall (i: ident),
    Dict.is_in i h0 <->
    In i (map fst (Source.Source.n_in (Source.node_ordered_is_node n)))) ->
  Dict.inclusion h0 h ->
  (forall (i: ident),
    Dict.is_in i h <->
    In i (map fst (Source.Source.n_body (Source.node_ordered_is_node n)) ++ map fst (Source.Source.n_in (Source.node_ordered_is_node n)))) ->
  (Forall (fun '(n, existT _ ty eq) =>
      exists (v': Stream.t (value _)),
      Dict.maps_to n (existT _ ty v') h /\ Source.Source.sem_exp h eq (Stream.hd v')
    ) (Source.Source.n_body (Source.node_ordered_is_node n))
  ) ->
  Target.sem_stmt h0 (Target.m_body (translate_node n)) h.
Proof.
  intros Hhist0 Hagree Hhist Hsource.
  destruct n.
  destruct node_ordered_is_node as [].
  unfold Source.Source.n_body in *.
  simpl in *.
  assert (assignments_wd : incl (map Source.Source.equation_dest n_body) (n_out ++ n_locals)).
  { intros x Hx.
    exact (Permutation.Permutation_in x n_vars_all_assigned Hx). }
  clear n_vars_all_assigned n_all_vars_exist.
  revert h Hagree Hhist Hsource.
  induction n_body as [ | (eq_left, (ty, eq_right)) n_body IH ]; intros h Hagree Hhist Hsource.
  - simpl.
    refine (eq_ind _ (fun h => Target.sem_stmt _ _ h) (Target.SeNop _) _ _).
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

    assert (incl (map Source.Source.equation_dest n_body) (n_out ++ n_locals)) as Hincl.
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
    apply Target.SeSeq with (s2 := hprev).
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
Qed. *)

(* Theorem correctness_node (n: Source.node_ordered):
  forall h0: history,
  (forall (i: ident) ty,
    in_history h0 (i, ty) <->
    In (i, ty) (Source.Source.n_in (Source.node_ordered_is_node n))) ->
  exists h: history,
  Target.sem_stmt h0 (Target.m_body (translate_node n)) h.
Proof.
  intros h0 Hh0.
  pose proof (Source.minimal_history (Source.Source.n_body (Source.node_ordered_is_node n)) _ _ Hh0 (Source.ordered n)) as ( h & H1 & H2 & H3 ).
  exists h.
  assert (Hh0' : forall i, Dict.is_in i h0 <-> In i (map fst (Source.Source.n_in (Source.node_ordered_is_node n)))).
  { clear - Hh0; intros i; specialize (Hh0 i); split.
    - intros [[ty s] H]; refine (in_map _ _ _ (proj1 (Hh0 ty) _)).
      unfold in_history, in_history.
      rewrite H; exact eq_refl.
    - intros H; apply in_map_iff in H; destruct H as [[i' ty] [<- H]].
      apply Hh0 in H.
      unfold in_history, in_history in H.
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
Qed. *)
