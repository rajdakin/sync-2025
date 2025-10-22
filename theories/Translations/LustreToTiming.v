From Reactive Require Import Base.
From Reactive.Languages Require Lustre LustreTiming.
From Reactive.Datatypes Require Import Sublist Inclusion.

Module Lustre := Lustre.
Module LustreTiming := LustreTiming.


Fixpoint expr_to_raw {ty} (e: Lustre.exp ty): LustreTiming.raw_exp ty :=
  match e with
    | Lustre.EConst c => LustreTiming.Raw_EConst c
    | Lustre.EInput b => LustreTiming.Raw_EInput b
    | Lustre.EVar v => LustreTiming.Raw_EVar v
    | Lustre.EIfte e1 e2 e3 => LustreTiming.Raw_EIfte (expr_to_raw e1) (expr_to_raw e2) (expr_to_raw e3)
    | Lustre.EUnop u e => match u in Lustre.unop tin tout return LustreTiming.raw_exp tin -> LustreTiming.raw_exp tout with
      | Lustre.Uop_neg => fun e => LustreTiming.Raw_EUnop LustreTiming.Uop_neg e
      | Lustre.Uop_not => fun e => LustreTiming.Raw_EUnop LustreTiming.Uop_not e
      | Lustre.Uop_pre => fun e => LustreTiming.Raw_EPre e
      end (expr_to_raw e)
    | Lustre.EBinop b e1 e2 => match b in Lustre.binop ty1 ty2 tout return LustreTiming.raw_exp ty1 -> LustreTiming.raw_exp ty2 -> LustreTiming.raw_exp tout with
      | Lustre.Bop_and => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_and e1 e2
      | Lustre.Bop_or => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_or e1 e2
      | Lustre.Bop_xor => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_xor e1 e2
      | Lustre.Bop_plus => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_plus e1 e2
      | Lustre.Bop_minus => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_minus e1 e2
      | Lustre.Bop_mult => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_mult e1 e2
      | Lustre.Bop_div => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_div e1 e2
      | Lustre.Bop_eq => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_eq e1 e2
      | Lustre.Bop_neq => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_neq e1 e2
      | Lustre.Bop_le => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_le e1 e2
      | Lustre.Bop_lt => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_lt e1 e2
      | Lustre.Bop_ge => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_ge e1 e2
      | Lustre.Bop_gt => fun e1 e2 => LustreTiming.Raw_EBinop LustreTiming.Bop_gt e1 e2
      | Lustre.Bop_arrow => fun e1 e2 => LustreTiming.Raw_EArrow e1 e2
      end (expr_to_raw e1) (expr_to_raw e2)
  end.

Definition translate_expr_aux {ty} (e: Lustre.exp ty) (ident_origin: ident) (pre_binders: list LustreTiming.binder) (pre_equations init_post_equations step_post_equations: list LustreTiming.equation): (
    LustreTiming.comb_exp ty (* init *)
    * LustreTiming.comb_exp ty (* step *)
    * ident (* New identifier origin *)
    * (list LustreTiming.binder) (* Variables created for pre *)
    * (list LustreTiming.equation) (* pre equations *)
    (* Equations to merge with the regular equations *)
    (* for init: 
      prex = undef (a variable initialised later)

      for step:
      prex = eqx (eqx being updated later with the current values)
    *)
    (* Equations NOT to be merged, but can be ordered separately *)
    * (list LustreTiming.equation) (* init_post equations *)
    * (list LustreTiming.equation) (* step_post equations *)
  ) :=
    LustreTiming.raw_to_comb_aux (expr_to_raw e) ident_origin pre_binders pre_equations init_post_equations step_post_equations.


Fixpoint translate_equations (eqs: list Lustre.equation) (ident_origin: ident): (
    list LustreTiming.equation (* init *)
    * list LustreTiming.equation (* step *)
    * ident (* New identifier origin *)
    * (list LustreTiming.binder) (* Variables created for pre *)
    * (list LustreTiming.equation) (* pre equations *)
    (* Equations to merge with the regular equations *)
    (* for init: 
      prex = undef (a variable initialised later)

      for step:
      prex = eqx (eqx being updated later with the current values)
    *)
    (* Equations NOT to be merged, but can be ordered separately *)
    * (list LustreTiming.equation) (* init_post equations *)
    * (list LustreTiming.equation) (* step_post equations *)
  ) :=
    match eqs with
      | [] => ([], [], ident_origin, [], [], [], [])
      | eq::eqs => let '(init_eq, step_eq, origin_ident, binders_pre, equations_pre, post_init_equations, post_step_equations) := translate_equations eqs ident_origin in
        let '(ident, existT _ ty e) := eq in
          let '(ei, es, orig, binders, equations_pre, init_equations_post, step_equations_post) := translate_expr_aux e origin_ident binders_pre equations_pre post_init_equations post_step_equations in
            (
              (ident, existT _ ty ei)::init_eq,
              (ident, existT _ ty es)::step_eq,
              orig,
              binders,
              equations_pre,
              init_equations_post,
              step_equations_post
            )
    end.

(* Properties of the translation *)
Lemma raw_binders_conservation {ty} (e: LustreTiming.raw_exp ty) (ident_origin: ident) (pre_binders: list LustreTiming.binder) (pre_equations init_post_equations step_post_equations: list LustreTiming.equation) (ei es: LustreTiming.comb_exp ty) (new_pre_equations new_init_post_equations new_step_post_equations: list LustreTiming.equation) (new_ident_origin: ident) (new_pre_binders: list LustreTiming.binder):
  LustreTiming.raw_to_comb_aux e ident_origin pre_binders pre_equations init_post_equations step_post_equations = (ei, es, new_ident_origin, new_pre_binders, new_pre_equations, new_init_post_equations, new_step_post_equations)
  -> Sublist pre_binders new_pre_binders.
Proof.
  intro translation.
  induction e in ident_origin, pre_binders, pre_equations, init_post_equations, step_post_equations, ei, es, new_pre_equations, new_init_post_equations, new_step_post_equations, new_ident_origin, new_pre_binders, translation |- *.
  - simpl in translation.
    injection translation as <- <- <- <- <- <- <-.
    apply sublist_refl.
  - simpl in translation.
    injection translation as <- <- <- <- <- <- <-.
    apply sublist_refl.
  - simpl in translation.
    injection translation as <- <- <- <- <- <- <-.
    apply sublist_refl.
  - simpl in translation.
    refine (IHe ident_origin pre_binders pre_equations init_post_equations step_post_equations _ _ new_pre_equations new_init_post_equations new_step_post_equations new_ident_origin new_pre_binders _).
Admitted.

Lemma binders_conservation {ty} (e: Lustre.exp ty) (ident_origin: ident) (pre_binders: list LustreTiming.binder) (pre_equations init_post_equations step_post_equations: list LustreTiming.equation) (ei es: LustreTiming.comb_exp ty) (new_pre_equations new_init_post_equations new_step_post_equations: list LustreTiming.equation) (new_ident_origin: ident) (new_pre_binders: list LustreTiming.binder):
  translate_expr_aux e ident_origin pre_binders pre_equations init_post_equations step_post_equations = (ei, es, new_ident_origin, new_pre_binders, new_pre_equations, new_init_post_equations, new_step_post_equations)
  -> Sublist pre_binders new_pre_binders.
Proof.
  unfold translate_expr_aux.
  apply raw_binders_conservation.
Qed.

Definition translate_node (node: Lustre.node) (ident_origin: ident) : LustreTiming.node.
Proof.
  destruct node as [n_name n_in n_out n_locals n_body n_vars n_assigned_vars n_assigned_vars_are_vars n_assigned_out n_out_is_not_an_input n_inputs_equations n_no_einputs_in_other ].

  destruct (translate_equations n_body ident_origin) as [
    [[[[[init_eqs
    step_eqs]
    new_ident_origin]
    pre_binders]
    pre_eqs]
    init_post_eqs]
    step_post_eqs
  ] eqn: translation.

  refine {|
    LustreTiming.n_name := n_name;
    LustreTiming.n_in := n_in;
    LustreTiming.n_out := n_out;
    LustreTiming.n_locals := pre_binders ++ n_locals;
    LustreTiming.n_pre := pre_eqs;
    LustreTiming.n_init := init_eqs ++ init_post_eqs;
    LustreTiming.n_step := step_eqs ++ step_post_eqs;
  |}.

  all: subst n_vars n_assigned_vars.

  - rewrite map_app.
    clear n_no_einputs_in_other n_out_is_not_an_input n_inputs_equations n_assigned_out.
    induction n_body in translation, init_eqs, step_eqs, new_ident_origin, pre_binders, pre_eqs, init_post_eqs, step_post_eqs, ident_origin, n_assigned_vars_are_vars |- *.
    + unfold translate_equations in translation.
      injection translation as <- <- <- <- <- <- <-.
      simpl.
      intros ? [].
    + assert (H := n_assigned_vars_are_vars).
      rewrite map_cons in H.
      apply incl_cons_inv in H.
      destruct H as [ina incl_nbody].
      cbn in translation.
      destruct (translate_equations n_body ident_origin) as [[[[[[init_eqs0 step_eqs0] new_ident_origin0] pre_binders0] pre_eqs0] init_post_eqs0] step_post_eqs0] eqn: eqIh.
      destruct a as [i [ty e]].
      specialize (IHn_body incl_nbody _ _ _ _ _ _ _ _ eqIh).
      unfold Lustre.equation_dest, fst, snd, projT1 in ina.
      clear -translation IHn_body ina.
      destruct (translate_expr_aux e new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei es] orig] binders] equations_pre] init_equations_post] step_equations_post] eqn: eqe.
      injection translation as <- <- <- <- <- <- <-.

      simpl.
      apply incl_cons.
      1: {
        unfold LustreTiming.equation_dest, fst, snd, projT1.
        rewrite !in_app_iff in ina.
        rewrite !in_app_iff.
        tauto.
      }
      clear ina i step_eqs0.
      induction e in n_in, eqe, n_out, n_locals, init_eqs0, new_ident_origin0, pre_binders0, pre_eqs0, init_post_eqs0, step_post_eqs0, IHn_body, ei, es, orig, binders, equations_pre, init_equations_post, step_equations_post |- *.
      * injection eqe as <- <- <- <- <- <- <-.
        simpl.
        assumption.
      * injection eqe as <- <- <- <- <- <- <-.
        simpl.
        assumption.
      * injection eqe as <- <- <- <- <- <- <-.
        simpl.
        assumption.
      * simpl.
      (*
        apply incl_app.
        -- assert (sublist_e := eqe).
           apply binders_conservation in sublist_e.
           apply sublist_incl in sublist_e.
           apply incl_app_inv in IHn_body.
           destruct IHn_body as [incl_init inc_post].
           eapply incl_trans_app_r.
           1: apply incl_init.
           eapply incl_trans_app_r.
           1: apply incl_refl.
           eapply incl_trans_app_l.
           1: apply incl_refl.
           assumption.
        -- 
      *)
        refine (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IHn_body).
        destruct u.
        -- unfold translate_expr_aux in eqe.
           simpl in eqe.
           fold @translate_expr_aux in eqe.
           destruct (LustreTiming.raw_to_comb_aux (expr_to_raw e) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0
step_post_eqs0) as [[[[[[]]]]]] eqn: e_unfold.
           fold @translate_expr_aux in e_unfold.
           admit.
        -- admit.
        -- admit.
      * admit.
      * admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - 
        

