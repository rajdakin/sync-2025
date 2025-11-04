From Reactive Require Import Base.
From Reactive.Languages Require Lustre LustreTiming.
From Reactive.Datatypes Require Import Inclusion.
From Reactive.Datatypes Require Import PermutationProps.

From Stdlib Require Import Permutation.

Module Lustre := Lustre.
Module LustreTiming := LustreTiming.


Fixpoint expr_to_raw {ty} (e: Lustre.exp ty): LustreTiming.raw_exp ty :=
  match e with
    | Lustre.EConst c => LustreTiming.Raw_EConst c
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

Definition translate_expr {ty} (e: Lustre.exp ty) (ident_origin: ident) (pre_binders: list LustreTiming.binder) (pre_equations init_post_equations step_post_equations: list LustreTiming.equation): (
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
    LustreTiming.raw_to_comb (expr_to_raw e) ident_origin pre_binders pre_equations init_post_equations step_post_equations.

Lemma freshness_translate_expr {ty} {e: Lustre.exp ty} {ei es: LustreTiming.comb_exp ty} {seed0 seed1: ident} {binders pre_binders0 pre_binders1: list LustreTiming.binder} {pre_eqs0 pre_eqs1 init_post0 init_post1 step_post0 step_post1: list LustreTiming.equation}:
  translate_expr e seed0 pre_binders0 pre_eqs0 init_post0 step_post0 = (ei, es, seed1, pre_binders1, pre_eqs1, init_post1, step_post1)
  -> LustreTiming.freshness seed0 (pre_binders0 ++ binders)
  -> LustreTiming.freshness seed1 (pre_binders1 ++ binders).
Proof.
  apply LustreTiming.freshness_raw_to_comb.
Qed.

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


Definition translate_node (node: Lustre.node) : LustreTiming.node.
Proof.
  destruct node as [
    n_loc
    n_name

    n_in
    n_out
    n_locals
    n_body
    
    n_vars
    n_assigned_vars
    
    n_vars_all_assigned
    n_vars_unique
    
    n_seed
    n_seed_always_fresh
  ].

  destruct (translate_equations n_body n_seed) as [
    [[[[[init_eqs
    step_eqs]
    new_seed]
    pre_binders]
    pre_eqs]
    init_post_eqs]
    step_post_eqs
  ] eqn: translation.

  refine {|
    LustreTiming.n_loc := n_loc;
    LustreTiming.n_name := n_name;

    LustreTiming.n_in := n_in;
    LustreTiming.n_out := n_out;
    LustreTiming.n_locals := pre_binders ++ n_locals;
    LustreTiming.n_pre := pre_eqs;
    LustreTiming.n_init := init_eqs ++ init_post_eqs;
    LustreTiming.n_step := step_eqs ++ step_post_eqs;

    LustreTiming.n_seed := new_seed;
  |}.

  all: subst n_vars n_assigned_vars.

  - clear -translation n_vars_all_assigned n_vars_unique n_seed_always_fresh.

    apply NoDup_map_inv in n_vars_unique.

    induction n_body as [ | eq n_body IHn] in translation, n_vars_unique, init_eqs, step_eqs, new_seed, pre_binders, pre_eqs, init_post_eqs, step_post_eqs, n_seed, n_vars_all_assigned, n_out, n_locals, n_seed_always_fresh |- *.
    + unfold translate_equations in translation.
      injection translation as <- <- <- <- <- <- <-.
      simpl.
      destruct n_out, n_locals; simpl in n_vars_all_assigned.
      1: apply perm_nil.
      all: apply Permutation_nil_cons in n_vars_all_assigned.
      all: contradiction.
    + destruct eq as [eq_ident [ty eq_expr]].
      cbn in translation.
      destruct (translate_equations n_body n_seed) as [[[[[[init_eqs0 step_eqs0] new_seed_0] pre_binders0] pre_eqs0] init_post_eqs0] step_post_eqs0] eqn: eq_trans_eq.
      destruct (@translate_expr ty eq_expr new_seed_0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei es] new_seed_bis] binders] equations_pre] init_equations_post] step_equations_post] eqn: eqe.
      injection translation as <- <- <- <- <- <- <-.

      rewrite map_cons in n_vars_all_assigned.
      unfold Lustre.equation_dest at 1, fst, snd, projT1 in n_vars_all_assigned.

      rewrite map_app.
      rewrite map_cons.
      unfold LustreTiming.equation_dest at 2, fst, snd, projT1.

      assert (eq_in_out_locals := n_vars_all_assigned).

      apply (Permutation_in (eq_ident, ty)) in eq_in_out_locals.
      2: left; reflexivity.

      assert (nodup_out_locals := n_vars_unique).

      apply NoDup_app_remove_l in nodup_out_locals.

      assert (vars_assigned_removed := permutation_nodup_remove_cons Lustre.binder_dec _ _ _ n_vars_all_assigned (Permutation_NoDup (Permutation_sym n_vars_all_assigned) nodup_out_locals)).
      rewrite remove_app in vars_assigned_removed.

      simpl.
      rewrite <- Permutation_middle.

      specialize (IHn _ _ vars_assigned_removed).

      assert (vars_unique_remove := NoDup_app_list_remove_r Lustre.binder_dec (eq_ident, ty) _ _ n_vars_unique).
      rewrite remove_app in vars_unique_remove.

      specialize (IHn vars_unique_remove).

      assert (fresh_remove : forall n : nat,
              ~In (iter n next_ident n_seed)
              (map fst (n_in ++
              remove Lustre.binder_dec (eq_ident, ty) n_out ++
              remove Lustre.binder_dec (eq_ident, ty) n_locals))
      ).
      1: intro n.
      1: specialize (n_seed_always_fresh n).
      1: apply (remove_map_notinr Lustre.binder_dec (eq_ident, ty)) in n_seed_always_fresh.
      1: rewrite remove_app in n_seed_always_fresh.
      1: assumption.

      specialize (IHn _ fresh_remove).
      specialize (IHn _ _ _ _ _ _ _ eq_trans_eq).

      clear -IHn eqe eq_in_out_locals nodup_out_locals fresh_remove eq_in_out_locals.

      induction eq_expr in n_in, n_out, n_locals, eq_ident, n_seed, init_eqs0, new_seed_0, pre_binders0, pre_eqs0, init_post_eqs0, step_post_eqs0, ei, es, new_seed_bis, binders, equations_pre, init_equations_post, step_equations_post, eqe, IHn, eq_in_out_locals, nodup_out_locals, fresh_remove, eq_in_out_locals |- *.
      * unfold translate_expr in eqe.
        simpl in eqe.
        injection eqe as <- <- <- <- <- <- <-.
        rewrite map_app in IHn.
        apply Permutation_sym in IHn.
        rewrite Permutation_app_comm in IHn.
        rewrite <- app_assoc in IHn.
        rewrite <- remove_app in IHn.
        apply Permutation_sym in IHn.
        rewrite (Permutation_app_comm n_out).
        rewrite <- app_assoc.
        apply (perm_skip (eq_ident, ty)) in IHn.
        rewrite IHn.
        rewrite Permutation_app_comm.
        rewrite (Permutation_app_comm pre_binders0).
        apply (Permutation_app_tail (l:=_ :: _)).
        apply Permutation_sym.
        apply add_removed.
        1: apply In_app_inv; assumption.
        apply NoDup_app_inv.
        assumption.
      * unfold translate_expr in eqe.
        simpl in eqe.
        injection eqe as <- <- <- <- <- <- <-.
        rewrite map_app in IHn.
        apply Permutation_sym in IHn.
        rewrite Permutation_app_comm in IHn.
        rewrite <- app_assoc in IHn.
        rewrite <- remove_app in IHn.
        apply Permutation_sym in IHn.
        rewrite (Permutation_app_comm n_out).
        rewrite <- app_assoc.
        apply (perm_skip (eq_ident, Lustre.binder_ty b)) in IHn.
        rewrite IHn.
        rewrite Permutation_app_comm.
        rewrite (Permutation_app_comm pre_binders0).
        apply (Permutation_app_tail (l:=_ :: _)).
        apply Permutation_sym.
        apply add_removed.
        1: apply In_app_inv; assumption.
        apply NoDup_app_inv.
        assumption.
      * destruct u.
        -- unfold translate_expr in eqe.
           simpl in eqe.
           destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt eq_expr) new_seed_0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei1 es1] new_seed_bis1] binders1] equations_pre1] init_equations_post1] step_equations_post1] eqn: eqe1.
           injection eqe as <- <- <- <- <- <- <-.

           specialize (IHeq_expr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eqe1 IHn eq_in_out_locals nodup_out_locals fresh_remove).
           exact IHeq_expr.
        -- unfold translate_expr in eqe.
           simpl in eqe.
           destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt eq_expr) new_seed_0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei1 es1] new_seed_bis1] binders1] equations_pre1] init_equations_post1] step_equations_post1] eqn: eqe1.
           injection eqe as <- <- <- <- <- <- <-.

           specialize (IHeq_expr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eqe1 IHn eq_in_out_locals nodup_out_locals fresh_remove).
           exact IHeq_expr.
        -- unfold translate_expr in eqe.
           simpl in eqe.
           destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt eq_expr) new_seed_0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei1 es1] new_seed_bis1] binders1] equations_pre1] init_equations_post1] step_equations_post1] eqn: eqe1.
           injection eqe as <- <- <- <- <- <- <-.

           specialize (IHeq_expr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eqe1 IHn eq_in_out_locals nodup_out_locals fresh_remove).

           simpl.

           unfold LustreTiming.equation_dest at 1 4, fst, snd, projT1.

           apply (Permutation_elt [_] _ n_out).
           simpl.

           (* TODO LATER FLEMME *)
           apply ABORT_FIXME; exact tt.
      * destruct b.
        -- unfold translate_expr in eqe.
           simpl in eqe.
           destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool eq_expr1) new_seed_0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei1 es1] new_seed_bis1] binders1] equations_pre1] init_equations_post1] step_equations_post1] eqn: eqe1.
           destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool eq_expr2) new_seed_bis1 binders1 equations_pre1 init_equations_post1 step_equations_post1) as [[[[[[ei2 es2] new_seed_bis2] binders2] equations_pre2] init_equations_post2] step_equations_post2] eqn: eqe2.
           injection eqe as <- <- <- <- <- <- <-.

           specialize (IHeq_expr1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eqe1 IHn eq_in_out_locals nodup_out_locals fresh_remove).
           rewrite <- map_app in IHeq_expr1.
           apply (perm_remove_app_without_mid Lustre.binder_dec _ _ _ _ _ _ eq_in_out_locals) in IHeq_expr1.
           specialize (IHeq_expr2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eqe2 IHeq_expr1 eq_in_out_locals nodup_out_locals fresh_remove).
           exact IHeq_expr.
    (*
    assert (H := n_vars_all_assigned).
      rewrite map_cons in H.
      apply incl_cons_inv in H.
      destruct H as [ina incl_nbody].
      cbn in translation.
      destruct (translate_equations n_body ident_origin) as [[[[[[init_eqs0 step_eqs0] new_ident_origin0] pre_binders0] pre_eqs0] init_post_eqs0] step_post_eqs0] eqn: eqIh.
      destruct a as [i [ty e]].
      specialize (IHn_body incl_nbody _ _ _ _ _ _ _ _ eqIh).
      unfold Lustre.equation_dest, fst, snd, projT1 in ina.
      clear -translation IHn_body ina.
      destruct (translate_expr e new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei es] orig] binders] equations_pre] init_equations_post] step_equations_post] eqn: eqe.
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
        destruct u.
        all: unfold translate_expr in eqe.
        all: simpl in eqe.
        1-2: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[]]]]]] eqn: e_unfold.
        3: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[]]]]]] eqn: e_unfold.
        all: injection eqe as <- <- <- <- <- <- <-.
        1-2: refine (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e_unfold IHn_body).
        simpl.
        specialize (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e_unfold IHn_body).
        apply incl_app.
        -- apply incl_app_inv in IHe.
          destruct IHe as [incl_init _].
          apply (incl_trans _ _ _ incl_init).
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          do 2 apply incl_tl.
          apply incl_refl.
        -- apply incl_app_inv in IHe.
          destruct IHe as [_ incl_l1].
          unfold LustreTiming.equation_dest, fst, snd, projT1.
          apply incl_cons.
          ++ do 2 (apply in_or_app; right).
              apply in_cons.
              apply in_eq.
          ++ apply (incl_trans _ _ _ incl_l1).
              apply incl_app.
              1: apply incl_appl; apply incl_refl.
              apply incl_appr.
              apply incl_app.
              1: apply incl_appl; apply incl_refl.
              apply incl_appr.
              do 2 apply incl_tl.
              apply incl_refl.
      * simpl.
        destruct b.
        all: unfold translate_expr in eqe.
        all: simpl in eqe.
        1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        1-13: injection eqe as <- <- <- <- <- <- <-.
        1-13: refine (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body)).

        destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        injection eqe as <- <- <- <- <- <- <-.
        simpl.
        specialize (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body)).
        apply incl_app.
        ++ apply incl_app_inv in IHe2.
          destruct IHe2 as [incl_init _].
          apply (incl_trans _ _ _ incl_init).
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          apply incl_refl.
        ++ apply incl_app_inv in IHe2.
          destruct IHe2 as [_ incl_l1].
          apply incl_l1.
      * unfold translate_expr in eqe.
        simpl in eqe.
        destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[? ?] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[? ?] ident_e2] binders_e2] eqs_e2] init_e2] step_e2] eqn: e2_unfold.
        destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e3) ident_e2 binders_e2 eqs_e2 init_e2 step_e2) as [[[[[[]]]]]] eqn: e3_unfold.
        injection eqe as <- <- <- <- <- <- <-.
        refine (IHe3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e3_unfold (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body))). *)
  - apply ABORT_FIXME; exact tt.
    (* clear -translation n_assigned_vars_are_vars.
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
      destruct (translate_expr e new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei es] orig] binders] equations_pre] init_equations_post] step_equations_post] eqn: eqe.
      injection translation as <- <- <- <- <- <- <-.

      simpl.
      clear ina i step_eqs0 init_eqs0.
      induction e in n_in, eqe, n_out, n_locals, new_ident_origin0, pre_binders0, pre_eqs0, init_post_eqs0, step_post_eqs0, IHn_body, ei, es, orig, binders, equations_pre, init_equations_post, step_equations_post |- *.
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
        destruct u.
        all: unfold translate_expr in eqe.
        all: simpl in eqe.
        1-2: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[]]]]]] eqn: e_unfold.
        3: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[]]]]]] eqn: e_unfold.
        all: injection eqe as <- <- <- <- <- <- <-.
        1-2: refine (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e_unfold IHn_body).
        simpl.
        specialize (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e_unfold IHn_body).
        apply incl_cons.
        -- unfold LustreTiming.equation_dest, fst, snd, projT1.
           do 2 (apply in_or_app; right).
           apply in_eq.
        -- apply (incl_trans _ _ _ IHe).
           apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          do 2 apply incl_tl.
          apply incl_refl.
      * destruct b.
        all: unfold translate_expr in eqe.
        all: simpl in eqe.
        1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        1-13: injection eqe as <- <- <- <- <- <- <-.
        1-13: refine (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body)).

        destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        injection eqe as <- <- <- <- <- <- <-.
        simpl.
        specialize (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body)).
        apply IHe2.
      * unfold translate_expr in eqe.
        simpl in eqe.
        destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[? ?] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[? ?] ident_e2] binders_e2] eqs_e2] init_e2] step_e2] eqn: e2_unfold.
        destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e3) ident_e2 binders_e2 eqs_e2 init_e2 step_e2) as [[[[[[]]]]]] eqn: e3_unfold.
        injection eqe as <- <- <- <- <- <- <-.
        refine (IHe3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e3_unfold (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body))). *)
  - apply ABORT_FIXME; exact tt.
    (* clear -translation n_assigned_vars_are_vars.
    rewrite map_app.
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
      destruct (translate_expr e new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[ei es] orig] binders] equations_pre] init_equations_post] step_equations_post] eqn: eqe.
      injection translation as <- <- <- <- <- <- <-.

      simpl.
      apply incl_cons.
      1: {
        unfold LustreTiming.equation_dest, fst, snd, projT1.
        rewrite !in_app_iff in ina.
        rewrite !in_app_iff.
        tauto.
      }
      clear ina i init_eqs0.
      induction e in n_in, eqe, n_out, n_locals, step_eqs0, new_ident_origin0, pre_binders0, pre_eqs0, init_post_eqs0, step_post_eqs0, IHn_body, ei, es, orig, binders, equations_pre, init_equations_post, step_equations_post |- *.
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
        destruct u.
        all: unfold translate_expr in eqe.
        all: simpl in eqe.
        1-2: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[]]]]]] eqn: e_unfold.
        3: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[]]]]]] eqn: e_unfold.
        all: injection eqe as <- <- <- <- <- <- <-.
        1-2: refine (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e_unfold IHn_body).
        simpl.
        specialize (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e_unfold IHn_body).
        apply incl_app.
        -- apply incl_app_inv in IHe.
          destruct IHe as [incl_init _].
          apply (incl_trans _ _ _ incl_init).
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          do 2 apply incl_tl.
          apply incl_refl.
        -- apply incl_app_inv in IHe.
          destruct IHe as [_ incl_l1].
          unfold LustreTiming.equation_dest, fst, snd, projT1.
          apply incl_cons.
          ++ do 2 (apply in_or_app; right).
              apply in_cons.
              apply in_eq.
          ++ apply (incl_trans _ _ _ incl_l1).
              apply incl_app.
              1: apply incl_appl; apply incl_refl.
              apply incl_appr.
              apply incl_app.
              1: apply incl_appl; apply incl_refl.
              apply incl_appr.
              do 2 apply incl_tl.
              apply incl_refl.
      * simpl.
        destruct b.
        all: unfold translate_expr in eqe.
        all: simpl in eqe.
        1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        1-13: injection eqe as <- <- <- <- <- <- <-.
        1-13: refine (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body)).

        destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        injection eqe as <- <- <- <- <- <- <-.
        simpl.
        specialize (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body)).
        apply incl_app.
        ++ apply incl_app_inv in IHe2.
          destruct IHe2 as [incl_init _].
          apply (incl_trans _ _ _ incl_init).
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          apply incl_app.
          1: apply incl_appl; apply incl_refl.
          apply incl_appr.
          apply incl_refl.
        ++ apply incl_app_inv in IHe2.
          destruct IHe2 as [_ incl_l1].
          apply incl_l1.
      * unfold translate_expr in eqe.
        simpl in eqe.
        destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) new_ident_origin0 pre_binders0 pre_eqs0 init_post_eqs0 step_post_eqs0) as [[[[[[? ?] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[? ?] ident_e2] binders_e2] eqs_e2] init_e2] step_e2] eqn: e2_unfold.
        destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e3) ident_e2 binders_e2 eqs_e2 init_e2 step_e2) as [[[[[[]]]]]] eqn: e3_unfold.
        injection eqe as <- <- <- <- <- <- <-.
        refine (IHe3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e3_unfold (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold IHn_body))). *)
  - apply ABORT_FIXME; exact tt.
    (* clear -translation n_assigned_out.
    induction n_out in translation, init_eqs, step_eqs, new_ident_origin, pre_binders, pre_eqs, init_post_eqs, step_post_eqs, ident_origin, n_assigned_out |- *.
    1: apply incl_nil_l.
    apply incl_cons_inv in n_assigned_out.
    destruct n_assigned_out as [a_assigned n_assigned_out].
    apply incl_cons.
    2: refine (IHn_out n_assigned_out _ _ _ _ _ _ _ _ translation).
    clear IHn_out n_out n_assigned_out.
    induction n_body as [ | eq n_body IHn_body] in a, a_assigned, ident_origin, init_eqs, step_eqs, new_ident_origin, pre_binders, pre_eqs, init_post_eqs, step_post_eqs, translation |- *.
    1: contradiction.
    simpl in a_assigned.
    simpl in translation.
    destruct (translate_equations n_body ident_origin) as [[[[[[init_eq step_eq] origin_ident] binders_pre] equations_pre] post_init_equations] post_step_equations] eqn: translate_nbody.
    destruct eq as [i [ty e]].
    destruct (translate_expr e origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[]]]]]] eqn: unfold_translate.
    injection translation as <- <- <- <- <- <- <-.
    unfold Lustre.equation_dest at 1, fst, snd, projT1 in a_assigned.
    simpl.

    destruct a_assigned as [a_dest_eq | a_assigned].
    1: left; assumption.
    right.
    specialize (IHn_body _ a_assigned _ _ _ _ _ _ _ _ translate_nbody).
    rewrite map_app.
    apply in_app_iff.
    rewrite map_app in IHn_body.
    apply in_app_iff in IHn_body.
    destruct IHn_body as [in_init | in_post_init].
    1: left; assumption.
    right.
    clear -unfold_translate in_post_init.
    rename c into init_eq, c0 into step_eq, i0 into new_origin_ident, l into new_binders_pre, l0 into new_equations_pre, l1 into new_post_init_equations, l2 into new_post_step_equations.
    rename unfold_translate into translation.

    induction e in a, origin_ident, binders_pre, equations_pre, post_init_equations, post_step_equations, init_eq, step_eq, new_origin_ident, new_binders_pre, new_equations_pre, new_post_init_equations, new_post_step_equations, translation, in_post_init |- *.
    1-3: unfold translate_expr in translation.
    1-3: simpl in translation.
    1-3: injection translation as <- <- <- <- <- <- <-.
    1-3: assumption.

    + unfold translate_expr in translation.
      destruct u.
      all: simpl in translation.
      1-2: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[]]]]]] eqn: unfold_e.
      1-2: injection translation as <- <- <- <- <- <- <-.
      1-2: refine (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ unfold_e in_post_init).

      destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[]]]]]] eqn: unfold_e.

      injection translation as <- <- <- <- <- <- <-.
      specialize (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ unfold_e in_post_init).
      simpl.
      right.
      assumption.
    + unfold translate_expr in translation.
      destruct b.
      all: simpl in translation.
      1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
      1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
      4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
      4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
      14: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
      14: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
      all: injection translation as <- <- <- <- <- <- <-.
      all: refine (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold in_post_init)).
    + unfold translate_expr in translation.
      simpl in translation.
      destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[? ?] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
      destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[? ?] ident_e2] binders_e2] eqs_e2] init_e2] step_e2] eqn: e2_unfold.
      destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e3) ident_e2 binders_e2 eqs_e2 init_e2 step_e2) as [[[[[[]]]]]] eqn: e3_unfold.
      injection translation as <- <- <- <- <- <- <-.
      refine (IHe3 _ _ _ _ _ _ _ _ _ _ _ _ _ e3_unfold (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold in_post_init))). *)
  - apply ABORT_FIXME; exact tt.
    (* clear -translation n_assigned_out.
    rewrite map_app.
    induction n_out in translation, init_eqs, step_eqs, new_ident_origin, pre_binders, pre_eqs, init_post_eqs, step_post_eqs, ident_origin, n_assigned_out |- *.
    1: apply incl_nil_l.
    apply incl_cons_inv in n_assigned_out.
    destruct n_assigned_out as [a_assigned n_assigned_out].
    apply incl_cons.
    2: refine (IHn_out n_assigned_out _ _ _ _ _ _ _ _ translation).
    clear IHn_out n_out n_assigned_out.
    induction n_body as [ | eq n_body IHn_body] in a, a_assigned, ident_origin, init_eqs, step_eqs, new_ident_origin, pre_binders, pre_eqs, init_post_eqs, step_post_eqs, translation |- *.
    1: contradiction.
    simpl in a_assigned.
    simpl in translation.
    destruct (translate_equations n_body ident_origin) as [[[[[[init_eq step_eq] origin_ident] binders_pre] equations_pre] post_init_equations] post_step_equations] eqn: translate_nbody.
    destruct eq as [i [ty e]].
    destruct (translate_expr e origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[]]]]]] eqn: unfold_translate.
    injection translation as <- <- <- <- <- <- <-.
    unfold Lustre.equation_dest at 1, fst, snd, projT1 in a_assigned.
    simpl.

    destruct a_assigned as [a_dest_eq | a_assigned].
    1: left; assumption.
    right.
    specialize (IHn_body _ a_assigned _ _ _ _ _ _ _ _ translate_nbody).
    apply in_app_iff.
    apply in_app_iff in IHn_body.
    destruct IHn_body as [in_init | in_post_init].
    1: left; assumption.
    right.
    clear -unfold_translate in_post_init.
    rename c into init_eq, c0 into step_eq, i0 into new_origin_ident, l into new_binders_pre, l0 into new_equations_pre, l1 into new_post_init_equations, l2 into new_post_step_equations.
    rename unfold_translate into translation.

    induction e in a, origin_ident, binders_pre, equations_pre, post_init_equations, post_step_equations, init_eq, step_eq, new_origin_ident, new_binders_pre, new_equations_pre, new_post_init_equations, new_post_step_equations, translation, in_post_init |- *.
    1-3: unfold translate_expr in translation.
    1-3: simpl in translation.
    1-3: injection translation as <- <- <- <- <- <- <-.
    1-3: assumption.

    + unfold translate_expr in translation.
      destruct u.
      all: simpl in translation.
      1-2: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[]]]]]] eqn: unfold_e.
      1-2: injection translation as <- <- <- <- <- <- <-.
      1-2: refine (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ unfold_e in_post_init).

      destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[]]]]]] eqn: unfold_e.

      injection translation as <- <- <- <- <- <- <-.
      specialize (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ unfold_e in_post_init).
      simpl.
      right.
      assumption.
    + unfold translate_expr in translation.
      destruct b.
      all: simpl in translation.
      1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
      1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
      4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
      4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
      14: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
      14: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
      all: injection translation as <- <- <- <- <- <- <-.
      all: refine (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold in_post_init)).
    + unfold translate_expr in translation.
      simpl in translation.
      destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[? ?] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
      destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[? ?] ident_e2] binders_e2] eqs_e2] init_e2] step_e2] eqn: e2_unfold.
      destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e3) ident_e2 binders_e2 eqs_e2 init_e2 step_e2) as [[[[[[]]]]]] eqn: e3_unfold.
      injection translation as <- <- <- <- <- <- <-.
      refine (IHe3 _ _ _ _ _ _ _ _ _ _ _ _ _ e3_unfold (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold in_post_init))). *)

  - apply ABORT_FIXME; exact tt.
    (* assumption. *)
  - apply ABORT_FIXME; exact tt.
    (* clear -translation n_inputs_equations.
    induction n_in in n_body, n_inputs_equations, ident_origin, init_eqs, step_eqs, new_ident_origin, pre_binders, pre_eqs, init_post_eqs, step_post_eqs, translation |- *.
    1: apply incl_nil_l.
    rewrite map_cons in n_inputs_equations.
    apply incl_cons_inv in n_inputs_equations.
    destruct n_inputs_equations as [a_in_b n_inputs_equations].
    apply incl_cons.
    2: refine (IHn_in _ n_inputs_equations _ _ _ _ _ _ _ _ translation).
    clear IHn_in n_in n_inputs_equations.
    destruct a as [name tya].
    induction n_body as [ | eq n_body IHn_body] in name, tya, a_in_b, ident_origin, init_eqs, step_eqs, new_ident_origin, pre_binders, pre_eqs, init_post_eqs, step_post_eqs, translation |- *.
    1: contradiction.
    simpl in a_in_b.
    simpl in translation.
    destruct (translate_equations n_body ident_origin) as [[[[[[init_eq step_eq] origin_ident] binders_pre] equations_pre] post_init_equations] post_step_equations] eqn: translate_nbody.
    destruct eq as [i [ty e]].
    destruct (translate_expr e origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[ei es] new_orig_ident] new_binders_pre] new_eqs_pre] new_init_eqs] new_step_eqs] eqn: unfold_translate.
    injection translation as <- <- <- <- <- <- <-.
    simpl.
    rename unfold_translate into translation.

    destruct a_in_b as [a_is_eq | a_in_body].
    + left.
      injection a_is_eq as <- <-.
      apply Lustre.sig2T_eq_type in H.
      subst.
      unfold translate_expr in translation.
      simpl in translation.
      injection translation as <- <- <- <- <- <-.
      reflexivity.
    + right.
      specialize (IHn_body _ _ a_in_body _ _ _ _ _ _ _ _ translate_nbody).
      apply in_app_iff.
      apply in_app_iff in IHn_body.
      destruct IHn_body as [in_init | in_post_init].
      1: left; assumption.
      right.
      clear -translation in_post_init.

      induction e in name, tya, origin_ident, binders_pre, equations_pre, new_orig_ident, new_binders_pre, new_eqs_pre, new_init_eqs, new_step_eqs, translation, in_post_init, post_init_equations, post_step_equations, ei, es |- *.
      1-3: unfold translate_expr in translation.
      1-3: simpl in translation.
      1-3: injection translation as <- <- <- <- <- <- <-.
      1-3: assumption.

      * unfold translate_expr in translation.
        destruct u.
        all: simpl in translation.
        1-2: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[]]]]]] eqn: unfold_e.
        1-2: injection translation as <- <- <- <- <- <- <-.
        1-2: refine (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ unfold_e in_post_init).

        destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[]]]]]] eqn: unfold_e.

        injection translation as <- <- <- <- <- <- <-.
        specialize (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ unfold_e in_post_init).
        simpl.
        right.
        assumption.
      * unfold translate_expr in translation.
        destruct b.
        all: simpl in translation.
        1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        1-3: destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        4-13: destruct (@LustreTiming.raw_to_comb LustreTiming.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        14: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[c1 c2] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        14: destruct (@LustreTiming.raw_to_comb Lustre.TInt (@expr_to_raw Lustre.TInt e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[]]]]]] eqn: e2_unfold.
        all: injection translation as <- <- <- <- <- <- <-.
        all: refine (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold in_post_init)).
      * unfold translate_expr in translation.
        simpl in translation.
        destruct (@LustreTiming.raw_to_comb LustreTiming.TBool (@expr_to_raw Lustre.TBool e1) origin_ident binders_pre equations_pre post_init_equations post_step_equations) as [[[[[[? ?] ident_e1] binders_e1] eqs_e1] init_e1] step_e1] eqn: e1_unfold.
        destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e2) ident_e1 binders_e1 eqs_e1 init_e1 step_e1) as [[[[[[? ?] ident_e2] binders_e2] eqs_e2] init_e2] step_e2] eqn: e2_unfold.
        destruct (@LustreTiming.raw_to_comb t (@expr_to_raw t e3) ident_e2 binders_e2 eqs_e2 init_e2 step_e2) as [[[[[[]]]]]] eqn: e3_unfold.
        injection translation as <- <- <- <- <- <- <-.
        refine (IHe3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ e3_unfold (IHe2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ e2_unfold (IHe1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1_unfold in_post_init))). *)
  (* EInput, will be changed later *)
  - apply ABORT_FIXME; exact tt.
  - apply ABORT_FIXME; exact tt.
  - apply ABORT_FIXME; exact tt.
  - apply ABORT_FIXME; exact tt.
Defined. 
