From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require Lustre.

From Stdlib Require Import Permutation.

Module Lustre := Lustre.

Definition type := Lustre.type.
Definition TBool := Lustre.TBool.
Definition TInt := Lustre.TInt.
Definition const := Lustre.const.
Definition binder := Lustre.binder.
Definition value := Lustre.value.
Definition binder_ty := Lustre.binder_ty.

Inductive unop: type -> type -> Set :=
  | Uop_not: unop TInt TInt
  | Uop_neg: unop TInt TInt
.

Inductive binop: type -> type -> type -> Set :=
  (** Boolean binop *)
  | Bop_and: binop TBool TBool TBool
  | Bop_or: binop TBool TBool TBool
  | Bop_xor: binop TBool TBool TBool

  (** Arithmetic binop *)
  | Bop_plus: binop TInt TInt TInt
  | Bop_minus: binop TInt TInt TInt
  | Bop_mult: binop TInt TInt TInt
  | Bop_div: binop TInt TInt TInt

  (** Relational binop *)
  | Bop_eq: binop TInt TInt TBool
  | Bop_neq: binop TInt TInt TBool
  | Bop_le: binop TInt TInt TBool
  | Bop_lt: binop TInt TInt TBool
  | Bop_ge: binop TInt TInt TBool
  | Bop_gt: binop TInt TInt TBool
.

Inductive raw_exp : type -> Set :=
  | Raw_EConst: forall {ty}, const ty -> raw_exp ty
  | Raw_EVar: forall (b: binder), raw_exp (binder_ty b)
  | Raw_EUnop: forall {tin tout}, unop tin tout -> raw_exp tin -> raw_exp tout
  | Raw_EBinop: forall {ty1 ty2 tout}, binop ty1 ty2 tout -> raw_exp ty1 -> raw_exp ty2 -> raw_exp tout
  | Raw_EIfte: forall {t}, raw_exp TBool -> raw_exp t -> raw_exp t -> raw_exp t
  | Raw_EPre: forall {ty}, raw_exp ty -> raw_exp ty
  | Raw_EArrow: forall {ty}, raw_exp ty -> raw_exp ty -> raw_exp ty
.

Inductive comb_exp : type -> Set :=
  | EConst: forall {ty}, const ty -> comb_exp ty
  | EVar: forall (b: binder), comb_exp (binder_ty b)
  | EUnop: forall {tin tout}, unop tin tout -> comb_exp tin -> comb_exp tout
  | EBinop: forall {ty1 ty2 tout}, binop ty1 ty2 tout -> comb_exp ty1 -> comb_exp ty2 -> comb_exp tout
  | EIfte: forall {t}, comb_exp TBool -> comb_exp t -> comb_exp t -> comb_exp t
.

Definition equation : Type := ident * { ty : type & comb_exp ty }.
Definition equation_dest (eq : equation) : ident * type := (fst eq, projT1 (snd eq)).

Record node := mk_node {
  n_loc: Result.location;
  n_name: string;

  n_in: list binder;
  n_out: list binder;
  n_locals: list binder; (* Also includes additionally created binders for pre *)
  n_pre: list equation; (* Happens before n_init and n_step *)
  n_init: list equation;
  n_step: list equation;

  n_vars: list binder := n_in ++ n_out ++ n_locals;
  n_assigned_vars_init: list binder := map equation_dest n_init;
  n_assigned_vars_pre: list binder := map equation_dest n_pre;
  n_assigned_vars_step: list binder := map equation_dest n_step;

  n_init_vars_all_assigned: Permutation (n_assigned_vars_pre ++ n_assigned_vars_init) (n_out ++ n_locals);
  n_step_vars_all_assigned: Permutation (n_assigned_vars_pre ++ n_assigned_vars_step) (n_out ++ n_locals);

  n_vars_unique: NoDup (map fst n_vars);

  n_seed: ident;
  n_seed_always_fresh:  forall n, ~ In (iter n next_ident n_seed) (map fst n_vars);
}.



(* Translation from raw expressions to combinatorial expressions, extracting pre and arrow *)

Fixpoint raw_to_comb_aux {ty} (exp: raw_exp ty) (ident_origin: ident) (pre_binders: list binder) (pre_equations init_post_equations step_post_equations: list equation): (
    comb_exp ty (* init *)
    * comb_exp ty (* step *)
    * ident (* New identifier origin *)
    * (list binder) (* Variables created for pre *)
    * (list equation) (* pre equations *)
    (* Equations to merge with the regular equations *)
    (* for init: 
      prex = undef (a variable initialised later)

      for step:
      prex = eqx (eqx being updated later with the current values)
    *)
    (* Equations NOT to be merged, but can be ordered separately *)
    * (list equation) (* init_post equations *)
    * (list equation) (* step_post equations *)
  ) :=
  match exp with
    | Raw_EConst c => (EConst c, EConst c, ident_origin, pre_binders, pre_equations, init_post_equations, step_post_equations)
    | Raw_EVar v => (EVar v, EVar v, ident_origin, pre_binders, pre_equations, init_post_equations, step_post_equations)
    | Raw_EUnop u e => let '(ei, es, orig, binders, equations_pre, init_equations_post, step_equations_post) := raw_to_comb_aux e ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      (EUnop u ei, EUnop u es, orig, binders, equations_pre, init_equations_post, step_equations_post)
    | Raw_EBinop b e1 e2 => let '(e1i, e1s, orig1, binders1, equations_pre1, init_equations_post1, step_equations_post1) := raw_to_comb_aux e1 ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      let '(e2i, e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2) := raw_to_comb_aux e2 orig1 binders1 equations_pre1 init_equations_post1 step_equations_post1 in
        (EBinop b e1i e2i, EBinop b e1s e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2)
    | Raw_EIfte e1 e2 e3 => let '(e1i, e1s, orig1, binders1, equations_pre1, init_equations_post1, step_equations_post1) := raw_to_comb_aux e1 ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      let '(e2i, e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2) := raw_to_comb_aux e2 orig1 binders1 equations_pre1 init_equations_post1 step_equations_post1 in
        let '(e3i, e3s, orig3, binders3, equations_pre3, init_equations_post3, step_equations_post3) := raw_to_comb_aux e3 orig2 binders2 equations_pre2 init_equations_post2 step_equations_post2 in
        (EIfte e1i e2i e3i, EIfte e1s e2s e3s, orig3, binders3, equations_pre3, init_equations_post3, step_equations_post3)
    | @Raw_EPre t e => let '(ei, es, ident_pre, binders, equations_pre, init_equations_post, step_equations_post) := raw_to_comb_aux e ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      let ident_eq := next_ident ident_pre in
        let next_orig := next_ident ident_eq in
          let pre_var := (ident_pre, t) in
            let eq_var := (ident_eq, t) in
              (
                EVar pre_var,
                EVar pre_var,
                next_orig,
                pre_var::eq_var::binders,
                (ident_pre, existT comb_exp t (EVar eq_var))::equations_pre,
                (ident_eq, existT _ t ei)::init_equations_post,
                (ident_eq, existT _ t es)::step_equations_post
              )
    | Raw_EArrow e1 e2 => let '(e1i, e1s, orig1, binders1, equations_pre1, init_equations_post1, step_equations_post1) := raw_to_comb_aux e1 ident_origin pre_binders pre_equations init_post_equations step_post_equations in
      let '(e2i, e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2) := raw_to_comb_aux e2 orig1 binders1 equations_pre1 init_equations_post1 step_equations_post1 in
        (e1i, e2s, orig2, binders2, equations_pre2, init_equations_post2, step_equations_post2)
  end.

Definition raw_to_comb {ty} (exp: raw_exp ty) (ident_origin: ident): (
    comb_exp ty (* init *)
    * comb_exp ty (* step *)
    * ident (* New identifier origin *)
    * (list binder) (* Variables created for pre *)
    * (list equation) (* pre equations *)
    (* Equations to merge with the regular equations *)
    (* for init: 
      prex = undef (a variable initialised later)

      for step:
      prex = eqx (eqx being updated later with the current values)
    *)
    (* Equations NOT to be merged, but can be ordered separately *)
    * (list equation) (* init_post equations *)
    * (list equation) (* step_post equations *)
  ) :=
  raw_to_comb_aux exp ident_origin [] [] [] [].

(** Properties *)
