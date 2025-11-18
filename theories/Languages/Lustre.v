Set Default Goal Selector "!".

From Reactive.Datatypes Require Dict Stream.
From Reactive.Languages Require LustreAst.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Freshness Identifier Sublist.

From Stdlib Require Import Nat List Permutation String.

Import ListNotations.

Module LustreAst := LustreAst.

Definition name_dec := LustreAst.name_dec.

(** A unary operator

  An operator of type [unop tyin tyout] takes an argument of type [tyin] and
  returns an expression of type [tyout].
*)
Inductive unop: type -> type -> Set :=
  | Uop_not: unop TInt TInt
  | Uop_neg: unop TInt TInt
  | Uop_pre: unop TInt TInt (* TODO: general pre*)
.

Lemma unop_inv {ty tout} (x: unop ty tout) :
  {exists (eq1 : ty = TInt) (eq2 : tout = TInt), x = eq_rect _ (unop _) (eq_rect _ (fun ty => unop ty _) Uop_not _ (eq_sym eq1)) _ (eq_sym eq2)} +
  {exists (eq1 : ty = TInt) (eq2 : tout = TInt), x = eq_rect _ (unop _) (eq_rect _ (fun ty => unop ty _) Uop_neg _ (eq_sym eq1)) _ (eq_sym eq2)} +
  {exists (eq1 : ty = TInt) (eq2 : tout = TInt), x = eq_rect _ (unop _) (eq_rect _ (fun ty => unop ty _) Uop_pre _ (eq_sym eq1)) _ (eq_sym eq2)}.
Proof using.
  destruct x; [left|left|right]; [left|right|]; exists eq_refl, eq_refl; exact eq_refl.
Defined.

Lemma unop_dec {ty tout} (x y: unop ty tout) : {x = y} + {x <> y}.
Proof.
  destruct (unop_inv x) as [[H1|H1]|H1].
  all: destruct (unop_inv y) as [[H2|H2]|H2].
  1,5,9: left.
  4-9: right.
  all: destruct H1 as [eq1 [eq2 ->]].
  all: destruct H2 as [-> [-> ->]].
  all: rewrite !(Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn.
  all: rewrite !(Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn.
  1-3: reflexivity.
  all: discriminate.
Defined.

(** A binary operator

  An operator of type [binop ty1 ty2 tyout] takes two arguments of type [ty1]
  and [ty2] returns an expression of type [tyout].
*)
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

  (** Timing bop *)
  | Bop_arrow: binop TInt TInt TInt (* TODO: general arrow *)
.

Lemma binop_inv {ty1 ty2 tout} (x: binop ty1 ty2 tout) :
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_and _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_or _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_xor _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_plus _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_minus _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_mult _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_div _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_eq _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_neq _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_le _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_lt _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_ge _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_gt _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)} +
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_arrow _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)}.
Proof using.
  destruct x.
  1-13: left.
  1-12: left.
  1-11: left.
  1-10: left.
  1-09: left.
  1-08: left.
  1-07: left.
  1-06: left.
  1-05: left.
  1-04: left.
  1-03: left.
  1-02: left.
  1-01: left.
  2-14: right.
  all: exists eq_refl, eq_refl, eq_refl; exact eq_refl.
Defined.
Lemma binop_dec {ty1 ty2 tout} (x y: binop ty1 ty2 tout) : {x = y} + {x <> y}.
Proof.
  pose proof (binop_inv x) as H1.
  repeat destruct H1 as [ H1 | H1 ].
  all: pose proof (binop_inv y) as H.
  14: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  15: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-13: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  13: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  14: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-12: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  12: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  13: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-11: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  11: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  12: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-10: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  10: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  11: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-9: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  9: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  10: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-8: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  8: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  9: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-7: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  7: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  8: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-6: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  6: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  7: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-5: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  5: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  6: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-4: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  4: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  5: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-3: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  3: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  4: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1-2: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  2: destruct H as [f|H]; [right|left]; destruct H1 as [eq1 [eq2 [eq3 ->]]]; [|destruct H as [-> [-> [-> ->]]]].
  3: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  1: destruct H as [H|f]; [|
    right; destruct H1 as [eq1 [eq2 [eq3 ->]]], f as [-> [-> [-> f]]]; try discriminate; intros <-;
    repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate
  ].
  1: left; destruct H1 as [eq1 [eq2 [eq3 ->]]], H as [-> [-> [-> ->]]].
  1: do 3 (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn); reflexivity.
  all: subst; cbn; intros <-; repeat (destruct f as [f|[? [? [? f]]]]; [|try discriminate]).
  all: try solve [repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate f].
  all: destruct f as [? [? [? f]]]; try discriminate.
  all: repeat (rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; cbn in f); discriminate f.
Defined.

Inductive exp : type -> Set :=
  | EConst: Result.location -> forall {ty}, const ty -> exp ty
  | EVar: Result.location -> forall (b : binder), exp (binder_ty b)
  | EUnop: Result.location -> forall {tin tout}, unop tin tout -> exp tin -> exp tout
  | EBinop: Result.location -> forall {ty1 ty2 tout}, binop ty1 ty2 tout -> exp ty1 -> exp ty2 -> exp tout
  | EIfte: Result.location -> forall {t}, exp TBool -> exp t -> exp t -> exp t
.

Inductive exp_eq : forall {ty : type}, exp ty -> exp ty -> Prop :=
  | EeqConst : forall {l1 l2 ty} {c : const ty}, exp_eq (EConst l1 c) (EConst l2 c)
  | EeqVar : forall {l1 l2 b}, exp_eq (EVar l1 b) (EVar l2 b)
  | EeqUnop : forall {l1 l2 tin tout} {op : unop tin tout} {e1 e2}, exp_eq e1 e2 -> exp_eq (EUnop l1 op e1) (EUnop l2 op e2)
  | EeqBinop : forall {l1 l2 ty1 ty2 tout} {op : binop ty1 ty2 tout} {e11 e12 e21 e22},
      exp_eq e11 e21 -> exp_eq e12 e22 -> exp_eq (EBinop l1 op e11 e12) (EBinop l2 op e21 e22)
  | EeqIfte : forall {l1 l2 ty e11 e12 e13 e21 e22} {e23 : exp ty},
      exp_eq e11 e21 -> exp_eq e12 e22 -> exp_eq e13 e23 -> exp_eq (EIfte l1 e11 e12 e13) (EIfte l2 e21 e22 e23)
.

Lemma exp_eq_refl : forall {ty} (e : exp ty), exp_eq e e.
Proof using.
  intros ty e; induction e; constructor; assumption.
Qed.

Lemma exp_inv {ty} (x: exp ty) : { loc &
  {c : const ty | x = EConst loc c} +
  {b | exists (eq : ty = _), x = eq_rect _ exp (EVar loc b) _ (eq_sym eq)} +
  {tin : type & {op : unop tin ty & {e : exp tin | x = EUnop loc op e}}} +
  {ty1 : type & {ty2 : type & {op : binop ty1 ty2 ty & {e1 : exp ty1 & {e2 : exp ty2 | x = EBinop loc op e1 e2}}}}} +
  {eb : exp TBool & {et : exp ty & {ef : exp ty | x = EIfte loc eb et ef}}} }%type.
Proof using.
  destruct x; eexists.
  1-4: left.
  1-3: left.
  1-2: left.
  1-1: left.
  2-5: right.
  all: try solve [repeat eexists; exact eq_refl].
  1: exists b, eq_refl; exact eq_refl.
Defined.
Lemma exp_dec {ty} (e1 e2: exp ty) : {exp_eq e1 e2} + {~ exp_eq e1 e2}.
Proof.
  revert e2.
  induction e1 as [ loc1 ty c | loc1 b | loc1 tin tout op e1 IH | loc1 ty1 ty2 tout op e11 IH1 e12 IH2 | loc1 ty eb1 IHb et1 IHt ef1 IHf ].
  - intros e2; destruct (exp_inv e2) as [ loc2 [ [ [ [
      (c' & ->) | (b' & H) ] | (tin & op & e1' & ->) ] | (ty1 & ty2 & op & e1' & e2' & ->) ] | (eb & et & ef & ->) ] ].
    1: destruct (const_dec c c') as [<-|n]; [left; exact EeqConst|].
    all: right.
    2: destruct H as [-> ->].
    all: intros f; inversion f; simpl_exist_type; try discriminate; subst.
    contradiction (n eq_refl).
  - intros e2; destruct (exp_inv e2) as [ loc2 [ [ [ [
      (c' & ->) | (b' & H) ] | (tin & op & e1' & ->) ] | (ty1 & ty2 & op & e1' & e2' & ->) ] | (eb & et & ef & ->) ] ].
    2: destruct b as [n1 ty1], b' as [n2 ty2].
    2: destruct (PeanoNat.Nat.eq_dec n1 n2) as [<-|n]; [left; cbn in H; destruct H as [<- ->]; exact EeqVar|].
    all: right.
    2: cbn in H; destruct H as [<- ->].
    all: intros f; inversion f; simpl_exist_type; try discriminate; subst.
    contradiction (n eq_refl).
  - intros e2; destruct (exp_inv e2) as [ loc2 [ [ [ [
      (c' & ->) | (b' & H) ] | (tin' & op' & e1' & ->) ] | (ty1 & ty2 & op' & e1' & e2' & ->) ] | (eb & et & ef & ->) ] ].
    3: destruct (type_dec tin tin') as [<-|n].
    3: destruct (unop_dec op op') as [<-|n].
    3: specialize (IH e1') as [IH|IH].
    3: left; constructor; assumption.
    all: right.
    2: destruct H as [-> ->].
    all: intros f; inversion f; simpl_exist_type; try discriminate; subst; contradiction.
  - intros e2; destruct (exp_inv e2) as [ loc2 [ [ [ [
      (c' & ->) | (b' & H) ] | (tin' & op' & e1' & ->) ] | (ty1' & ty2' & op' & e1' & e2' & ->) ] | (eb & et & ef & ->) ] ].
    4: destruct (type_dec ty1 ty1') as [<-|n].
    4: destruct (type_dec ty2 ty2') as [<-|n].
    4: destruct (binop_dec op op') as [<-|n].
    4: specialize (IH1 e1') as [IH1|IH1].
    4: specialize (IH2 e2') as [IH2|IH2].
    4: left; constructor; assumption.
    all: right.
    2: destruct H as [-> ->].
    all: intros f; inversion f; simpl_exist_type; try discriminate; subst; simpl_exist_type; subst; contradiction.
  - intros e2; destruct (exp_inv e2) as [ loc2 [ [ [ [
      (c' & ->) | (b' & H) ] | (tin' & op' & e1' & ->) ] | (ty1' & ty2' & op' & e1' & e2' & ->) ] | (eb2 & et2 & ef2 & ->) ] ].
    5: specialize (IHb eb2) as [IHb|IHb].
    5: specialize (IHt et2) as [IHt|IHt].
    5: specialize (IHf ef2) as [IHf|IHf].
    5: left; constructor; assumption.
    all: right.
    2: destruct H as [-> ->].
    all: intros f; inversion f; simpl_exist_type; try discriminate; subst; contradiction.
Defined.

Definition equation : Type := ident * { ty : type & exp ty }.
Definition equation_dest (eq : equation) : ident * type := (fst eq, projT1 (snd eq)).

Definition equation_eq (eq1 eq2 : equation) : Prop :=
  fst eq1 = fst eq2 /\
  { Hty : projT1 (snd eq1) = projT1 (snd eq2)
  | exp_eq (projT2 (snd eq1)) (eq_rec_r exp (projT2 (snd eq2)) Hty) }.

Lemma equation_dec (e1 e2: equation) : {equation_eq e1 e2} + {~ equation_eq e1 e2}.
Proof.
  destruct e1 as [n1 [ty1 e1]].
  destruct e2 as [n2 [ty2 e2]].
  destruct (PeanoNat.Nat.eq_dec n1 n2) as [<-|ne]; [|right; cbn; intros [f _]; exact (ne f)].
  destruct (type_dec ty1 ty2) as [<-|ne]; [|right; cbn; intros [_ [f _]]; exact (ne f)].
  destruct (exp_dec e1 e2) as [e|ne]; [|right; cbn; intros [_ [He f]]; refine (ne _)].
  2: rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl) in f; exact f.
  left; split; [exact eq_refl|exists eq_refl; exact e].
Defined.

Record node := mk_node {
  n_loc: Result.location;
  n_name: string;

  n_in: list binder;
  n_out: list binder;
  n_locals: list binder;
  n_body: list equation;

  n_vars: list binder := n_in ++ n_out ++ n_locals;
  n_assigned_vars: list binder := map equation_dest n_body;

  n_vars_all_assigned: Permutation n_assigned_vars (n_out ++ n_locals);
  n_vars_unique: NoDup (map fst n_vars);
  
  n_seed: ident;
  n_seed_always_fresh: freshness n_seed n_vars;
}.

Definition node_eq (n1 n2: node) :=
  n_name n1 = n_name n2 /\
  Permutation (n_in n1) (n_in n2) /\
  n_out n1 = n_out n2 /\
  Permutation (n_locals n1) (n_locals n2) /\
  (exists b, Permutation (n_body n1) b /\ Forall2 equation_eq b (n_body n2)).

(** ** Semantics *)
Inductive value : type -> Set :=
  | VConst : forall {ty}, const ty -> value ty
  | VUnop  : forall {ty tout}, unop ty tout -> value ty -> value tout
  | VBinop : forall {ty1 ty2 tout}, binop ty1 ty2 tout -> value ty1 -> value ty2 -> value tout
  | VIfte  : forall {ty}, value TBool -> value ty -> value ty -> value ty
.

Lemma value_inv {ty} (x: value ty) :
  {c : const ty | x = VConst c} +
  {tin : type & {op : unop tin ty & {e : value tin | x = VUnop op e}}} +
  {ty1 : type & {ty2 : type & {op : binop ty1 ty2 ty & {e1 : value ty1 & {e2 : value ty2 | x = VBinop op e1 e2}}}}} +
  {eb : value TBool & {et : value ty & {ef : value ty | x = VIfte eb et ef}}}.
Proof using.
  destruct x.
  1-3: left.
  1-2: left.
  1-1: left.
  2-4: right.
  all: repeat eexists; exact eq_refl.
Defined.
Lemma value_dec {ty} (e1 e2: value ty) : {e1 = e2} + {e1 <> e2}.
Proof.
  revert e2.
  induction e1 as [ ty c | tin tout op e1 IH | ty1 ty2 tout op e11 IH1 e12 IH2 | ty eb1 IHb et1 IHt ef1 IHf ].
  - intros e2; destruct (value_inv e2) as [ [ [
      (c' & ->) | (tin & op & e1' & ->) ] | (ty1 & ty2 & op & e1' & e2' & ->) ] | (eb & et & ef & ->) ].
    1: destruct (const_dec c c') as [e|n]; [left; exact (f_equal _ e)|right; intros [=f]; apply sig2T_eq_type in f; exact (n f)].
    all: right; try destruct H as [eq1 ->]; subst; discriminate.
  - intros e2; destruct (value_inv e2) as [ [ [
      (c' & ->) | (tin' & op' & e1' & ->) ] | (ty1 & ty2 & op' & e1' & e2' & ->) ] | (eb & et & ef & ->) ].
    1,3-4: right; try destruct H as [eq1 ->]; subst; discriminate.
    destruct (type_dec tin tin') as [<-|ne]; [|right; intros [=f _ _]; exact (ne f)].
    destruct (unop_dec op op') as [<-|ne]; [|right; intros [=f _]; exact (ne (sig2T_eq_type (sig2T_eq_type f)))].
    destruct (IH e1') as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    left; reflexivity.
  - intros e2; destruct (value_inv e2) as [ [ [
      (c' & ->) | (tin' & op' & e1' & ->) ] | (ty1' & ty2' & op' & e1' & e2' & ->) ] | (eb & et & ef & ->) ].
    1-2,4: right; try destruct H as [eq1 ->]; subst; discriminate.
    destruct (type_dec ty1 ty1') as [<-|ne]; [|right; intros [=f _ _ _]; exact (ne f)].
    destruct (type_dec ty2 ty2') as [<-|ne]; [|right; intros [=f _ _]; exact (ne f)].
    destruct (binop_dec op op') as [<-|ne]; [|right; intros [=f _]; exact (ne (sig2T_eq_type (sig2T_eq_type (sig2T_eq_type f))))].
    destruct (IH1 e1') as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    destruct (IH2 e2') as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    left; reflexivity.
  - intros e2; destruct (value_inv e2) as [ [ [
      (c' & ->) | (tin' & op' & e1' & ->) ] | (ty1' & ty2' & op' & e1' & e2' & ->) ] | (eb2 & et2 & ef2 & ->) ].
    1-3: right; try destruct H as [eq1 ->]; subst; discriminate.
    destruct (IHb eb2) as [<-|ne]; [|right; intros [=f]; exact (ne f)].
    destruct (IHt et2) as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    destruct (IHf ef2) as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    left; reflexivity.
Defined.

Definition history := Dict.t {ty & Stream.t (value ty)}.
Definition in_history (h : history) '((v, ty) : nat * type) := match Dict.find v h with
  | Some (existT _ ty' _) => ty' = ty
  | None => False
end.
Definition in_history' (h : history) '((v, ty) : nat * type) := exists s, Dict.find v h = Some (existT _ ty s).

Lemma in_history_iff : forall h v, in_history h v <-> in_history' h v.
Proof using.
  intros h [ v ty ].
  unfold in_history, in_history'.
  destruct (Dict.find v h) as [ [ ty' e ] | ]; split.
  - intros H.
    subst.
    exists e.
    reflexivity.
  - intros [ e' He ].
    injection He as He.
    exact (EqdepFacts.eq_sigT_fst H).
  - intros [].
  - intros [ e He ].
    discriminate He.
Qed.

Inductive sem_exp : history -> forall {ty}, exp ty -> value ty -> Prop :=
  | SeConst (h: history) loc {ty} (c: const ty):
      sem_exp h (EConst loc c) (VConst c)

  | SeVar (h : history) loc (b: binder) (v: Stream.t (value (binder_ty b))):
      Dict.maps_to (fst b) (existT _ _ v) h ->
      sem_exp h (EVar loc b) (Stream.hd v)

  | SeUnop (h: history) loc {ty tout} (op: unop ty tout) (e: exp ty) (v: value ty):
      sem_exp h e v ->
      sem_exp h (EUnop loc op e) (VUnop op v)

  | SeBinop (h: history) loc {ty1 ty2 tout} (op: binop ty1 ty2 tout) (e1 e2: exp _) (v1 v2: value _):
      sem_exp h e1 v1 ->
      sem_exp h e2 v2 ->
      sem_exp h (EBinop loc op e1 e2) (VBinop op v1 v2)

  | SeIfte (h: history) loc {ty} (e1: exp TBool) (e2 e3: exp ty) (v1 v2 v3: value _):
      sem_exp h e1 v1 ->
      sem_exp h e2 v2 ->
      sem_exp h e3 v3 ->
      sem_exp h (EIfte loc e1 e2 e3) (VIfte v1 v2 v3)
.


(** ** Properties *)

Definition extract_stream (ty : type) {ty'} (s : Stream.t (value ty')) : option (value ty) := match type_dec ty' ty with
  | left e => Some (eq_rect ty' value (Stream.hd s) ty e)
  | right _ => None
end.
Lemma extract_stream_eqty : forall {ty} (s : Stream.t (value ty)), extract_stream ty s = Some (Stream.hd s).
Proof using.
  intros ty s.
  unfold extract_stream.
  rewrite type_dec_same.
  reflexivity.
Qed.

Fixpoint eval_exp (h: history) {ty} (e: exp ty): option (value ty) :=
  match e with
    | EConst _ c => Some (VConst c)
    | EVar _ (name, typ) => match Dict.find name h with None => None | Some (existT _ ty' s) => extract_stream _ s end
    | EUnop _ op e => match eval_exp h e with
      | Some v => Some (VUnop op v)
      | None => None
    end
    | EBinop _ op e1 e2 => match eval_exp h e1, eval_exp h e2 with
      | Some v1, Some v2 => Some (VBinop op v1 v2)
      | _, _ => None
    end
    | EIfte _ e1 e2 e3 => match eval_exp h e1, eval_exp h e2, eval_exp h e3 with
      | Some v1, Some v2, Some v3 => Some (VIfte v1 v2 v3)
      | _, _, _ => None
    end
  end.

Definition is_evaluable (h: history) {ty} (e: exp ty): Prop :=
  exists v: value ty, eval_exp h e = Some v.


Fixpoint var_of_exp_aux {ty} (e: exp ty) (acc: list (ident * type)): list (ident * type) :=
  match e with
    | EConst _ _ => acc
    | EVar _ (name, ty) => (name, ty) :: acc
    | EUnop _ _ e => var_of_exp_aux e acc
    | EBinop _ _ e1 e2 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 acc)
    | EIfte _ e1 e2 e3 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 (var_of_exp_aux e3 acc))
  end.

Definition var_of_exp {ty} (e: exp ty): list (ident * type) :=
  var_of_exp_aux e [].

Fixpoint deps_of_exp_aux {ty} (e: exp ty) (acc: list (ident * type)): list (ident * type) :=
  match e with
    | EConst _ _ => acc
    | EVar _ (name, ty) => (name, ty) :: acc
    | EUnop _ Uop_pre e => acc
    | EUnop _ _ e => deps_of_exp_aux e acc
    | EBinop _ _ e1 e2 =>
      deps_of_exp_aux e1 (deps_of_exp_aux e2 acc)
    | EIfte _ e1 e2 e3 =>
      deps_of_exp_aux e1 (deps_of_exp_aux e2 (deps_of_exp_aux e3 acc))
  end.

Definition deps_of_exp {ty} (e: exp ty): list (ident * type) :=
  deps_of_exp_aux e [].

(** ** Lemmas *)

Lemma var_of_exp_aux_eq {ty} (e: exp ty) (l: list (ident * type)):
  var_of_exp_aux e l = var_of_exp e ++ l.
Proof.
  revert l.
  induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros l.
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

Lemma var_of_exp_aux_empty {ty} (e: exp ty) (l: list (ident * type)):
  var_of_exp_aux e l = [] -> l = [].
Proof.
  intros H.
  rewrite var_of_exp_aux_eq in H.
  apply app_eq_nil in H as [ _ H ].
  assumption.
Qed.

Lemma var_of_exp_aux_incl {ty} (e: exp ty) (l1 l2: list (ident * type)):
  incl l1 l2 -> incl (var_of_exp_aux e l1) (var_of_exp_aux e l2).
Proof.
  intros H i Hi.
  rewrite var_of_exp_aux_eq in Hi |- *.
  apply in_or_app.
  apply in_app_or in Hi as [ Hin | Hin ]; auto.
Qed.

Lemma var_of_exp_aux_in_exp {ty tyv} (e: exp ty) (l: list (ident * type)) (x: ident):
  In (x, tyv) (var_of_exp e) -> In (x, tyv) (var_of_exp_aux e l).
Proof.
  apply var_of_exp_aux_incl with (l1 := []).
  intros a Hin.
  destruct Hin.
Qed.

Lemma var_of_exp_aux_in_acc {ty tyv} (e: exp ty) (l: list (ident * type)) (x: ident):
  In (x, tyv) l -> In (x, tyv) (var_of_exp_aux e l).
Proof.
  intros H.
  rewrite var_of_exp_aux_eq.
  apply in_or_app.
  auto.
Qed.

Lemma var_of_exp_binop_eq loc {ty1 ty2 ty} (e1 e2: exp _) (b: binop ty1 ty2 ty):
  var_of_exp (EBinop loc b e1 e2) = var_of_exp e1 ++ var_of_exp e2.
Proof.
  unfold var_of_exp.
  simpl.
  rewrite var_of_exp_aux_eq.
  reflexivity.
Qed.

Lemma var_of_exp_ifte_eq loc {ty} (e1 : exp TBool) (e2 e3: exp ty):
  var_of_exp (EIfte loc e1 e2 e3) = var_of_exp e1 ++ var_of_exp e2 ++ var_of_exp e3.
Proof.
  unfold var_of_exp.
  simpl.
  do 2 rewrite var_of_exp_aux_eq.
  reflexivity.
Qed.

Lemma var_of_exp_not_in_binop loc {ty1 ty2 ty} (exp1 exp2: exp _) (x: ident) (b: binop ty1 ty2 ty):
  (forall tyv, ~ In (x, tyv) (var_of_exp (EBinop loc b exp1 exp2))) ->
  forall tyv, (~ In (x, tyv) (var_of_exp exp1) /\ ~ In (x, tyv) (var_of_exp exp2)).
Proof.
  intros Hnin.
  split.
  - intros Hin1.
    apply (Hnin tyv).
    unfold var_of_exp.
    simpl.
    apply var_of_exp_aux_in_exp.
    assumption.
  - intros Hin1.
    apply (Hnin tyv).
    unfold var_of_exp.
    simpl.
    apply var_of_exp_aux_in_acc.
    assumption.
Qed.

Lemma var_of_exp_not_in_ifte loc {ty} (e1: exp TBool) (e2 e3: exp ty) (x: ident):
  (forall tyv, ~ In (x, tyv) (var_of_exp (EIfte loc e1 e2 e3))) ->
  forall tyv, (~ In (x, tyv) (var_of_exp e1) /\ ~ In (x, tyv) (var_of_exp e2) /\ ~ In (x, tyv) (var_of_exp e3)).
Proof.
  intros Hnin.
  split.
  - intros Hin.
    apply (Hnin tyv).
    unfold var_of_exp.
    simpl.
    apply var_of_exp_aux_in_exp.
    assumption.
  - split.
    + intros Hin.
      apply (Hnin tyv).
      unfold var_of_exp.
      simpl.
      apply var_of_exp_aux_in_acc.
      apply var_of_exp_aux_in_exp.
      assumption.
    + intros Hin.
      apply (Hnin tyv).
      unfold var_of_exp.
      simpl.
      apply var_of_exp_aux_in_acc.
      apply var_of_exp_aux_in_acc.
      assumption.
Qed.

Lemma exp_with_evaluable_vars_is_evaluable (h: history) {ty} (e: exp ty):
  Forall (in_history h) (var_of_exp e) ->
  is_evaluable h e.
Proof.
  intros H.
  induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ].
  - exists (VConst c).
    reflexivity.
  - apply Forall_inv, in_history_iff in H.
    destruct H as [ s Hs ].
    exists (Stream.hd s).
    simpl.
    rewrite Hs.
    exact (extract_stream_eqty _).
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

Lemma exp_evaluable_have_evaluable_vars (h: history) {ty} (e: exp ty) (v: value ty):
  eval_exp h e = Some v ->
  Forall (in_history h) (var_of_exp e).
Proof.
  intros H.
  revert v H.
  induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros v H.
  - constructor.
  - constructor; [ | constructor ].
    apply in_history_iff.
    simpl in H |- *.
    destruct (Dict.find i h) as [ [ ty' s ] | ]; [ | discriminate H ].
    unfold extract_stream in H.
    destruct (type_dec ty' ty) as [ e | n ]; [ subst | discriminate H ].
    exists s.
    reflexivity.
  - unfold var_of_exp.
    simpl in *.
    destruct (eval_exp h e); [ | discriminate ].
    apply IH with (v := v0).
    reflexivity.
  - simpl in H.
    destruct (eval_exp h e1) as [ v1 | ]; [ | discriminate ].
    destruct (eval_exp h e2) as [ v2 | ]; [ | discriminate ].
    specialize (IH1 v1 eq_refl).
    specialize (IH2 v2 eq_refl).
    rewrite var_of_exp_binop_eq.
    apply Forall_app.
    split; assumption.
  - simpl in H.
    destruct (eval_exp h e1) as [ v1 | ]; [ | discriminate ].
    destruct (eval_exp h e2) as [ v2 | ]; [ | discriminate ].
    destruct (eval_exp h e3) as [ v3 | ]; [ | discriminate ].
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

Theorem sem_eval_exp {ty} (e: exp ty) (h: history) (v: value ty):
  eval_exp h e = Some v <-> sem_exp h e v.
Proof.
  split.
  - intros H.
    revert v H.
    induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros v H.
    + inversion H.
      apply SeConst.
    + cbn in H.
      destruct (Dict.find i h) as [ [ ty' s ] | ] eqn: Heq; [ | discriminate H ].
      unfold extract_stream in H.
      destruct (type_dec ty' ty) as [ -> | n ]; [ | discriminate H ].
      injection H as <-.
      apply SeVar.
      assumption.
    + inversion H.
      destruct (eval_exp h e) as [ v' | ]; [ | discriminate ].
      specialize (IH v' eq_refl).
      inversion H1.
      apply SeUnop.
      assumption.
    + simpl in H.
      destruct (eval_exp h e1) as [ v1 | ]; [ | discriminate ].
      destruct (eval_exp h e2) as [ v2 | ]; [ | discriminate ].
      specialize (IH1 v1 eq_refl).
      specialize (IH2 v2 eq_refl).
      inversion H.
      apply SeBinop; assumption.
    + simpl in H.
      destruct (eval_exp h e1) as [ v1 | ]; [ | discriminate ].
      destruct (eval_exp h e2) as [ v2 | ]; [ | discriminate ].
      destruct (eval_exp h e3) as [ v3 | ]; [ | discriminate ].
      specialize (IH1 v1 eq_refl).
      specialize (IH2 v2 eq_refl).
      specialize (IH3 v3 eq_refl).
      inversion H.
      apply SeIfte; assumption.
  - intros H.
    revert v H.
    induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros v H.
    + inversion H.
      simpl_exist_type.
      subst.
      reflexivity.
    + inversion H; subst.
      simpl_exist_type; subst.
      simpl.
      rewrite H3.
      unfold extract_stream; cbn; rewrite type_dec_same.
      reflexivity.
    + inversion H.
      simpl_exist_type.
      subst.
      simpl.
      rewrite (IH _ H3).
      reflexivity.
    + inversion H.
      subst ty3.
      simpl_exist_type.
      subst.
      simpl.
      rewrite (IH1 _ H4), (IH2 _ H10).
      reflexivity.
    + inversion H.
      simpl_exist_type.
      subst.
      simpl.
      rewrite (IH1 _ H5), (IH2 _ H8), (IH3 _ H9).
      reflexivity.
Qed.

Lemma deps_of_exp_aux_eq {ty} (e: exp ty) (l: list (ident * type)):
  deps_of_exp_aux e l = deps_of_exp e ++ l.
Proof.
  revert l.
  induction e as [ loc ty c | loc (i, ty) | loc ty tout op e IH | loc ty1 ty2 tout op e1 IH1 e2 IH2 | loc ty e1 IH1 e2 IH2 e3 IH3 ]; intros l.
  - reflexivity.
  - reflexivity.
  - destruct op.
    + apply IH.
    + apply IH.
    + reflexivity.
  - unfold deps_of_exp.
    simpl.
    rewrite IH1, IH2, IH1, IH2.
    rewrite app_nil_r, app_assoc.
    reflexivity.
  - unfold deps_of_exp.
    simpl.
    rewrite IH1, IH2, IH3, IH1, IH2, IH3.
    rewrite app_nil_r, app_assoc, app_assoc, app_assoc.
    reflexivity.
Qed.

Lemma deps_of_exp_binop_eq loc {ty1 ty2 ty} (e1 e2: exp _) (b: binop ty1 ty2 ty):
  deps_of_exp (EBinop loc b e1 e2) = deps_of_exp e1 ++ deps_of_exp e2.
Proof.
  unfold deps_of_exp.
  simpl.
  rewrite deps_of_exp_aux_eq.
  reflexivity.
Qed.

Lemma deps_of_exp_ifte_eq loc {ty} (e1 : exp TBool) (e2 e3: exp ty):
  deps_of_exp (EIfte loc e1 e2 e3) = deps_of_exp e1 ++ deps_of_exp e2 ++ deps_of_exp e3.
Proof.
  unfold deps_of_exp.
  simpl.
  do 2 rewrite deps_of_exp_aux_eq.
  reflexivity.
Qed.

Lemma sub_deps_of_exp_aux_gen {ty} (e: exp ty) (l1 l2: list (ident * type)):
  Sublist l1 l2 -> Sublist l1 (deps_of_exp_aux e l2).
Proof.
  revert l1 l2.
  induction e as [ | loc b | loc tin tout u e Ih | loc ty1 ty2 tout b e1 Ih1 e2 Ih2 | loc t e1 Ih1 e2 Ih2 e3 Ih3 ].
  all: intros l1 l2 s12.
  1: intros; simpl; assumption.
  - destruct b.
    constructor 2.
    assumption.
  - destruct u.
    + simpl.
      apply Ih.
      assumption.
    + simpl.
      apply Ih.
      assumption.
    + simpl.
      assumption.
  - simpl.
    apply Ih1.
    apply Ih2.
    assumption.
  - simpl.
    apply Ih1.
    apply Ih2.
    apply Ih3.
    assumption.
Qed.

Lemma sub_deps_of_exp_aux {ty} (e: exp ty) (aux: list (ident * type)):
  Sublist aux (deps_of_exp_aux e aux).
Proof.
  apply sub_deps_of_exp_aux_gen.
  apply sublist_refl.
Qed.

Lemma deps_var_aux_sublist {ty} (e: exp ty) (lexp: list (ident * type)) (ldeps: list (ident * type)):
  Sublist ldeps lexp -> Sublist (deps_of_exp_aux e ldeps) (var_of_exp_aux e lexp).
Proof.
  revert lexp.
  revert ldeps.
  induction e as [ | loc [] | loc tin tout u e He | loc ty1 ty2 tout b e1 H1 e2 H2 | loc t e1 H1 e2 H2 e3 H3 ].
  all: intros ldeps lexp sub.
  - simpl.
    assumption.
  - simpl.
    constructor 3.
    assumption.
  - destruct u.
    + simpl.
      apply He.
      assumption.
    + simpl.
      apply He.
      assumption.
    + simpl.
      eapply sublist_trans.
      * eapply sub_deps_of_exp_aux.
      * apply He.
        assumption.
  - simpl.
    apply H1.
    apply H2.
    assumption.
  - simpl.
    apply H1.
    apply H2.
    apply H3.
    assumption.
Qed.

Lemma deps_var_sublist {ty} (e: exp ty):
  Sublist (deps_of_exp e) (var_of_exp e).
Proof.
  unfold deps_of_exp, var_of_exp.
  apply deps_var_aux_sublist.
  constructor 1.
Qed.
