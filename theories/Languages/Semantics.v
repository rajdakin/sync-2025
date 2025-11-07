Set Default Goal Selector "!".

From Stdlib Require Import Nat.
From Reactive.Props Require Import Identifier Sigma.

Inductive type : Set :=
  | TVoid
  | TBool
  | TInt
.

Definition binder := prod ident type.
Definition binder_ty (b : binder) : type := snd b.

Lemma type_dec (x y: type): {x = y} + {x <> y}.
Proof.
  destruct x, y; try solve [left; reflexivity]; right; discriminate.
Defined.

Lemma binder_dec (x y: binder) : {x = y} + {x <> y}.
Proof.
  destruct x as [i1 ty1], y as [i2 ty2].
  
  pose proof (PeanoNat.Nat.eq_dec i1 i2).
  destruct H.
  2: {
    right.
    injection as eqi _.
    contradiction.
  }

  destruct (type_dec ty1 ty2).
  2: {
    right.
    injection as _ eqt.
    contradiction.
  }

  left.
  f_equal.
  all: assumption.
Defined.

Definition sig2T_eq_type := @sig2T_eq _ type_dec.
Arguments sig2T_eq_type {_ _ _ _}.

Lemma type_dec_same : forall ty, type_dec ty ty = left eq_refl.
Proof using.
  intros ty.
  destruct (type_dec ty ty) as [ e | n ]; [ | contradiction (n eq_refl) ].
  f_equal.
  apply Eqdep_dec.UIP_dec.
  exact type_dec.
Qed.

Lemma forall_type_dec : forall (P : type -> Prop), (forall ty, {P ty} + {~P ty}) -> {forall ty, P ty} + {exists ty, ~ P ty}.
Proof using.
  intros P dec.
  destruct (dec TVoid) as [Pvoid | nP]; [|right; exact (ex_intro (fun ty => ~ P ty) _ nP)].
  destruct (dec TBool) as [Pbool | nP]; [|right; exact (ex_intro (fun ty => ~ P ty) _ nP)].
  destruct (dec TInt)  as [Pint  | nP]; [|right; exact (ex_intro (fun ty => ~ P ty) _ nP)].
  left; intros []; assumption.
Defined.

Definition type_eqb (x y: type): bool :=
  match x, y with
    | TVoid, TVoid => true
    | TBool, TBool => true
    | TInt, TInt => true
    | _, _ => false
  end.

Lemma type_eqb_eq (x y: type):
  type_eqb x y = true <-> x = y.
Proof.
  destruct x, y.
  all: firstorder.
  all: discriminate.
Qed.

Lemma type_eqb_refl (t: type):
  type_eqb t t = true.
Proof.
  destruct t; reflexivity.
Qed.

Definition binder_eqb (x y: binder): bool :=
  andb (fst x =? fst y) (type_eqb (snd x) (snd y)).

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

  intros H.
  now destruct t, t0.
Qed.

Inductive const : type -> Set :=
  | CVoid: const TVoid
  | CBool: bool -> const TBool
  | CInt: nat -> const TInt
.
Lemma const_inv {ty} (x: const ty) :
  {eq : ty = _ & {b : bool | x = eq_rect _ const (CBool b) _ (eq_sym eq)}} +
  {eq : ty = _ & {n : nat | x = eq_rect _ const (CInt n) _ (eq_sym eq)}} +
  {exists (eq : ty = _), x = eq_rect _ const CVoid _ (eq_sym eq)}.
Proof using.
  destruct x as [|b|n]; [right|left; left|left; right]; exists eq_refl; [|exists b|exists n]; exact eq_refl.
Defined.

Lemma const_dec {ty} (x y: const ty) : {x = y} + {x <> y}.
Proof.
  destruct x as [ | b | n ].
  all: destruct (const_inv y) as [[[eq' [b' ->]]|[eq' [n' ->]]]|H].
  all: try discriminate; try solve [right; destruct H as [f _]; discriminate f].
  1: left; destruct H as [eq' ->].
  2: destruct (Bool.bool_dec b b') as [eq|ne]; [left|right].
  4: destruct (PeanoNat.Nat.eq_dec n n') as [eq|ne]; [left|right].
  all: rewrite !(Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn; try intros [=f]; auto.
  exact (f_equal _ eq).
Defined.

Inductive value : type -> Set :=
  | VConst : forall {ty}, const ty -> value ty
  | VIfte  : forall {ty}, value TBool -> value ty -> value ty -> value ty
  | Vnot   : value TInt -> value TInt
  | Vneg   : value TInt -> value TInt
  | Vand   : value TBool -> value TBool -> value TBool
  | Vor    : value TBool -> value TBool -> value TBool
  | Vxor   : value TBool -> value TBool -> value TBool
  | Vplus  : value TInt -> value TInt -> value TInt
  | Vminus : value TInt -> value TInt -> value TInt
  | Vmult  : value TInt -> value TInt -> value TInt
  | Vdiv   : value TInt -> value TInt -> value TInt
  | Veq    : value TInt -> value TInt -> value TBool
  | Vneq   : value TInt -> value TInt -> value TBool
  | Vle    : value TInt -> value TInt -> value TBool
  | Vlt    : value TInt -> value TInt -> value TBool
  | Vge    : value TInt -> value TInt -> value TBool
  | Vgt    : value TInt -> value TInt -> value TBool
.

Lemma value_inv {ty} (x: value ty) :
  {c : const ty | x = VConst c} +
  {eb : value TBool & {et : value ty & {ef : value ty | x = VIfte eb et ef}}} +
  {e: value TInt | exists (eqt : TInt = ty), x = eq_rect _ value (Vnot e) _ eqt} +
  {e: value TInt | exists (eqt : TInt = ty), x = eq_rect _ value (Vneg e) _ eqt} +
  {e1: value TBool & {e2 : value TBool | exists (eqt : TBool = ty), x = eq_rect _ value (Vand e1 e2) _ eqt}} +
  {e1: value TBool & {e2 : value TBool | exists (eqt : TBool = ty), x = eq_rect _ value (Vor e1 e2) _ eqt}} +
  {e1: value TBool & {e2 : value TBool | exists (eqt : TBool = ty), x = eq_rect _ value (Vxor e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TInt = ty), x = eq_rect _ value (Vplus e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TInt = ty), x = eq_rect _ value (Vminus e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TInt = ty), x = eq_rect _ value (Vmult e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TInt = ty), x = eq_rect _ value (Vdiv e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TBool = ty), x = eq_rect _ value (Veq e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TBool = ty), x = eq_rect _ value (Vneq e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TBool = ty), x = eq_rect _ value (Vle e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TBool = ty), x = eq_rect _ value (Vlt e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TBool = ty), x = eq_rect _ value (Vge e1 e2) _ eqt}} +
  {e1: value TInt & {e2 : value TInt | exists (eqt : TBool = ty), x = eq_rect _ value (Vgt e1 e2) _ eqt}}.
Proof using.
  destruct x.
  1-16: left.
  1-15: left.
  1-14: left.
  1-13: left.
  1-12: left.
  1-11: left.
  1-10: left.
  1-9: left.
  1-8: left.
  1-7: left.
  1-6: left.
  1-5: left.
  1-4: left.
  1-3: left.
  1-2: left.
  1-1: left.
  2-17: right.
  all: repeat (eexists; try exists eq_refl).
Defined.

Lemma value_dec {ty} (v1 v2: value ty) : {v1 = v2} + {v1 <> v2}.
Proof.
  revert v2.
  induction v1 as [ty1 c1 | ty1 vb1 IHeb1 vt1 IHvt1 vf1 IHvf1 | v1 IH | v1 IH | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2 | v11 IH1 v12 IH2].
  all: intro v2.
  1, 2: destruct (value_inv v2) as [[[[[[[[[[[[[[[[
    (c2 & ->) | (vb2 & vt2 & vf2 & ->)] |
    (v2' & eqt2)] |
    (v2' & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)]; try (right; (try destruct eqt2); subst; simpl; discriminate).
  1: destruct (const_dec c1 c2); [left; subst; reflexivity | right; intros [=f]; apply sig2T_eq_type in f; contradiction].
  1: destruct (IHeb1 vb2).
  2: right; intros [=f]; contradiction.
  1: destruct (IHvt1 vt2).
  2: right; intros [=_ f]; apply sig2T_eq_type in f; contradiction.
  1: destruct (IHvf1 vf2).
  2: right; intros [=_ _ f]; apply sig2T_eq_type in f; contradiction.
  1: subst; left; reflexivity.
  1, 2: destruct (value_inv v2) as [[[[[[[[[[[[[[[[
    (c2 & ->) | (vb2 & vt2 & vf2 & ->)] |
    (v2' & eqt2)] |
    (v2' & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)]; try (right; (try destruct eqt2); subst; simpl; discriminate); try (right; destruct eqt2 as [type_eq eqt2]; revert eqt2; refine (match type_eq with eq_refl => fun f => _ end); subst; discriminate).
    1, 2: destruct (IH v2') as [eq|neq]; [left | right].
    1-4: destruct eqt2 as [type_eq ->].
    1, 3: exact (match type_eq with eq_refl => f_equal _ eq end).
    1, 2: refine (match type_eq with eq_refl => fun f => _ end); cbn in f.
    1, 2: injection f as f; exact (neq f).
  all: destruct (value_inv v2) as [[[[[[[[[[[[[[[[
    (c2 & ->) | (vb2 & vt2 & vf2 & ->)] |
    (v2' & eqt2)] |
    (v2' & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)] |
    (v21 & v22 & eqt2)]; try (right; (try destruct eqt2); subst; simpl; discriminate); try (right; destruct eqt2 as [type_eq eqt2]; revert eqt2; refine (match type_eq with eq_refl => fun f => _ end); subst; discriminate).
    all: destruct (IH1 v21) as [eq1|neq1]; [| right].
    all: try (destruct (IH2 v22) as [eq2|neq2]; [left| right]).
    all: subst.
    all: destruct eqt2 as [type_eq ->].
    all: try exact (match type_eq with eq_refl => eq_refl end).
    all: refine (match type_eq with eq_refl => fun f => _ end); cbn in f.
    all: injection f as f.
    all: contradiction.
Qed.