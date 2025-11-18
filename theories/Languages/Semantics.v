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

Ltac simpl_exist_type := repeat match goal with H : @existT type _ _ _ = existT _ _ _ |- _ => apply sig2T_eq_type in H end.

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
