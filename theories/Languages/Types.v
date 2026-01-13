Set Default Goal Selector "!".

From Reactive.Props Require Import Sigma.

Inductive type : Set :=
  | TBool
  | TInt
.

Lemma type_dec (x y: type): {x = y} + {x <> y}.
Proof.
  destruct x, y; try solve [left; reflexivity]; right; discriminate.
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
  destruct (dec TBool) as [Pbool | nP]; [|right; exact (ex_intro (fun ty => ~ P ty) _ nP)].
  destruct (dec TInt)  as [Pint  | nP]; [|right; exact (ex_intro (fun ty => ~ P ty) _ nP)].
  left; intros []; assumption.
Defined.

Definition type_eqb (x y: type): bool :=
  match x, y with
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
