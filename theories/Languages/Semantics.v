Set Default Goal Selector "!".

From Stdlib Require Import ZArith.
From Stdlib Require Import Nat.
From Reactive.Datatypes Require Dict Stream.
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
  | CBool: bool -> const TBool
  | CInt: nat -> const TInt
.
Lemma const_inv {ty} (x: const ty) :
  {eq : ty = _ & {b : bool | x = eq_rect _ const (CBool b) _ (eq_sym eq)}} +
  {eq : ty = _ & {n : nat | x = eq_rect _ const (CInt n) _ (eq_sym eq)}}.
Proof using.
  destruct x as [b|n]; [left|right]; exists eq_refl; [exists b|exists n]; exact eq_refl.
Defined.

Lemma const_dec {ty} (x y: const ty) : {x = y} + {x <> y}.
Proof.
  destruct x as [b | n ].
  all: destruct (const_inv y) as [[eq' [b' ->]]|[eq' [n' ->]]].
  all: try discriminate; try solve [right; destruct H as [f _]; discriminate f].
  1: destruct (Bool.bool_dec b b') as [eq|ne]; [left|right].
  3: destruct (Nat.eq_dec n n') as [eq|ne]; [left|right].
  all: rewrite !(Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn; try intros [=f]; auto.
  all: exact (f_equal _ eq).
Defined.

Definition const_eqb {ty1} (c1: const ty1) {ty2} (c2: const ty2): bool :=
  match c1, c2 with
    | CBool b1, CBool b2 => Bool.eqb b1 b2
    | CInt n1, CInt n2 => Nat.eqb n1 n2
    | _, _ => false
  end.

Lemma const_eqb_refl {ty} (c: const ty):
  const_eqb c c = true.
Proof.
  destruct c as [ b | n ].
  - apply Bool.eqb_true_iff.
    reflexivity.
  - apply Nat.eqb_refl.
Qed.

Inductive value : type -> Set :=
  | VBool : bool -> value TBool
  | VInt  : Z    -> value TInt.

Definition const_to_value {ty} (c: const ty): value ty:=
  match c with
  | CBool b => VBool b
  | CInt n => VInt (Z.of_nat n)
  end.

Lemma value_inv {ty} (x: value ty) :
  {b : bool | exists (eqt : TBool = ty), x = eq_rect _ value (VBool b) _ eqt} +
  {z : Z | exists (eqt : TInt = ty), x = eq_rect _ value (VInt z) _ eqt}.
Proof using.
  destruct x.
  1: left.
  2: right.
  1: exists b.
  2: exists z.
  all: exists eq_refl.
  all: reflexivity.
Defined.

Lemma value_dec {ty} (v1 v2: value ty) : {v1 = v2} + {v1 <> v2}.
Proof.
  destruct v1 as [b1 | z1].
  all: destruct (value_inv v2) as [[b2 eqt2] | [z2 eqt2]].
  2, 3: right; destruct eqt2; discriminate.
  1: destruct (Bool.bool_dec b1 b2) as [eq | neq].
  3: destruct (Z_noteq_dec z1 z2) as [neq | eq].
  2, 3: right.
  1, 4: left.
  all: destruct eqt2 as [ ? [=->]]; subst.
  all: rewrite (Eqdep_dec.UIP_dec type_dec x eq_refl).
  all: cbn.
  all: try reflexivity.
  all: intro f; injection f.
  all: intro; contradiction.
Defined.

Definition history := Dict.t {ty & Stream.t (value ty)}.
Definition in_history (h : history) '((v, ty) : nat * type) := match Dict.find v h with
  | Some (existT _ ty' _) => ty' = ty
  | None => False
end.
Definition in_history' (h : history) '((v, ty) : nat * type) := exists s, Dict.find v h = Some (existT _ ty s).

Definition h_maps_to {ty} i (s: Stream.t (value ty)) (h: history) := Dict.maps_to i (existT _ ty s) h.

Lemma h_maps_to_eq {ty} i (s s': Stream.t (value ty)) (h: history) : h_maps_to i s h -> h_maps_to i s' h -> s = s'.
Proof.
  unfold h_maps_to.
  unfold Dict.maps_to.
  intros maps maps'.
  rewrite maps in maps'.
  injection maps'; intro eqT.
  apply (sig2T_eq type_dec) in eqT.
  assumption.
Qed.

Definition eq_support (support: list nat) (h1 h2: history) := forall n, List.In n support -> Dict.find n h1 = Dict.find n h2.

Lemma eq_support_app (s1 s2: list nat) (h1 h2: history) :
  eq_support s1 h1 h2 -> eq_support s2 h1 h2 -> eq_support (s1 ++ s2) h1 h2.
Proof.
  unfold eq_support.
  intros eq1 eq2 n isin.
  rewrite List.in_app_iff in isin.
  specialize (eq1 n).
  specialize (eq2 n).
  destruct isin as [in1 | in2].
  all: tauto.
Qed.

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

Definition extract_stream (ty : type) (t: nat) {ty'} (s : Stream.t (value ty')) : option (value ty) := match type_dec ty' ty with
  | left e => Some (eq_rect ty' value (Stream.nth t s) ty e)
  | right _ => None
end.

Lemma extract_stream_eqty : forall {ty} (s : Stream.t (value ty)) n, extract_stream ty n s = Some (Stream.nth n s).
Proof using.
  intros ty s n.
  unfold extract_stream.
  rewrite type_dec_same.
  reflexivity.
Qed.

Definition sub_history (sub h: history) := Dict.inclusion sub h.

Lemma sub_history_refl h : sub_history h h.
Proof.
  unfold sub_history.
  rewrite Dict.inclusion_is_list_incl.
  apply List.incl_refl.
Qed.

Lemma sub_history_trans h1 h2 h3 : sub_history h1 h2 -> sub_history h2 h3 -> sub_history h1 h3.
Proof.
  unfold sub_history.
  do 3 rewrite Dict.inclusion_is_list_incl.
  unfold List.incl.
  intros sub12 sub23 a isin.
  apply (sub23 a (sub12 a isin)).
Qed.

Lemma sub_history_antirefl h1 h2 : sub_history h1 h2 -> sub_history h2 h1 -> h1 = h2.
Proof.
  unfold sub_history.
  intros sub12 sub21.
  rewrite <- (Dict.equivalence_is_eq h1 h2).
  unfold Dict.equivalence.
  split; assumption.
Qed.


(* Operators *)
Definition vnot (v: value TInt) : value TInt :=
  match v with
  | VInt z => VInt (1%Z - z)
  end.

Definition vneg (v: value TInt) : value TInt :=
  match v with
  | VInt z => VInt (-z)
  end.

Definition vand (v1 v2: value TBool) : value TBool :=
  match v1, v2 with
  | VBool b1, VBool b2 => VBool (b1 && b2)
  end.

Definition vor (v1 v2: value TBool) : value TBool :=
  match v1, v2 with
  | VBool b1, VBool b2 => VBool (b1 || b2)
  end.

Definition vxor (v1 v2: value TBool) : value TBool :=
  match v1, v2 with
  | VBool b1, VBool b2 => VBool (xorb b1 b2)
  end.

Definition vplus (v1 v2: value TInt) : value TInt :=
  match v1, v2 with
  | VInt z1, VInt z2 => VInt (z1 + z2)
  end.

Definition vminus (v1 v2: value TInt) : value TInt :=
  match v1, v2 with
  | VInt z1, VInt z2 => VInt (z1 - z2)
  end.

Definition vmult (v1 v2: value TInt) : value TInt :=
  match v1, v2 with
  | VInt z1, VInt z2 => VInt (z1 * z2)
  end.

Definition vdiv (v1 v2: value TInt) : value TInt :=
  match v1, v2 with
  | VInt z1, VInt z2 => VInt (z1 / z2)
  end.

Definition veq (v1 v2: value TInt) : value TBool :=
  match v1, v2 with
  | VInt z1, VInt z2 => VBool (Z.eqb z1 z2)
  end.

Definition vneq (v1 v2: value TInt) : value TBool :=
  match v1, v2 with
  | VInt z1, VInt z2 => VBool (negb (Z.eqb z1 z2))
  end.

Definition vle (v1 v2: value TInt) : value TBool :=
  match v1, v2 with
  | VInt z1, VInt z2 => VBool (Z.leb z1 z2)
  end.

Definition vlt (v1 v2: value TInt) : value TBool :=
  match v1, v2 with
  | VInt z1, VInt z2 => VBool (Z.ltb z1 z2)
  end.

Definition vge (v1 v2: value TInt) : value TBool :=
  match v1, v2 with
  | VInt z1, VInt z2 => VBool (Z.geb z1 z2)
  end.

Definition vgt (v1 v2: value TInt) : value TBool :=
  match v1, v2 with
  | VInt z1, VInt z2 => VBool (Z.gtb z1 z2)
  end.

Definition vifte {ty} (vb: value TBool) (vt vf: value ty) : value ty :=
  match vb with
  | VBool b => match b with
    | true => vt
    | false => vf
    end
  end.
