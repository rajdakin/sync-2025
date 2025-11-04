Set Default Goal Selector "!".

From Stdlib Require Import Nat List String.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Identifier Sigma.

From Reactive.Datatypes Require Dict.

Inductive unop: type -> type -> Set :=
  | Uop_not: unop TInt TInt
  | Uop_neg: unop TInt TInt
.

Inductive binop: type -> type -> type -> Set :=
  (** Boolean binop *)
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

Inductive exp: type -> Set :=
  | EConst {ty}: const ty -> exp ty
  | EVar (b: binder): exp (snd b)
  | EUnop {ty tout}: unop ty tout -> exp ty -> exp tout
  | EBAnd: exp TBool -> exp TBool -> exp TBool
  | EBOr: exp TBool -> exp TBool -> exp TBool
  | EBinop {ty1 ty2 tout}: binop ty1 ty2 tout -> exp ty1 -> exp ty2 -> exp tout
  | EIfte {ty}: exp TBool -> exp ty -> exp ty -> exp ty
.

Inductive stmt :=
  | SAssign (b: binder): exp (snd b) -> stmt
  | SSeq : stmt -> stmt -> stmt
  | SNop : stmt
.


(** ** Equalities *)

Lemma unop_inv {ty tout} (x: unop ty tout) :
  {exists (eq1 : ty = TInt) (eq2 : tout = TInt), x = eq_rect _ (unop _) (eq_rect _ (fun ty => unop ty _) Uop_not _ (eq_sym eq1)) _ (eq_sym eq2)} +
  {exists (eq1 : ty = TInt) (eq2 : tout = TInt), x = eq_rect _ (unop _) (eq_rect _ (fun ty => unop ty _) Uop_neg _ (eq_sym eq1)) _ (eq_sym eq2)}.
Proof using.
  destruct x; [left|right]; exists eq_refl, eq_refl; exact eq_refl.
Defined.
Lemma unop_dec {ty tout} (x y: unop ty tout) : {x = y} + {x <> y}.
Proof.
  destruct (unop_inv x) as [H1|H1].
  all: destruct (unop_inv y) as [H2|H2].
  1,4: left.
  3,4: right.
  all: destruct H1 as [eq1 [eq2 ->]].
  all: destruct H2 as [-> [-> ->]].
  all: rewrite !(Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn.
  all: rewrite !(Eqdep_dec.UIP_dec type_dec _ eq_refl); cbn.
  1-2: reflexivity.
  all: discriminate.
Defined.

Definition unop_eqb {tyx toutx} (x: unop tyx toutx) {tyy touty} (y: unop tyy touty): bool :=
  match x, y with
    | Uop_not, Uop_not => true
    | Uop_neg, Uop_neg => true
    | _, _ => false
  end.

Lemma binop_inv {ty1 ty2 tout} (x: binop ty1 ty2 tout) :
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
  {exists (eq1 : ty1 = _) (eq2 : ty2 = _) (eqo : tout = _), x = eq_rect _ (binop _ _) (eq_rect _ (fun ty => binop _ ty _) (eq_rect _ (fun ty => binop ty _ _) Bop_gt _ (eq_sym eq1)) _ (eq_sym eq2)) _ (eq_sym eqo)}.
Proof using.
  destruct x.
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
  2-11: right.
  all: exists eq_refl, eq_refl, eq_refl; exact eq_refl.
Defined.
Lemma binop_dec {ty1 ty2 tout} (x y: binop ty1 ty2 tout) : {x = y} + {x <> y}.
Proof.
  pose proof (binop_inv x) as H1.
  repeat destruct H1 as [ H1 | H1 ].
  all: pose proof (binop_inv y) as H.
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

Definition binop_eqb {ty1x ty2x toutx} (x: binop ty1x ty2x toutx) {ty1y ty2y touty} (y: binop ty1y ty2y touty): bool :=
  match x, y with
    | Bop_xor, Bop_xor => true
    | Bop_plus, Bop_plus => true
    | Bop_minus, Bop_minus => true
    | Bop_mult, Bop_mult => true
    | Bop_div, Bop_div => true
    | Bop_eq, Bop_eq => true
    | Bop_neq, Bop_neq => true
    | Bop_lt, Bop_lt => true
    | Bop_le, Bop_le => true
    | Bop_gt, Bop_gt => true
    | Bop_ge, Bop_ge => true
    | _, _ => false
  end.

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

Definition const_eqb {ty1} (c1: const ty1) {ty2} (c2: const ty2): bool :=
  match c1, c2 with
    | CVoid, CVoid => true
    | CBool b1, CBool b2 => Bool.eqb b1 b2
    | CInt n1, CInt n2 => PeanoNat.Nat.eqb n1 n2
    | _, _ => false
  end.

Fixpoint exp_eqb {ty1} (e1: exp ty1) {ty2} (e2: exp ty2): bool :=
  match e1, e2 with
    | EConst c1, EConst c2 => const_eqb c1 c2
    | EVar b1, EVar b2 => binder_eqb b1 b2
    | EUnop op1 e1, EUnop op2 e2 =>
      (unop_eqb op1 op2) && (exp_eqb e1 e2)
    | EBAnd e11 e12, EBAnd e21 e22 =>
      (exp_eqb e11 e21) && (exp_eqb e12 e22)
    | EBOr e11 e12, EBOr e21 e22 =>
      (exp_eqb e11 e21) && (exp_eqb e12 e22)
    | EBinop op1 e11 e12, EBinop op2 e21 e22 =>
      (binop_eqb op1 op2) && (exp_eqb e11 e21) && (exp_eqb e12 e22)
    | EIfte e11 e12 e13, EIfte e21 e22 e23 =>
      (exp_eqb e11 e21) && (exp_eqb e12 e22) && (exp_eqb e13 e23)
    | _, _ => false
  end.

Fixpoint stmt_eqb (s1 s2: stmt): bool :=
  match s1, s2 with
    | SAssign (i1, ty1) e1, SAssign (i2, ty2) e2 =>  PeanoNat.Nat.eqb i1 i2 && exp_eqb e1 e2
    | SSeq s11 s12, SSeq s21 s22 => stmt_eqb s11 s21 && stmt_eqb s12 s22
    | SNop, SNop => true
    | _, _ => false
  end.


(** ** Method *)

Fixpoint is_substmt (sub s: stmt): bool :=
  stmt_eqb sub s || match s with
    | SAssign _ _ | SNop => false
    | SSeq sl sr => is_substmt sub sl || is_substmt sub sr 
  end.

Record method := mk_method {
  m_name: string;

  m_in: list binder;
  m_out: list binder;
  m_vars: list binder;

  m_body: stmt;

  m_out_assign: forall b, In b m_out -> exists (e: exp _), is_substmt (SAssign b e) m_body = true
}.


(** ** Semantics *)

Inductive value : type -> Set :=
  | VConst : forall {ty}, const ty -> value ty
  | VUnop  : forall {ty tout}, unop ty tout -> value ty -> value tout
  | VBAnd  : value TBool -> value TBool -> value TBool
  | VBOr   : value TBool -> value TBool -> value TBool
  | VBinop : forall {ty1 ty2 tout}, binop ty1 ty2 tout -> value ty1 -> value ty2 -> value tout
  | VIfte  : forall {ty}, value TBool -> value ty -> value ty -> value ty
.

Lemma value_inv {ty} (x: value ty) :
  {c : const ty | x = VConst c} +
  {tin : type & {op : unop tin ty & {e : value tin | x = VUnop op e}}} +
  {eq : ty = _ & {e1 : value _ & {e2 : value _ | x = eq_rect _ value (VBAnd e1 e2) _ (eq_sym eq)}}} +
  {eq : ty = _ & {e1 : value _ & {e2 : value _ | x = eq_rect _ value (VBOr e1 e2) _ (eq_sym eq)}}} +
  {ty1 : type & {ty2 : type & {op : binop ty1 ty2 ty & {e1 : value ty1 & {e2 : value ty2 | x = VBinop op e1 e2}}}}} +
  {eb : value TBool & {et : value ty & {ef : value ty | x = VIfte eb et ef}}}.
Proof using.
  destruct x.
  1-5: left.
  1-4: left.
  1-3: left.
  1-2: left.
  1-1: left.
  2-6: right.
  all: try solve [repeat eexists; exact eq_refl].
  1-2: exists eq_refl; exact (existT _ _ (exist _ _ eq_refl)).
Defined.
Lemma value_dec {ty} (e1 e2: value ty) : {e1 = e2} + {e1 <> e2}.
Proof.
  revert e2.
  induction e1 as [ ty c | tin tout op e1 IH | e11 IH1 e12 IH2 | e11 IH1 e12 IH2 | ty1 ty2 tout op e11 IH1 e12 IH2 | ty eb1 IHb et1 IHt ef1 IHf ].
  - intros e2; destruct (value_inv e2) as [ [ [ [ [
      (c' & ->) | (tin & op & e1' & ->) ] | (e & e1' & e2' & ->) ] | (e & e1' & e2' & ->) ] | (ty1 & ty2 & op & e1' & e2' & ->) ] | (eb & et & ef & ->) ].
    1: destruct (const_dec c c') as [e|n]; [left; exact (f_equal _ e)|right; intros [=f]; apply sig2T_eq_type in f; exact (n f)].
    all: right; try destruct H as [eq1 ->]; subst; discriminate.
  - intros e2; destruct (value_inv e2) as [ [ [ [ [
      (c' & ->) | (tin' & op' & e1' & ->) ] | (e & e1' & e2' & ->) ] | (e & e1' & e2' & ->) ] | (ty1 & ty2 & op' & e1' & e2' & ->) ] | (eb & et & ef & ->) ].
    1,3-6: right; try destruct H as [eq1 ->]; subst; discriminate.
    destruct (type_dec tin tin') as [<-|ne]; [|right; intros [=f _ _]; exact (ne f)].
    destruct (unop_dec op op') as [<-|ne]; [|right; intros [=f _]; exact (ne (sig2T_eq_type (sig2T_eq_type f)))].
    destruct (IH e1') as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    left; reflexivity.
  - intros e2; destruct (value_inv e2) as [ [ [ [ [
      (c' & ->) | (tin' & op' & e1' & ->) ] | (e & e1' & e2' & ->) ] | (e & e1' & e2' & ->) ] | (ty1 & ty2 & op' & e1' & e2' & ->) ] | (eb & et & ef & ->) ].
    1-2,4-6: right; subst; try discriminate; rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); discriminate.
    rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl).
    destruct (IH1 e1') as [<-|ne]; [|right; intros [=f]; exact (ne f)].
    destruct (IH2 e2') as [<-|ne]; [|right; intros [=f]; exact (ne f)].
    left; reflexivity.
  - intros e2; destruct (value_inv e2) as [ [ [ [ [
      (c' & ->) | (tin' & op' & e1' & ->) ] | (e & e1' & e2' & ->) ] | (e & e1' & e2' & ->) ] | (ty1 & ty2 & op' & e1' & e2' & ->) ] | (eb & et & ef & ->) ].
    1-3,5-6: right; subst; try discriminate; rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl); discriminate.
    rewrite (Eqdep_dec.UIP_dec type_dec _ eq_refl).
    destruct (IH1 e1') as [<-|ne]; [|right; intros [=f]; exact (ne f)].
    destruct (IH2 e2') as [<-|ne]; [|right; intros [=f]; exact (ne f)].
    left; reflexivity.
  - intros e2; destruct (value_inv e2) as [ [ [ [ [
      (c' & ->) | (tin' & op' & e1' & ->) ] | (e & e1' & e2' & ->) ] | (e & e1' & e2' & ->) ] | (ty1' & ty2' & op' & e1' & e2' & ->) ] | (eb & et & ef & ->) ].
    1-4,6: right; try destruct H as [eq1 ->]; subst; discriminate.
    destruct (type_dec ty1 ty1') as [<-|ne]; [|right; intros [=f _ _ _]; exact (ne f)].
    destruct (type_dec ty2 ty2') as [<-|ne]; [|right; intros [=f _ _]; exact (ne f)].
    destruct (binop_dec op op') as [<-|ne]; [|right; intros [=f _]; exact (ne (sig2T_eq_type (sig2T_eq_type (sig2T_eq_type f))))].
    destruct (IH1 e1') as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    destruct (IH2 e2') as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    left; reflexivity.
  - intros e2; destruct (value_inv e2) as [ [ [ [ [
      (c' & ->) | (tin' & op' & e1' & ->) ] | (e & e1' & e2' & ->) ] | (e & e1' & e2' & ->) ] | (ty1' & ty2' & op' & e1' & e2' & ->) ] | (eb2 & et2 & ef2 & ->) ].
    1-5: right; try destruct H as [eq1 ->]; subst; discriminate.
    destruct (IHb eb2) as [<-|ne]; [|right; intros [=f]; exact (ne f)].
    destruct (IHt et2) as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    destruct (IHf ef2) as [<-|ne]; [|right; intros [=f]; exact (ne (sig2T_eq_type f))].
    left; reflexivity.
Defined.

Definition stack := Dict.t (sigT value).

Inductive sem_exp: stack -> forall {ty}, exp ty -> value ty -> Prop :=
  | SeConst (s: stack) {ty} (c: const ty):
      sem_exp s (EConst c) (VConst c)

  | SeVar (s: stack) (b: binder) (v: value _):
      Dict.maps_to (fst b) (existT value (snd b) v) s ->
      sem_exp s (EVar b) v

  | SeUnop (s: stack) {ty tout} (op: unop ty tout) (e: exp _) (v: value _):
      sem_exp s e v ->
      sem_exp s (EUnop op e) (VUnop op v)

  | SeBAndConstF (s: stack) (e1 e2: exp _):
      sem_exp s e1 (VConst (CBool false)) ->
      sem_exp s (EBAnd e1 e2) (VConst (CBool false))

  | SeBAndConstT (s: stack) (e1 e2: exp _) (v2: value _):
      sem_exp s e1 (VConst (CBool true)) ->
      sem_exp s e2 v2 ->
      sem_exp s (EBAnd e1 e2) v2

  | SeBAndDefer (s: stack) (e1 e2: exp _) (v1 v2: value _):
      sem_exp s e1 v1 ->
      v1 <> VConst (CBool true) ->
      v1 <> VConst (CBool false) ->
      sem_exp s e2 v2 ->
      sem_exp s (EBAnd e1 e2) (VBAnd v1 v2)

  | SeBOrConstF (s: stack) (e1 e2: exp _) (v2: value _):
      sem_exp s e1 (VConst (CBool false)) ->
      sem_exp s e2 v2 ->
      sem_exp s (EBOr e1 e2) v2

  | SeBOrConstT (s: stack) (e1 e2: exp _):
      sem_exp s e1 (VConst (CBool true)) ->
      sem_exp s (EBOr e1 e2) (VConst (CBool true))

  | SeBOrDefer (s: stack) (e1 e2: exp _) (v1 v2: value _):
      sem_exp s e1 v1 ->
      v1 <> VConst (CBool true) ->
      v1 <> VConst (CBool false) ->
      sem_exp s e2 v2 ->
      sem_exp s (EBOr e1 e2) (VBOr v1 v2)

  | SeBinop (s: stack) {ty1 ty2 tout} (op: binop ty1 ty2 tout) (e1 e2: exp _) (v1 v2: value _):
      sem_exp s e1 v1 ->
      sem_exp s e2 v2 ->
      sem_exp s (EBinop op e1 e2) (VBinop op v1 v2)

  | SeIfte (s: stack) {ty} (e1: exp _) (e2 e3: exp ty) (v1 v2 v3: value _):
      sem_exp s e1 v1 ->
      sem_exp s e2 v2 ->
      sem_exp s e3 v3 ->
      sem_exp s (EIfte e1 e2 e3) (VIfte v1 v2 v3).

Inductive sem_stmt: stack -> stmt -> stack -> Prop :=
  | SeAssign (s: stack) (name: ident) (ty: type) (e: exp _) (v: value _):
      sem_exp s e v ->
      sem_stmt s (SAssign (name, ty) e) (Dict.add name (existT value ty v) s)

  | SeSeq (s1 s2 s3: stack) (st1 st2: stmt):
      sem_stmt s1 st1 s2 ->
      sem_stmt s2 st2 s3 ->
      sem_stmt s1 (SSeq st1 st2) s3

  | SeNop (s: stack):
      sem_stmt s SNop s.


(** ** Properties *)

Definition try_cast_value_type (ty: type) {ty'} (v: value ty'): option (value ty) := match type_dec ty ty' with
  | left e => Some (eq_rect _ value v _ (eq_sym e))
  | right _ => None
end.

Fixpoint eval_exp {ty} (e: exp ty) (s: stack): option (value ty) :=
  match e with
    | EConst c => Some (VConst c)
    | EVar (name, typ) => match Dict.find name s with Some (existT _ ty' v) => try_cast_value_type typ v | None => None end
    | EUnop op e => match eval_exp e s with
      | Some v => Some (VUnop op v)
      | None => None
    end
    | EBAnd e1 e2 => match eval_exp e1 s, eval_exp e2 s with
      | Some (VConst (CBool false)), _ => Some (VConst (CBool false))
      | Some (VConst (CBool true)), Some v2 => Some v2
      | Some v1, Some v2 => Some (VBAnd v1 v2)
      | _, _ => None
    end
    | EBOr e1 e2 => match eval_exp e1 s, eval_exp e2 s with
      | Some (VConst (CBool false)), Some v2 => Some v2
      | Some (VConst (CBool true)), _ => Some (VConst (CBool true))
      | Some v1, Some v2 => Some (VBOr v1 v2)
      | _, _ => None
    end
    | EBinop op e1 e2 => match eval_exp e1 s, eval_exp e2 s with
      | Some v1, Some v2 => Some (VBinop op v1 v2)
      | _, _ => None
    end
    | EIfte e1 e2 e3 => match eval_exp e1 s, eval_exp e2 s, eval_exp e3 s with
      | Some v1, Some v2, Some v3 => Some (VIfte v1 v2 v3)
      | _, _, _ => None
    end
  end.


(** ** Lemmas *)

Lemma unop_eqb_refl {ty tout} (op: unop ty tout):
  unop_eqb op op = true.
Proof.
  destruct op; reflexivity.
Qed.

(* Lemma unop_eqb_to_eq {ty tout} (op1 op2: unop ty tout):
  unop_eqb op1 op2 = true -> op1 = op2.
Proof.
  intros H.
  destruct op1, op2; (reflexivity || inversion H).
Qed. *)

Lemma binop_eqb_refl {ty1 ty2 tout} (op: binop ty1 ty2 tout):
  binop_eqb op op = true.
Proof.
  destruct op; reflexivity.
Qed.

(* Lemma binop_eqb_to_eq (op1 op2: binop):
  binop_eqb op1 op2 = true -> op1 = op2.
Proof.
  intros H.
  destruct op1, op2; reflexivity || inversion H.
Qed. *)

Lemma const_eqb_refl {ty} (c: const ty):
  const_eqb c c = true.
Proof.
  destruct c as [ | b | n ].
  - reflexivity.
  - apply Bool.eqb_true_iff.
    reflexivity.
  - apply PeanoNat.Nat.eqb_refl.
Qed.

(* Lemma const_eqb_to_eq (c1 c2: const):
  const_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros H.
  destruct c1.
  - destruct c2.
    + reflexivity.
    + inversion H.
    + inversion H.
  - destruct c2.
    + inversion H.
    + simpl in H.
      f_equal.
      apply Bool.eqb_true_iff.
      assumption.
    + inversion H.
  - destruct c2.
    + inversion H.
    + inversion H.
    + apply PeanoNat.Nat.eqb_eq in H.
      subst.
      reflexivity.
Qed. *)

Lemma exp_eqb_refl {ty} (e: exp ty):
  exp_eqb e e = true.
Proof.
  induction e.
  - apply const_eqb_refl.
  - apply binder_eqb_refl.
  - apply andb_true_intro.
    split; [ | assumption ].
    apply unop_eqb_refl.
  - apply andb_true_intro.
    split; assumption.
  - apply andb_true_intro.
    split; assumption.
  - apply andb_true_intro.
    split; [ | assumption ].
    rewrite binop_eqb_refl.
    assumption.
  - simpl.
    rewrite IHe1, IHe2, IHe3.
    reflexivity.
Qed.

(* Lemma exp_eqb_to_eq (e1 e2: exp):
  exp_eqb e1 e2 = true -> e1 = e2.
Proof.
  intros H.
  revert e2 H.
  induction e1 as [ c1 | b1 | b1 | op1 e1 IH | op1 e11 IH1 e12 IH2 | e11 IH1 e12 IH2 e13 IH3 ]; intros e2 H.
  - destruct e2; try inversion H.
    apply const_eqb_to_eq in H1.
    subst.
    reflexivity.
  - destruct e2; try inversion H.
    apply binder_eqb_to_eq in H1.
    subst.
    reflexivity.
  - destruct e2; try inversion H.
    apply binder_eqb_to_eq in H1.
    subst.
    reflexivity.
  -  destruct e2; try inversion H.
    apply andb_prop in H1 as [ H1 H2 ].
    apply unop_eqb_to_eq in H1.
    apply IH in H2.
    f_equal; assumption.
  - destruct e2; try inversion H.
    apply andb_prop in H1 as [ H1 H2 ].
    apply andb_prop in H1 as [ H3 H1 ].
    apply IH1 in H1.
    apply IH2 in H2.
    apply binop_eqb_to_eq in H3.
    rewrite H1, H2, H3.
    reflexivity.
  - destruct e2; try inversion H.
    apply andb_prop in H1 as [ H1 H3 ].
    apply andb_prop in H1 as [ H1 H2 ].
    apply IH1 in H1.
    apply IH2 in H2.
    apply IH3 in H3.
    f_equal; assumption.
Qed. *)
