Set Default Goal Selector "!".

From Stdlib Require Import Nat List String.
From Reactive.Datatypes Require Dict.
From Reactive.Props Require Import Identifier Sigma.
From Reactive.Languages Require Import Semantics.

Import ListNotations.

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
  | EVar (b: binder): exp (binder_ty b)
  | EUnop {ty tout}: unop ty tout -> exp ty -> exp tout
  | EBAnd: exp TBool -> exp TBool -> exp TBool
  | EBOr: exp TBool -> exp TBool -> exp TBool
  | EBinop {ty1 ty2 tout}: binop ty1 ty2 tout -> exp ty1 -> exp ty2 -> exp tout
  | EIfte {ty}: exp TBool -> exp ty -> exp ty -> exp ty
.

Inductive stmt :=
  | SAssign (b: binder): exp (binder_ty b) -> stmt
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
    | SAssign b1 e1, SAssign b2 e2 => binder_eqb b1 b2 && exp_eqb e1 e2
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

Record method_pair := mk_method {
  m_name: string;

  m_in: list binder;
  m_out: list binder;
  m_locals: list binder;
  m_vars := m_in ++ m_out ++ m_locals;
  m_pre: list binder;

  m_init: stmt;
  m_step: stmt;

  m_out_assign_init: forall b, In b m_out -> exists (e: exp _), is_substmt (SAssign b e) m_init = true;
  m_out_assign_step: forall b, In b m_out -> exists (e: exp _), is_substmt (SAssign b e) m_step = true
}.


(** ** Semantics *)

Inductive sem_unop : forall {tyin tyout : type}, unop tyin tyout -> value tyin -> value tyout -> Prop :=
  | SeNot (v: value TInt) : sem_unop Uop_not v (vnot v)
  | SeNeg (v: value TInt) : sem_unop Uop_neg v (vneg v).

Inductive sem_binop : forall {ty1 ty2 tyout : type}, binop ty1 ty2 tyout -> value ty1 -> value ty2 -> value tyout -> Prop :=
  | SeXor (v1 v2: value TBool) : sem_binop Bop_xor v1 v2 (vxor v1 v2)
  | SePlus (v1 v2: value TInt) : sem_binop Bop_plus v1 v2 (vplus v1 v2)
  | SeMinus (v1 v2: value TInt) : sem_binop Bop_minus v1 v2 (vminus v1 v2)
  | SeMult (v1 v2: value TInt) : sem_binop Bop_mult v1 v2 (vmult v1 v2)
  | SeDiv (v1 v2: value TInt) : sem_binop Bop_div v1 v2 (vdiv v1 v2)
  | SeEq (v1 v2: value TInt) : sem_binop Bop_eq v1 v2 (veq v1 v2)
  | SeNeq (v1 v2: value TInt) : sem_binop Bop_neq v1 v2 (vneq v1 v2)
  | SeLe (v1 v2: value TInt) : sem_binop Bop_le v1 v2 (vle v1 v2)
  | SeLt (v1 v2: value TInt) : sem_binop Bop_lt v1 v2 (vlt v1 v2)
  | SeGe (v1 v2: value TInt) : sem_binop Bop_ge v1 v2 (vge v1 v2)
  | SeGt (v1 v2: value TInt) : sem_binop Bop_gt v1 v2 (vgt v1 v2).

Inductive sem_exp: stack -> forall {ty}, exp ty -> value ty -> Prop :=
  | SeConst (s: stack) {ty} (c: const ty):
      sem_exp s (EConst c) (const_to_value c)

  | SeVar (s: stack) (b: binder) (v: value _):
      Dict.maps_to (binder_id b) (existT value (binder_ty b) v) s ->
      sem_exp s (EVar b) v

  | SeUnop (s: stack) {ty tout} (op: unop ty tout) (e: exp _) (vin vout: value _):
      sem_exp s e vin ->
      sem_unop op vin vout ->
      sem_exp s (EUnop op e) vout

  | SeBAndConstF (s: stack) (e1 e2: exp _):
      sem_exp s e1 (VBool false) ->
      sem_exp s (EBAnd e1 e2) (VBool false)

  | SeBAndConstT (s: stack) (e1 e2: exp _) (v2: value _):
      sem_exp s e1 (VBool true) ->
      sem_exp s e2 v2 ->
      sem_exp s (EBAnd e1 e2) v2

  | SeBOrConstF (s: stack) (e1 e2: exp _) (v2: value _):
      sem_exp s e1 (VBool false) ->
      sem_exp s e2 v2 ->
      sem_exp s (EBOr e1 e2) v2

  | SeBOrConstT (s: stack) (e1 e2: exp _):
      sem_exp s e1 (VBool true) ->
      sem_exp s (EBOr e1 e2) (VBool true)

  | SeBinop (s: stack) {ty1 ty2 tout} (op: binop ty1 ty2 tout) (e1 e2: exp _) (v1 v2 vout: value _):
      sem_exp s e1 v1 ->
      sem_exp s e2 v2 ->
      sem_binop op v1 v2 vout ->
      sem_exp s (EBinop op e1 e2) vout

  | SeIfte (s: stack) {ty} (e1: exp _) (e2 e3: exp ty) (v1 v2 v3: value _):
      sem_exp s e1 v1 ->
      sem_exp s e2 v2 ->
      sem_exp s e3 v3 ->
      sem_exp s (EIfte e1 e2 e3) (vifte v1 v2 v3).

Inductive sem_stmt: stack -> stmt -> stack -> Prop :=
  | SeAssign (s: stack) (b: binder) (e: exp _) (v: value _):
      sem_exp s e v ->
      sem_stmt s (SAssign b e) (Dict.add (binder_id b) (existT value (binder_ty b) v) s)

  | SeSeq (s1 s2 s3: stack) (st1 st2: stmt):
      sem_stmt s1 st1 s2 ->
      sem_stmt s2 st2 s3 ->
      sem_stmt s1 (SSeq st1 st2) s3

  | SeNop (s: stack):
      sem_stmt s SNop s.

Definition sem_node (inputs: Stream.t stack) (ss: Stream.t stack) (m: method_pair): Prop :=
  sem_stmt (Stream.hd inputs) m.(m_init) (Stream.hd ss) /\
  forall n: nat, sem_stmt (
    Dict.union (Stream.nth n ss) (Stream.nth (S n) inputs)
    ) m.(m_step) (Stream.nth (S n) ss).

Fixpoint var_of_exp_aux {ty} (e: exp ty) (acc: list binder): list binder :=
  match e with
    | EConst _ => acc
    | EVar b => b :: acc
    | EUnop _ e => var_of_exp_aux e acc
    | EBAnd e1 e2 =>  var_of_exp_aux e1 (var_of_exp_aux e2 acc)
    | EBOr e1 e2 =>  var_of_exp_aux e1 (var_of_exp_aux e2 acc)
    | EBinop _ e1 e2 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 acc)
    | EIfte e1 e2 e3 =>
      var_of_exp_aux e1 (var_of_exp_aux e2 (var_of_exp_aux e3 acc))
  end.

Definition var_of_exp {ty} (e: exp ty): list binder:=
  var_of_exp_aux e [].


(** ** Properties *)

Definition try_cast_value_type (ty: type) {ty'} (v: value ty'): option (value ty) := match type_dec ty ty' with
  | left e => Some (eq_rect _ value v _ (eq_sym e))
  | right _ => None
end.

Fixpoint eval_exp {ty} (e: exp ty) (s: stack): option (value ty) :=
  match e with
    | EConst c => Some (const_to_value c)
    | EVar b => match Dict.find (binder_id b) s with Some (existT _ ty' v) => try_cast_value_type (binder_ty b) v | None => None end
    | EUnop op e => match op, e with
      | Uop_not, e => option_map (fun v => vnot v) (eval_exp e s)
      | Uop_neg, e => option_map (fun v => vneg v) (eval_exp e s)
    end
    | EBAnd e1 e2 => match eval_exp e1 s, eval_exp e2 s with
      | Some (VBool false), _ => Some (VBool false)
      | Some (VBool true), Some v2 => Some v2
      | _, _ => None
    end
    | EBOr e1 e2 => match eval_exp e1 s, eval_exp e2 s with
      | Some (VBool false), Some v2 => Some v2
      | Some (VBool true), _ => Some (VBool true)
      | _, _ => None
    end
    | EBinop op e1 e2 => match op, e1, e2 with
      | Bop_xor, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vxor v1 v2)
        | _, _ => None
      end
      | Bop_plus, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vplus v1 v2)
        | _, _ => None
      end
      | Bop_minus, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vminus v1 v2)
        | _, _ => None
      end
      | Bop_mult, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vmult v1 v2)
        | _, _ => None
      end
      | Bop_div, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vdiv v1 v2)
        | _, _ => None
      end
      | Bop_eq, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (veq v1 v2)
        | _, _ => None
      end
      | Bop_neq, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vneq v1 v2)
        | _, _ => None
      end
      | Bop_le, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vle v1 v2)
        | _, _ => None
      end
      | Bop_lt, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vlt v1 v2)
        | _, _ => None
      end
      | Bop_ge, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vge v1 v2)
        | _, _ => None
      end
      | Bop_gt, e1, e2 => match (eval_exp e1 s), (eval_exp e2 s) with
        | Some v1, Some v2 => Some (vgt v1 v2)
        | _, _ => None
      end
    end
    | EIfte e1 e2 e3 => match eval_exp e1 s, eval_exp e2 s, eval_exp e3 s with
      | Some v1, Some v2, Some v3 => Some (vifte v1 v2 v3)
      | _, _, _ => None
    end
  end.


(** ** Lemmas *)

Lemma var_of_exp_aux_eq {ty} (e: exp ty) (l: list binder):
  var_of_exp_aux e l = var_of_exp e ++ l.
Proof.
  revert l.
  induction e as [ ty c | b | ty tout op e IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | ty1 ty2 tout op e1 IH1 e2 IH2 | ty e1 IH1 e2 IH2 e3 IH3 ]; intros l.
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
    rewrite IH1, IH2, IH1, IH2.
    rewrite app_nil_r, app_assoc.
    reflexivity.
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


Lemma sem_exp_without_useless_var (s: stack) b (e: exp (binder_ty b)) (v: value (binder_ty b)):
  sem_exp s e v -> (forall b', binder_id b' = binder_id b -> ~ In b' (var_of_exp e)) -> sem_exp (Dict.remove (binder_id b) s) e v.
Proof.
  intros Hexp Hnin.
  revert v Hexp.
  induction e as [ ty c | b' | ty tout op e IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | ty1 ty2 tout op e1 IH1 e2 IH2 | ty e1 IH1 e2 IH2 e3 IH3 ]; intros v Hexp.
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    apply SeConst.
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    clear H H1.
    remember (binder_id b) as i eqn:eqi; clear b eqi.
    unfold var_of_exp in Hnin.
    simpl in Hnin.
    refine (SeVar _ _ _ _).
    refine (Dict.maps_to_not_removed _ _ _ _ H2 _).
    intros f.
    exact (Hnin _ f (or_introl eq_refl)).
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e) in Hnin.
    specialize (IH Hnin _ H3).
    apply (SeUnop _ _ _ _ _ IH H6).
  - unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e2) in Hnin.
    rewrite var_of_exp_aux_eq in Hnin.
    inversion Hexp; subst.
    all: simpl_exist_type; subst.
    + apply SeBAndConstF.
      apply IH1.
      2: assumption.
      intros b' Hb.
      specialize (Hnin b' Hb).
      rewrite in_app_iff in Hnin.
      apply Decidable.not_or in Hnin.
      tauto.
    + apply SeBAndConstT.
      1: apply IH1.
      3: apply IH2.
      2, 4: assumption.
      all: intros b' Hb.
      all: specialize (Hnin b' Hb).
      all: rewrite in_app_iff in Hnin.
      all: apply Decidable.not_or in Hnin.
      all: tauto.
  - unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e2) in Hnin.
    rewrite var_of_exp_aux_eq in Hnin.
    inversion Hexp; subst.
    all: simpl_exist_type; subst.
    + apply SeBOrConstF.
      1: apply IH1.
      3: apply IH2.
      2, 4: assumption.
      all: intros b' Hb.
      all: specialize (Hnin b' Hb).
      all: rewrite in_app_iff in Hnin.
      all: apply Decidable.not_or in Hnin.
      all: tauto.
    + apply SeBOrConstT.
      apply IH1.
      2: assumption.
      intros b' Hb.
      specialize (Hnin b' Hb).
      rewrite in_app_iff in Hnin.
      apply Decidable.not_or in Hnin.
      tauto.
  - unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e2) in Hnin.
    rewrite var_of_exp_aux_eq in Hnin.
    inversion Hexp; subst.
    simpl_exist_type.
    subst.
    apply (SeBinop _ _ _ _ v1 v2).
    3: assumption.
    1: apply IH1.
    3: apply IH2.
    2, 4: assumption.
    all: intros b' Hb.
    all: specialize (Hnin b' Hb).
    all: rewrite in_app_iff in Hnin.
    all: apply Decidable.not_or in Hnin.
    all: tauto.
  - unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e3) in Hnin.
    rewrite 2!var_of_exp_aux_eq in Hnin.
    inversion Hexp; subst.
    simpl_exist_type.
    subst.
    constructor.
    1: apply IH1.
    3: apply IH2.
    5: apply IH3.
    2, 4, 6: assumption.
    all: intros b' Hb.
    all: specialize (Hnin b' Hb).
    all: rewrite 2!in_app_iff in Hnin.
    all: apply Decidable.not_or in Hnin.
    all: destruct Hnin as [Hn1 Hn2].
    all: apply Decidable.not_or in Hn2.
    all: tauto.
Qed.

Lemma sem_exp_with_useless_var (s: stack) (b: binder) (e: exp (binder_ty b)) (v: value (binder_ty b)):
  sem_exp s e v -> (forall b', binder_id b' = binder_id b -> ~ In b' (var_of_exp e)) ->
  forall {ty'} (v': value ty'), sem_exp (Dict.add (binder_id b) (existT _ _ v') s) e v.
Proof.
  intros Hexp Hnin.
  revert v Hexp.
  induction e as [ ty c | b' | ty tout op e IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | ty1 ty2 tout op e1 IH1 e2 IH2 | ty e1 IH1 e2 IH2 e3 IH3 ]; intros v Hexp tyv v'.
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    apply SeConst.
  - inversion Hexp.
    simpl_exist_type.
    subst.
    clear H H1.
    refine (SeVar _ _ _ _).
    refine (Dict.maps_to_add _ _ _ _ _ H2 _).
    intros f.
    refine (Hnin _ f (or_introl eq_refl)).
  - inversion Hexp.
    subst.
    simpl_exist_type.
    subst.
    unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e) in Hnin.
    specialize (IH Hnin _ H3).
    apply (SeUnop _ _ _ _ _ (IH tyv v') H6).
  - unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e2) in Hnin.
    rewrite var_of_exp_aux_eq in Hnin.
    inversion Hexp; subst.
    all: simpl_exist_type; subst.
    + apply SeBAndConstF.
      apply IH1.
      2: assumption.
      intros b' Hb.
      specialize (Hnin b' Hb).
      rewrite in_app_iff in Hnin.
      apply Decidable.not_or in Hnin.
      tauto.
    + apply SeBAndConstT.
      1: apply IH1.
      3: apply IH2.
      2, 4: assumption.
      all: intros b' Hb.
      all: specialize (Hnin b' Hb).
      all: rewrite in_app_iff in Hnin.
      all: apply Decidable.not_or in Hnin.
      all: tauto.
  - unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e2) in Hnin.
    rewrite var_of_exp_aux_eq in Hnin.
    inversion Hexp; subst.
    all: simpl_exist_type; subst.
    + apply SeBOrConstF.
      1: apply IH1.
      3: apply IH2.
      2, 4: assumption.
      all: intros b' Hb.
      all: specialize (Hnin b' Hb).
      all: rewrite in_app_iff in Hnin.
      all: apply Decidable.not_or in Hnin.
      all: tauto.
    + apply SeBOrConstT.
      apply IH1.
      2: assumption.
      intros b' Hb.
      specialize (Hnin b' Hb).
      rewrite in_app_iff in Hnin.
      apply Decidable.not_or in Hnin.
      tauto.
  - unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e2) in Hnin.
    rewrite var_of_exp_aux_eq in Hnin.
    inversion Hexp; subst.
    simpl_exist_type.
    subst.
    apply (SeBinop _ _ _ _ v1 v2).
    3: assumption.
    1: apply IH1.
    3: apply IH2.
    2, 4: assumption.
    all: intros b' Hb.
    all: specialize (Hnin b' Hb).
    all: rewrite in_app_iff in Hnin.
    all: apply Decidable.not_or in Hnin.
    all: tauto.
  - unfold var_of_exp in Hnin.
    simpl in Hnin.
    fold (var_of_exp e3) in Hnin.
    rewrite 2!var_of_exp_aux_eq in Hnin.
    inversion Hexp; subst.
    simpl_exist_type.
    subst.
    constructor.
    1: apply IH1.
    3: apply IH2.
    5: apply IH3.
    2, 4, 6: assumption.
    all: intros b' Hb.
    all: specialize (Hnin b' Hb).
    all: rewrite 2!in_app_iff in Hnin.
    all: apply Decidable.not_or in Hnin.
    all: destruct Hnin as [Hn1 Hn2].
    all: apply Decidable.not_or in Hn2.
    all: tauto.
Qed.
