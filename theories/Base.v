#[export] Set Default Goal Selector "!".

From Stdlib Require Export List Nat String.
From Stdlib Require Export Lia.

Export ListNotations.
Open Scope nat_scope.

Lemma sig2T_eq :
  forall {A : Type}, (forall x y : A, {x = y} + {x <> y}) ->
  forall {P : A -> Type} {u x y}, existT P u x = existT P u y -> x = y.
Proof using.
  intros A HA P u x y Hxy.
  specialize (projT2_eq Hxy : eq_rect u P x u (projT1_eq Hxy) = y) as tmp.
  rewrite (Eqdep_dec.UIP_dec HA (projT1_eq Hxy) eq_refl) in tmp.
  exact tmp.
Qed.

Definition prod_dec {A B : Type} : (forall x y : A, {x = y} + {x <> y}) -> (forall x y : B, {x = y} + {x <> y}) ->
  (forall x y : A * B, {x = y} + {x <> y}) := fun decA decB '(xa, xb) '(ya, yb) =>
  match decA xa ya with
  | right n => right (fun (f : (_, _) = (_, _)) => n (f_equal fst f))
  | left ea =>
    match decB xb yb with
    | right n => right (fun (f : (_, _) = (_, _)) => n (f_equal snd f))
    | left eb => left (f_equal2 pair ea eb)
    end
  end.

Definition sigT_dec {A : Type} {B : A -> Type} : (forall x y : A, {x = y} + {x <> y}) -> (forall a (x y : B a), {x = y} + {x <> y}) ->
  (forall x y : sigT B, {x = y} + {x <> y}) := fun decA decB '(existT _ xa xb) '(existT _ ya yb) =>
  match decA xa ya with
  | right n => right (fun f => n (EqdepFacts.eq_sigT_fst f))
  | left ea =>
    match decB _ (eq_rect _ B xb _ ea) yb with
    | right n => right (fun f => n (eq_ind _ (fun v => eq_rect _ _ _ _ v = _) (EqdepFacts.eq_sigT_snd f) _ (Eqdep_dec.UIP_dec decA _ _)))
    | left eb => left (eq_existT_curried ea eb)
    end
  end.

Axiom ProofIrrelevance: forall (P: Prop) (p q: P), p = q.

Lemma sig2T_eq_PI :
  forall {A : Type} {P : A -> Type} {u x y}, existT P u x = existT P u y -> x = y.
Proof using.
  intros A P u x y Hxy.
  specialize (projT2_eq Hxy : eq_rect u P x u (projT1_eq Hxy) = y) as tmp.
  rewrite (ProofIrrelevance _ (projT1_eq Hxy) eq_refl) in tmp.
  exact tmp.
Qed.

Definition ident := nat.
