From Reactive Require Import Base.

From Reactive.Datatypes Require Result.
From Reactive.Languages Require LustreAst Lustre.

From Stdlib Require ListDec.
From Stdlib Require Import Bool Sorting Permutation.

Module Source := LustreAst.
Module Target := Lustre.

Definition convert_type (t : Source.type) : Target.type := match t with
  | Source.TVoid => Target.TVoid
  | Source.TBool => Target.TBool
  | Source.TInt => Target.TInt
end.

Record common_temp : Set := {
  orig :> Source.node;
  env: Dict.t Target.type;
  Henv: forall x t, Dict.maps_to x (convert_type t) env <-> In (x, t) (orig.(Source.n_in) ++ orig.(Source.n_out) ++ orig.(Source.n_locals));
  
  n_in: list Target.binder;
  n_out: list Target.binder;
  n_locals: list Target.binder;
  
  nvars := n_in ++ n_out ++ n_locals;
  Hnvars: nvars = map (fun '(x, t) => (x, convert_type t)) (orig.(Source.n_in) ++ orig.(Source.n_out) ++ orig.(Source.n_locals));
}.

Open Scope string_scope.

Fixpoint check_exp (temp: common_temp) (e: Source.exp): Result.t (sigT Target.exp).
Proof.
  destruct e as [ c | n | n | op e | op e1 e2 | e1 e2 e3 ].
  - left.
    destruct c as [ | b | n ].
    + exists Target.TVoid.
      exact (Target.EConst Target.CVoid).
    + exists Target.TBool.
      exact (Target.EConst (Target.CBool b)).
    + exists Target.TInt.
      exact (Target.EConst (Target.CInt n)).
  - destruct (Dict.find n (env temp)) as [ ty | ].
    2: right; exact "An input variable is not declared".
    left.
    exists ty.
    exact (Target.EInput (n, ty)).
  - destruct (Dict.find n (env temp)) as [ ty | ].
    2: right; exact "A variable is not declared".
    left.
    exists ty.
    exact (Target.EVar (n, ty)).
  - refine (Result.bind (check_exp temp e) _).
    intros e'.
    exact (match op, e' with
      | Source.Uop_neg, existT _ Target.TInt e => Result.Ok (existT _ _ (Target.EUnop Target.Uop_neg e))
      | Source.Uop_not, existT _ Target.TInt e => Result.Ok (existT _ _ (Target.EUnop Target.Uop_not e))
      | Source.Uop_pre, existT _ Target.TInt e => Result.Ok (existT _ _ (Target.EUnop Target.Uop_pre e))
      | _, _ => Result.Err "Untypeable expression"
    end).
  - refine (Result.bind (check_exp temp e1) _).
    intros e1'.
    refine (Result.bind (check_exp temp e2) _).
    intros e2'.
    exact (match op, e1', e2' with
      | Source.Bop_and, existT _ Target.TBool e1, existT _ Target.TBool e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_and e1 e2))
      | Source.Bop_or, existT _ Target.TBool e1, existT _ Target.TBool e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_or e1 e2))
      | Source.Bop_xor, existT _ Target.TBool e1, existT _ Target.TBool e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_xor e1 e2))
      | Source.Bop_plus, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_plus e1 e2))
      | Source.Bop_minus, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_minus e1 e2))
      | Source.Bop_mult, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_mult e1 e2))
      | Source.Bop_div, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_div e1 e2))
      | Source.Bop_eq, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_eq e1 e2))
      | Source.Bop_neq, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_neq e1 e2))
      | Source.Bop_le, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_le e1 e2))
      | Source.Bop_lt, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_lt e1 e2))
      | Source.Bop_ge, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_ge e1 e2))
      | Source.Bop_gt, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_gt e1 e2))
      | Source.Bop_arrow, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_arrow e1 e2))
      | Source.Bop_fby, existT _ Target.TInt e1, existT _ Target.TInt e2 => Result.Ok (existT _ _ (Target.EBinop Target.Bop_arrow e1 (Target.EUnop Target.Uop_pre e2)))
      | _, _, _ => Result.Err "Untypeable expression"
    end).
  - refine (Result.bind (check_exp temp e1) _).
    intros e1'.
    refine (Result.bind (check_exp temp e2) _).
    intros e2'.
    refine (Result.bind (check_exp temp e3) _).
    intros e3'.
    exact (match e1', e2', e3' with
      | existT _ Target.TBool e1, existT _ t2 e2, existT _ t3 e3 =>
          match Target.type_dec t2 t3 with
          | left e => Result.Ok (existT _ _ (Target.EIfte e1 (eq_rect _ _ e2 _ e) e3))
          | right _ => Result.Err "Untypeable expression"
          end
      | _, _, _ => Result.Err "Untypeable expression"
    end).
Defined.

Definition check_body (temp: common_temp) (entry: Source.node): Result.t
  { body : list Target.equation | incl (map Target.equation_dest body) (nvars temp) }.
Proof.
  destruct entry.
  induction n_body as [ | [ n e ] tl IH ].
  - left.
    exists [].
    exact (incl_nil_l _).
  - refine (Result.bind (check_exp temp e) _).
    intros [ ty e' ].
    destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Target.type_dec) (n, ty) (nvars temp)) as [Hin|_].
    2: destruct (In_dec PeanoNat.Nat.eq_dec n (map fst (nvars temp))) as [Hin|_].
    2:  exact (Result.Err "A variable is assigned to an expression of an incompatible type").
    2: exact (Result.Err "A variable is assigned to but not declared").
    refine (Result.bind IH _); clear IH.
    intros [ eqs IH ].
    left.
    exists ((n, existT Target.exp ty e') :: eqs).
    intros a [<-|H]; [exact Hin|exact (IH _ H)].
Defined.

Definition n_assigned_vars (body: list Target.equation) :=
  map Target.equation_dest body.

Scheme Equality for list.

Module EquationOrder <: Orders.TotalLeBool.
  Local Coercion is_true : bool >-> Sortclass.

  Definition t := Source.equation.

  Definition leb (x y: Source.equation): bool := Nat.leb (fst x) (fst y).
  Infix "<=?" := leb (at level 70, no associativity).

  Theorem leb_total: forall x y, x <=? y \/ y <=? x.
  Proof.
    intros [] [].
    unfold leb; simpl.

    revert i i0.
    induction i; destruct i0; simpl; auto.
  Qed.
End EquationOrder.

Module Import EquationSort := Sort EquationOrder.

Definition list_eq_dec_binder :=
  list_eq_dec _ Source.binder_eqb Source.binder_eqb_to_eq Source.binder_eq_to_eqb.

Definition list_eq_dec_equation :=
  list_eq_dec _ Source.equation_eqb Source.equation_eqb_to_eq Source.equation_eq_to_eqb.

Definition check_assigned_out (temp: common_temp) body: Result.t (incl (n_out temp) (n_assigned_vars body)).
Proof.
  exact (match incl_dec (prod_dec PeanoNat.Nat.eq_dec Target.type_dec) _ _ with
    | left h => Result.Ok h
    | right h => Result.Err "The output variable is never assigned"
  end).
Defined.

Definition n_out_is_not_an_input (temp: common_temp) :
  Result.t (Forall (fun b => ~ In (fst b) (map fst (n_in temp))) (n_out temp)) :=
  match Forall_dec _ (fun b => dec_not (In_dec PeanoNat.Nat.eq_dec (fst b) _)) _ with
  | right h => Result.Err "The output variable is also an input"
  | left h => Result.Ok h
  end.


Definition n_inputs_equations (temp: common_temp) body:
  Result.t (incl (List.map (fun '((n, ty) as b) => (n, existT Target.exp ty (Target.EInput b))) (n_in temp)) body).
Proof.
  refine (match incl_dec _ _ _ with
    | left h => Result.Ok h
    | right h => Result.Err "The output variable is never assigned"
  end).
  intros [n1 [ty1 e1]] [n2 [ty2 e2]].
  destruct (PeanoNat.Nat.eq_dec n1 n2) as [ <- | n ]; [ | right; injection as e _; contradiction (n e) ].
  destruct (Target.type_dec ty1 ty2) as [ <- | n ]; [ | right; injection as _ e; contradiction (n (projT1_eq e)) ].
  destruct (Target.exp_dec e1 e2) as [ <- | n ]; [ left; reflexivity | ].
  right; intros [=f]; exact (n (Target.sig2T_eq_type f)).
Defined.


Definition n_no_einputs_in_other (temp: common_temp) (body: list Target.equation):
  Result.t (Forall (fun '(name, existT _ _ exp) => ~ In name (map fst (n_in temp)) -> Target.has_einput exp = false) body).
Proof.
  refine (match Forall_dec _ _ _ with
    | left h => Result.Ok h
    | right _ => Result.Err "A variable not present in inputs has an EInput subexpression"
  end).
  intros [n [ty e]].
  refine (match ListDec.In_dec PeanoNat.Nat.eq_dec _ _ with left h => left (fun f => False_ind _ (f h)) | right h => _ end).
  destruct (Target.has_einput e); [ right | left; reflexivity ].
  intros f.
  apply f in h.
  discriminate h.
Defined.

Lemma forall_type_dec : forall (P : Source.type -> Prop), (forall ty, {P ty} + {~P ty}) -> {forall ty, P ty} + {exists ty, ~ P ty}.
Proof using.
  intros P dec.
  destruct (dec Source.TVoid) as [Pvoid | nP]; [|right; exact (ex_intro (fun ty => ~ P ty) _ nP)].
  destruct (dec Source.TBool) as [Pbool | nP]; [|right; exact (ex_intro (fun ty => ~ P ty) _ nP)].
  destruct (dec Source.TInt)  as [Pint  | nP]; [|right; exact (ex_intro (fun ty => ~ P ty) _ nP)].
  left; intros []; assumption.
Defined.

Import Result.notations.

Lemma check_Henv {entry} :
  let n_in := map (fun '(n, t) => (n, convert_type t)) (Source.n_in entry) in
  let n_out := map (fun '(n, t) => (n, convert_type t)) (Source.n_out entry) in
  let n_locals := map (fun '(n, t) => (n, convert_type t)) (Source.n_locals entry) in
  Result.t (forall n t,
    Dict.maps_to n (convert_type t)
      (fold_left (fun acc '(n, t) => Dict.add n t acc)
      (n_in ++ n_out ++ n_locals)
      (Dict.empty Target.type)) <->
    In (n, t) (Source.n_in entry ++ Source.n_out entry ++ Source.n_locals entry)).
Proof using.
  destruct entry as [? nin nout nloc ?]; cbn; clear.
  destruct (Forall_Exists_dec (* Technically, does not check for duplicates, only variables with same ID but different types *)
    (fun v => forall ty', In (fst v, ty') nin -> ty' = snd v)
    (fun v =>
      match forall_type_dec
        (fun ty' => In (fst v, ty') nin -> ty' = snd v)
        ltac:(
          intros ty;
          destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Source.type_dec) (fst v, ty) nin) as [Hin|Hnin]; [|left; intros f; contradiction (Hnin f)];
          destruct (Source.type_dec ty (snd v)) as [eqty|nety]; [left; intros _; exact eqty|];
          right; intros f; exact (nety (f Hin)))
      with
      | left H => left H
      | right H => right (fun f => match H with ex_intro _ ty Hty => Hty (f ty) end)
      end)
    nin) as [innotdup'|_].
  2: right; exact "An input variable is present multiple times in the input list".
  destruct (Forall_Exists_dec (fun v => ~ In (fst v) (map fst nout))
    (fun v => dec_not (In_dec PeanoNat.Nat.eq_dec (fst v) (map fst nout))) nin) as [innotout'|_].
  2: right; exact "An input variable is also an output variable".
  destruct (Forall_Exists_dec (fun v => ~ In (fst v) (map fst nloc))
    (fun v => dec_not (In_dec PeanoNat.Nat.eq_dec (fst v) (map fst nloc))) nin) as [innotloc'|_].
  2: right; exact "An input variable is also a local variable".
  destruct (Forall_Exists_dec (* Technically, does not check for duplicates, only variables with same ID but different types *)
    (fun v => forall ty', In (fst v, ty') nout -> ty' = snd v)
    (fun v =>
      match forall_type_dec
        (fun ty' => In (fst v, ty') nout -> ty' = snd v)
        ltac:(
          intros ty;
          destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Source.type_dec) (fst v, ty) nout) as [Hin|Hnin]; [|left; intros f; contradiction (Hnin f)];
          destruct (Source.type_dec ty (snd v)) as [eqty|nety]; [left; intros _; exact eqty|];
          right; intros f; exact (nety (f Hin)))
      with
      | left H => left H
      | right H => right (fun f => match H with ex_intro _ ty Hty => Hty (f ty) end)
      end)
    nout) as [outnotdup'|_].
  2: right; exact "An output variable is present multiple times in the output list".
  destruct (Forall_Exists_dec (fun v => ~ In (fst v) (map fst nloc))
    (fun v => dec_not (In_dec PeanoNat.Nat.eq_dec (fst v) (map fst nloc))) nout) as [outnotloc'|_].
  2: right; exact "An output variable is also a local variable".
  destruct (Forall_Exists_dec (* Technically, does not check for duplicates, only variables with same ID but different types *)
    (fun vloc => forall ty', In (fst vloc, ty') nloc -> ty' = snd vloc)
    (fun vloc =>
      match forall_type_dec
        (fun ty' => In (fst vloc, ty') nloc -> ty' = snd vloc)
        ltac:(
          intros ty;
          destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Source.type_dec) (fst vloc, ty) nloc) as [Hin|Hnin]; [|left; intros f; contradiction (Hnin f)];
          destruct (Source.type_dec ty (snd vloc)) as [eqty|nety]; [left; intros _; exact eqty|];
          right; intros f; exact (nety (f Hin)))
      with
      | left H => left H
      | right H => right (fun f => match H with ex_intro _ ty Hty => Hty (f ty) end)
      end)
    nloc) as [locnotdup'|_].
  2: right; exact "A local variable is present multiple times in the locals list".
  left; intros n t.
  match goal with |- Dict.maps_to _ _ (fold_left ?f ?l ?d) <-> _ =>
  rewrite <-(fold_left_rev_right (fun x y => f y x) l d) end.
  rewrite (in_rev (nin ++ nout ++ nloc) (n, t)),
          !rev_app_distr, <-!app_assoc, <-!map_rev.
  apply Forall_rev in innotdup', innotloc', innotout', outnotloc', outnotdup', locnotdup'.
  specialize (Forall_impl _ (fun v HP ty' Hin => HP ty' (proj2 (in_rev _ _) Hin)) innotdup') as innotdup.
  specialize (Forall_impl _ (fun v Hnin Hin => Hnin (proj2 (in_rev _ _) (eq_ind _ _ Hin _ (map_rev _ _)))) innotout') as innotout.
  specialize (Forall_impl _ (fun v Hnin Hin => Hnin (proj2 (in_rev _ _) (eq_ind _ _ Hin _ (map_rev _ _)))) innotloc') as innotloc.
  specialize (Forall_impl _ (fun v HP ty' Hin => HP ty' (proj2 (in_rev _ _) Hin)) outnotdup') as outnotdup.
  specialize (Forall_impl _ (fun v Hnin Hin => Hnin (proj2 (in_rev _ _) (eq_ind _ _ Hin _ (map_rev _ _)))) outnotloc') as outnotloc.
  specialize (Forall_impl _ (fun v HP ty' Hin => HP ty' (proj2 (in_rev _ _) Hin)) locnotdup') as locnotdup.
  remember (rev nin) as l3 eqn:eq3.
  remember (rev nout) as l2 eqn:eq2.
  remember (rev nloc) as l1 eqn:eq1.
  clear nin nout nloc eq1 eq2 eq3 innotdup' innotout' innotloc' outnotdup' outnotloc' locnotdup'.
  split.
  - intros H.
    clear innotout innotloc outnotloc.
    induction l1 as [|(v, t') l1 IH]; swap 1 2.
    1: destruct (PeanoNat.Nat.eq_dec n v) as [<-|Hne]; [left; f_equal; cbn in H; clear - H|].
    1:  unfold Dict.maps_to in H; rewrite Dict.maps_to_last_added in H.
    1:  injection H as H.
    1:  destruct t, t'; try exact eq_refl; discriminate H.
    1: right; cbn in *; apply Forall_inv in locnotdup as H2.
    1: apply Forall_inv_tail in locnotdup.
    1: refine (IH (Forall_impl _ _ locnotdup) _).
    1:  intros [b tb] Hb ty Hin; exact (Hb ty (or_intror Hin)).
    1: exact (Dict.maps_to_not_last_added _ _ _ _ _ H Hne).
    clear locnotdup.
    induction l2 as [|(v, t') l1 IH]; swap 1 2.
    1: destruct (PeanoNat.Nat.eq_dec n v) as [<-|Hne]; [left; f_equal; cbn in H; clear - H|].
    1:  unfold Dict.maps_to in H; rewrite Dict.maps_to_last_added in H.
    1:  injection H as H.
    1:  destruct t, t'; try exact eq_refl; discriminate H.
    1: right; cbn in *; apply Forall_inv in outnotdup as H2.
    1: apply Forall_inv_tail in outnotdup.
    1: refine (IH (Forall_impl _ _ outnotdup) _).
    1:  intros [b tb] Hb ty Hin; exact (Hb ty (or_intror Hin)).
    1: exact (Dict.maps_to_not_last_added _ _ _ _ _ H Hne).
    clear outnotdup.
    induction l3 as [|(v, t') l1 IH]; swap 1 2.
    1: destruct (PeanoNat.Nat.eq_dec n v) as [<-|Hne]; [left; f_equal; cbn in H; clear - H|].
    1:  unfold Dict.maps_to in H; rewrite Dict.maps_to_last_added in H.
    1:  injection H as H.
    1:  destruct t, t'; try exact eq_refl; discriminate H.
    1: right; cbn in *; apply Forall_inv in innotdup as H2.
    1: apply Forall_inv_tail in innotdup.
    1: refine (IH (Forall_impl _ _ innotdup) _).
    1:  intros [b tb] Hb ty Hin; exact (Hb ty (or_intror Hin)).
    1: exact (Dict.maps_to_not_last_added _ _ _ _ _ H Hne).
    unfold Dict.maps_to, Dict.find, map, app, fold_right in H.
    rewrite (proj2 (Dict.no_element_is_empty _) eq_refl) in H.
    discriminate H.
  - rewrite !in_app_iff.
    intros [H|[H|H]].
    1: rename locnotdup into Hnotdup, l1 into l; clear innotdup outnotdup.
    2: specialize (proj1 (Forall_forall _ _) outnotloc _ H : ~ In n _) as notinl1.
    2: rename outnotdup into Hnotdup, l2 into l; clear innotdup locnotdup.
    3: specialize (proj1 (Forall_forall _ _) innotout _ H : ~ In n _) as notinl2.
    3: specialize (proj1 (Forall_forall _ _) innotloc _ H : ~ In n _) as notinl1.
    3: rename innotdup into Hnotdup, l3 into l; clear outnotdup locnotdup.
    1-3: clear innotout innotloc outnotloc.
    2-3: induction l1 as [|[n1 t1] l1 IH].
    2,4: clear notinl1; cbn.
    4-5: cbn; refine (Dict.maps_to_add _ _ _ _ _ (IH (fun f => notinl1 (or_intror f))) (fun f => notinl1 (or_introl (eq_sym f)))).
    3: induction l2 as [|[n2 t2] l2 IH].
    3: clear notinl2; cbn.
    4: cbn; refine (Dict.maps_to_add _ _ _ _ _ (IH (fun f => notinl2 (or_intror f))) (fun f => notinl2 (or_introl (eq_sym f)))).
    1-3: induction l as [|[nl tl] l IH]; [contradiction H|].
    1-3: destruct H as [[=<- <-]|H]; [exact (Dict.maps_to_last_added _ _ _)|].
    1-3: destruct (PeanoNat.Nat.eq_dec n nl) as [<-|Hne]; [clear IH|].
    1,3,5: rewrite (proj1 (Forall_forall _ _) Hnotdup _ (or_intror H) _ (or_introl eq_refl)); exact (Dict.maps_to_last_added _ _ _).
    1-3: refine (Dict.maps_to_add _ _ _ _ _ (IH _ H) Hne).
    1-3: refine (Forall_impl _ _ (Forall_inv_tail Hnotdup)).
    1-3: clear; intros x H t Hin; exact (H _ (or_intror Hin)).
Defined.

Definition check_node_prop (entry: Source.node): Result.t Target.node :=
  let n_in := map (fun '(n, t) => (n, convert_type t)) (Source.n_in entry) in
  let n_out := map (fun '(n, t) => (n, convert_type t)) (Source.n_out entry) in
  let n_locals := map (fun '(n, t) => (n, convert_type t)) (Source.n_locals entry) in
  do Henv <- check_Henv;
  let temp := {|
    orig := entry;
    env := fold_left (fun acc '(n, t) => Dict.add n t acc) (n_in ++ n_out ++ n_locals) (Dict.empty _);
    Henv := Henv;
    
    n_in := n_in;
    n_out := n_out;
    n_locals := n_locals;
    
    Hnvars := eq_sym (eq_trans (map_app _ _ _) (f_equal _ (map_app _ _ _)));
  |} in
  do '(exist _ n_body assigned_vars_are_vars) <- check_body temp entry;
  do check_assigned <- check_assigned_out temp n_body;
  do n_out_is_not_an_input <- n_out_is_not_an_input temp;
  do n_inputs_equations <- n_inputs_equations temp n_body;
  do n_no_einputs_in_other <- n_no_einputs_in_other temp n_body;
  Result.Ok {|
      Target.n_name := Source.n_name entry;
      Target.n_in := n_in;
      Target.n_out := n_out;
      Target.n_locals := n_locals;
      Target.n_body := n_body;
      Target.n_assigned_vars_are_vars := assigned_vars_are_vars;
      Target.n_assigned_out := check_assigned;
      Target.n_out_is_not_an_input := n_out_is_not_an_input;
      Target.n_inputs_equations := n_inputs_equations;
      Target.n_no_einputs_in_other := n_no_einputs_in_other
    |}.
