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

Definition translate_unop (op: Source.unop): { tin & { tout & Target.unop tin tout } } := match op with
  | Source.Uop_neg => existT _ _ (existT _ _ Target.Uop_neg)
  | Source.Uop_not => existT _ _ (existT _ _ Target.Uop_not)
  | Source.Uop_pre => existT _ _ (existT _ _ Target.Uop_pre)
end.
Definition translate_binop (op: Source.binop): { tin1 & { tin2 & { tout & Target.binop tin1 tin2 tout } } } := match op with
  | Source.Bop_and => existT _ _ (existT _ _ (existT _ _ Target.Bop_and))
  | Source.Bop_or => existT _ _ (existT _ _ (existT _ _ Target.Bop_or))
  | Source.Bop_xor => existT _ _ (existT _ _ (existT _ _ Target.Bop_xor))
  | Source.Bop_plus => existT _ _ (existT _ _ (existT _ _ Target.Bop_plus))
  | Source.Bop_minus => existT _ _ (existT _ _ (existT _ _ Target.Bop_minus))
  | Source.Bop_mult => existT _ _ (existT _ _ (existT _ _ Target.Bop_mult))
  | Source.Bop_div => existT _ _ (existT _ _ (existT _ _ Target.Bop_div))
  | Source.Bop_eq => existT _ _ (existT _ _ (existT _ _ Target.Bop_eq))
  | Source.Bop_neq => existT _ _ (existT _ _ (existT _ _ Target.Bop_neq))
  | Source.Bop_le => existT _ _ (existT _ _ (existT _ _ Target.Bop_le))
  | Source.Bop_lt => existT _ _ (existT _ _ (existT _ _ Target.Bop_lt))
  | Source.Bop_ge => existT _ _ (existT _ _ (existT _ _ Target.Bop_ge))
  | Source.Bop_gt => existT _ _ (existT _ _ (existT _ _ Target.Bop_gt))
  | Source.Bop_arrow => existT _ _ (existT _ _ (existT _ _ Target.Bop_arrow))
  | Source.Bop_fby => existT _ _ (existT _ _ (existT _ _ Target.Bop_arrow))
end.
Definition typecheck_exp {P : forall ty, Target.exp ty -> Prop} (loc: Result.location) (e: { ty & sig (P ty) }) (t: Target.type):
    Result.t Target.type (sig (P t)) := match e, t with
  | existT _ Target.TVoid (exist _ e H), Target.TVoid => Result.Ok (exist _ e H)
  | existT _ Target.TBool (exist _ e H), Target.TBool => Result.Ok (exist _ e H)
  | existT _ Target.TInt (exist _ e H), Target.TInt => Result.Ok (exist _ e H)
  | existT _ ety (exist _ _ H), _ => Result.Err [(loc, Result.BadType [t] ety)]
end.

Fixpoint check_exp (temp: common_temp) (e: Source.exp): Result.t Target.type
  { ty & { exp : Target.exp ty | incl (Target.var_of_exp exp) (nvars temp) } }.
Proof.
  destruct e as [ l c | l n | l op e | l op e1 e2 | l e1 e2 e3 ].
  - left.
    destruct c as [ | b | n ].
    + exists Target.TVoid, (Target.EConst Target.CVoid); intros ? [].
    + exists Target.TBool, (Target.EConst (Target.CBool b)); intros ? [].
    + exists Target.TInt, (Target.EConst (Target.CInt n)); intros ? [].
  - destruct (Dict.find n (env temp)) as [ ty | ] eqn:eqn.
    2: right; exact [(l, Result.UndeclaredVariable n)].
    left.
    exists ty, (Target.EVar (n, ty)).
    intros ? [<-|[]]; cbn.
    assert (TODO_removeme : exists ty0, ty = convert_type ty0)
      by (destruct ty; [exists Source.TVoid|exists Source.TBool|exists Source.TInt]; exact eq_refl);
      destruct TODO_removeme as [ty0 ->].
    rewrite (Hnvars temp).
    apply (in_map (fun '(x, t) => (x, convert_type t)) _ (n, ty0)).
    exact (proj1 (Henv temp n ty0) eqn).
  - refine (Result.bind (check_exp temp e) _).
    intros e'.
    destruct (translate_unop op) as [ tin [ tout top ]].
    refine (Result.bind (typecheck_exp l e' tin) _).
    intros [ e'' He ].
    refine (Result.Ok _); exists tout, (Target.EUnop top e'').
    exact He.
  - refine (Result.bind (check_exp temp e1) _).
    intros e1'.
    refine (Result.bind (check_exp temp e2) _).
    intros e2'.
    destruct (translate_binop op) as [ tin1 [ tin2 [ tout top ]]].
    refine (Result.bind (typecheck_exp l e1' tin1) _).
    intros [ e1'' He1 ].
    refine (Result.bind (typecheck_exp l e2' tin2) _).
    intros [ e2'' He2 ].
    refine (Result.Ok _); exists tout, (Target.EBinop top e1'' e2'').
    cbn; rewrite Target.var_of_exp_aux_eq.
    apply incl_app; assumption.
  - refine (Result.bind (check_exp temp e1) _).
    intros e1'.
    refine (Result.bind (typecheck_exp l e1' Target.TBool) _).
    intros [ e1'' He1 ].
    refine (Result.bind (check_exp temp e2) _).
    intros e2'.
    refine (Result.bind (check_exp temp e3) _).
    intros e3'.
    destruct e2' as [t [e2'' He2]].
    refine (Result.bind (typecheck_exp l e3' t) _).
    intros [ e3'' He3 ].
    refine (Result.Ok _); exists t, (Target.EIfte e1'' e2'' e3'').
    cbn; rewrite !Target.var_of_exp_aux_eq, app_nil_r.
    repeat apply incl_app; assumption.
Defined.

Definition check_body (temp: common_temp) (entry: Source.node): Result.t Target.type
  { body : list Target.equation
  | Permutation (map Target.equation_dest body) (n_out temp ++ n_locals temp) /\
    Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in temp ++ n_out temp ++ n_locals temp)) body }.
Proof.
  destruct entry as [nloc n nin out loc eqs]; clear n nin out loc.
  refine (Result.bind _
    (fun res : { rem & { body | Permutation (rem ++ map Target.equation_dest body) (n_out temp ++ n_locals temp) /\
                                Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in temp ++ n_out temp ++ n_locals temp)) body } } =>
      match res with existT _ [] ret => Result.Ok ret | existT _ ((i, ty) :: _) _ => Result.Err [(nloc, Result.NeverAssigned i ty)] end)).
  induction eqs as [ | [ l [ n e ] ] tl IH ].
  - refine (Result.Ok (existT _ (n_out temp ++ n_locals temp) (exist _ [] _))); split.
    1: rewrite app_nil_r; exact (Permutation_refl _).
    exact (Forall_nil _).
  - refine (Result.bind (Result.combine (check_exp temp e) IH) _); clear IH.
    intros [ [ ty [ e' He ] ] [ rem [ eqs [ IH1 IH2 ] ] ] ].
    pose (rev_lhs := @nil (ident * Target.type)); change rem with (rev_lhs ++ rem) in IH1.
    generalize dependent rev_lhs; induction rem as [ | [ i ty' ] rem IH ]; intros rev_lhs Hperm.
    1: refine (Result.Err [(l, _)]); destruct temp as [? ? ? nin ? ? ?]; clear - n nin.
    1: induction nin as [|[hdn hdt] tl IH].
    1:  exact (Result.UndeclaredVariable n).
    1: destruct (PeanoNat.Nat.eq_dec n hdn) as [_|_].
    1:  exact (Result.AssignToInput n hdt).
    1: exact IH.
    destruct (PeanoNat.Nat.eq_dec n i) as [ <- | nnei ].
    2: refine (IH ((i, ty') :: rev_lhs) (Permutation_trans (Permutation_app_tail _ _) Hperm)).
    2: rewrite (app_assoc _ [_] _ : _ ++ (i, ty') :: _ = _).
    2: exact (Permutation_app_tail _ (Permutation_cons_append _ _)).
    destruct (Target.type_dec ty ty') as [ <- | nety ].
    2: exact (Result.Err [(l, Result.IncompatibleTypeAssignment n ty' ty)]).
    refine (Result.Ok (existT _ (rev_append rev_lhs rem) (exist _ ((n, existT Target.exp ty e') :: eqs) _))).
    split; [|refine (Forall_cons _ _ IH2); exact He].
    rewrite (app_assoc _ [_] _ : _ ++ map Target.equation_dest ((_, _) :: _) = (_ ++ _) ++ map _ _), rev_append_rev.
    refine (Permutation_trans (Permutation_app_tail _ _) Hperm); unfold Target.equation_dest, fst, snd, projT1.
    rewrite <-app_assoc; exact (Permutation_sym (Permutation_app (Permutation_rev _) (Permutation_cons_append _ _))).
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

Definition check_assigned_out (l: Result.location) (temp: common_temp) body: Result.t Target.type (incl (n_out temp) (n_assigned_vars body)).
Proof.
  refine (Result.bind (Result.list_map _ _) (fun H => Result.Ok (proj2 (incl_Forall_in_iff _ _) H))).
  intros b.
  destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Target.type_dec) b (n_assigned_vars body)) as [Hin|Hnin].
  1: exact (Result.Ok Hin).
  exact (Result.Err [(l, Result.NeverAssigned (fst b) (snd b))]).
Defined.

(* TODO: merge with check_Henv *)
Definition vars_unique (l: Result.location) (temp: common_temp) :
  Result.t Target.type (NoDup ((map fst (n_in temp ++ n_out temp ++ n_locals temp)))).
Proof using.
  induction (n_in temp) as [ | hd tl IH ].
  2:{
    refine (Result.bind (Result.combine_prop _ IH) (fun '(conj H1 H2) => Result.Ok (NoDup_cons _ H1 H2))); clear IH.
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst tl)) as [ _ | nin ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration (fst hd) Result.DeclInput Result.DeclInput)]).
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst (n_out temp))) as [ _ | nout ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration (fst hd) Result.DeclInput Result.DeclOutput)]).
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst (n_locals temp))) as [ _ | nloc ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration (fst hd) Result.DeclInput Result.DeclLocal)]).
    refine (Result.Ok _).
    rewrite !map_app, !in_app_iff; tauto.
  }
  induction (n_out temp) as [ | hd tl IH ].
  2:{
    refine (Result.bind (Result.combine_prop _ IH) (fun '(conj H1 H2) => Result.Ok (NoDup_cons _ H1 H2))); clear IH.
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst tl)) as [ _ | nin ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration (fst hd) Result.DeclOutput Result.DeclOutput)]).
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst (n_locals temp))) as [ _ | nloc ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration (fst hd) Result.DeclOutput Result.DeclLocal)]).
    refine (Result.Ok _).
    rewrite !map_app, !in_app_iff; tauto.
  }
  induction (n_locals temp) as [ | hd tl IH ].
  2:{
    refine (Result.bind (Result.combine_prop _ IH) (fun '(conj H1 H2) => Result.Ok (NoDup_cons _ H1 H2))); clear IH.
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst tl)) as [ _ | nin ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration (fst hd) Result.DeclLocal Result.DeclLocal)]).
    refine (Result.Ok _).
    rewrite !map_app, !in_app_iff; tauto.
  }
  exact (Result.Ok (NoDup_nil _)).
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
  Result.t Target.type (forall n t,
    Dict.maps_to n (convert_type t)
      (fold_left (fun acc '(n, t) => Dict.add n t acc)
      (n_in ++ n_out ++ n_locals)
      (Dict.empty Target.type)) <->
    In (n, t) (Source.n_in entry ++ Source.n_out entry ++ Source.n_locals entry)).
Proof using.
  destruct entry as [l ? nin nout nloc ?]; cbn; clear - l.
  refine (Result.bind
    (Result.combine_prop (Result.list_map (P := fun v => forall ty', In (fst v, ty') nin -> ty' = snd v) _ nin)
    (Result.combine_prop (Result.list_map (P := fun v => ~ In (fst v) (map fst nout)) _ nin)
    (Result.combine_prop (Result.list_map (P := fun v => ~ In (fst v) (map fst nloc)) _ nin)
    (Result.combine_prop (Result.list_map (P := fun v => forall ty', In (fst v, ty') nout -> ty' = snd v) _ nout)
    (Result.combine_prop (Result.list_map (P := fun v => ~ In (fst v) (map fst nloc)) _ nout)
                         (Result.list_map (P := fun v => forall ty', In (fst v, ty') nloc -> ty' = snd v) _ nloc)))))) _).
  all: try refine (fun v => match In_dec PeanoNat.Nat.eq_dec _ _ with left _ => _ | right h => Result.Ok h end).
  1: rename nin into nlist.
  4: rename nout into nlist.
  6: rename nloc into nlist.
  1-6: try (intros [b t]; refine (match forall_type_dec (* Technically, does not check for duplicates, only variables with same ID but different types *)
        (fun ty' => In (b, ty') nlist -> ty' = t)
        ltac:(
          intros ty;
          destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Source.type_dec) (b, ty) nlist) as [Hin|Hnin]; [|left; intros f; contradiction (Hnin f)];
          destruct (Source.type_dec ty t) as [eqty|nety]; [left; intros _; exact eqty|];
          right; intros f; exact (nety (f Hin)))
        with left h => Result.Ok h | right _ => _ end)).
  1: exact (Result.Err [(l, Result.MultipleDeclaration b Result.DeclInput Result.DeclInput)]).
  1: exact (Result.Err [(l, Result.MultipleDeclaration (fst v) Result.DeclInput Result.DeclOutput)]).
  1: exact (Result.Err [(l, Result.MultipleDeclaration (fst v) Result.DeclInput Result.DeclLocal)]).
  1: exact (Result.Err [(l, Result.MultipleDeclaration b Result.DeclOutput Result.DeclOutput)]).
  1: exact (Result.Err [(l, Result.MultipleDeclaration (fst v) Result.DeclOutput Result.DeclLocal)]).
  1: exact (Result.Err [(l, Result.MultipleDeclaration b Result.DeclLocal Result.DeclLocal)]).
  intros (innotdup' & innotout' & innotloc' & outnotdup' & outnotloc' & locnotdup').
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
  clear l nin nout nloc eq1 eq2 eq3 innotdup' innotout' innotloc' outnotdup' outnotloc' locnotdup'.
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

Definition check_node_prop (entry: Source.node): Result.t Target.type Target.node :=
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
  do '(exist _ n_body (conj vars_all_assigned vars_exist), vars_unique) <-
    Result.combine (check_body temp entry) (vars_unique (Source.n_loc entry) temp);
  Result.Ok {|
      Target.n_loc := Source.n_loc entry;
      Target.n_name := Source.n_name entry;
      Target.n_in := n_in;
      Target.n_out := n_out;
      Target.n_locals := n_locals;
      Target.n_body := n_body;
      Target.n_vars_all_assigned := vars_all_assigned;
      Target.n_vars_unique := vars_unique;
      Target.n_all_vars_exist := vars_exist;
    |}.
