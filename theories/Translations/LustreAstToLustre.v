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
Definition typecheck_exp (loc: Result.location) (e: sigT Target.exp) (t: Target.type): Result.t Target.type (Target.exp t) := match e, t with
  | existT _ Target.TVoid e, Target.TVoid => Result.Ok e
  | existT _ Target.TBool e, Target.TBool => Result.Ok e
  | existT _ Target.TInt e, Target.TInt => Result.Ok e
  | existT _ ety _, _ => Result.Err [(loc, Result.BadType [t] ety)]
end.

Fixpoint check_exp (temp: common_temp) (e: Source.exp): Result.t Target.type (sigT Target.exp).
Proof.
  destruct e as [ l c | l n | l n | l op e | l op e1 e2 | l e1 e2 e3 ].
  - left.
    destruct c as [ | b | n ].
    + exists Target.TVoid.
      exact (Target.EConst Target.CVoid).
    + exists Target.TBool.
      exact (Target.EConst (Target.CBool b)).
    + exists Target.TInt.
      exact (Target.EConst (Target.CInt n)).
  - destruct (Dict.find n (env temp)) as [ ty | ].
    2: right; exact [(l, Result.UndeclaredInput n)].
    left.
    exists ty.
    exact (Target.EInput (n, ty)).
  - destruct (Dict.find n (env temp)) as [ ty | ].
    2: right; exact [(l, Result.UndeclaredVariable n)].
    left.
    exists ty.
    exact (Target.EVar (n, ty)).
  - refine (Result.bind (check_exp temp e) _).
    intros e'.
    destruct (translate_unop op) as [ tin [ tout top ]].
    refine (Result.bind (typecheck_exp l e' tin) _).
    intros e''.
    exact (Result.Ok (existT _ tout (Target.EUnop top e''))).
  - refine (Result.bind (check_exp temp e1) _).
    intros e1'.
    refine (Result.bind (check_exp temp e2) _).
    intros e2'.
    destruct (translate_binop op) as [ tin1 [ tin2 [ tout top ]]].
    refine (Result.bind (typecheck_exp l e1' tin1) _).
    intros e1''.
    refine (Result.bind (typecheck_exp l e2' tin2) _).
    intros e2''.
    exact (Result.Ok (existT _ tout (Target.EBinop top e1'' e2''))).
  - refine (Result.bind (check_exp temp e1) _).
    intros e1'.
    refine (Result.bind (typecheck_exp l e1' Target.TBool) _).
    intros e1''.
    refine (Result.bind (check_exp temp e2) _).
    intros e2'.
    refine (Result.bind (check_exp temp e3) _).
    intros e3'.
    destruct e2' as [t e2''].
    refine (Result.bind (typecheck_exp l e3' t) _).
    intros e3''.
    exact (Result.Ok (existT _ t (Target.EIfte e1'' e2'' e3''))).
Defined.

Definition check_body (temp: common_temp) (entry: Source.node): Result.t Target.type
  { body : list Target.equation | incl (map Target.equation_dest body) (nvars temp) }.
Proof.
  destruct entry.
  induction n_body as [ | [ l [ n e ] ] tl IH ].
  - left.
    exists [].
    exact (incl_nil_l _).
  - refine (Result.bind (Result.combine (check_exp temp e) IH) _); clear IH.
    intros [ [ ty e' ] [ eqs IH ] ].
    destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Target.type_dec) (n, ty) (nvars temp)) as [Hin|_].
    2: refine (Result.Err [(l, _)]).
    2: destruct temp as [? ? ? ? ? ? nvars H]; cbn; fold nvars; clear H IH; generalize dependent nvars; intros nvars; clear - l n ty nvars.
    2: induction nvars as [|[hdn hdt] tl IH].
    2:  exact (Result.NeverAssigned n ty).
    2: destruct (PeanoNat.Nat.eq_dec n hdn) as [neqhdn|_].
    2:  exact (Result.IncompatibleTypeAssignment hdn hdt ty).
    2: exact IH.
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

Definition check_assigned_out (l: Result.location) (temp: common_temp) body: Result.t Target.type (incl (n_out temp) (n_assigned_vars body)).
Proof.
  refine (Result.bind (Result.list_map _ _) (fun H => Result.Ok (proj2 (incl_Forall_in_iff _ _) H))).
  intros b.
  destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Target.type_dec) b (n_assigned_vars body)) as [Hin|Hnin].
  1: exact (Result.Ok Hin).
  exact (Result.Err [(l, Result.NeverAssigned (fst b) (snd b))]).
Defined.

Definition n_out_is_not_an_input (l: Result.location) (temp: common_temp) :
  Result.t Target.type (Forall (fun b => ~ In (fst b) (map fst (n_in temp))) (n_out temp)) :=
  Result.list_map (fun b => match In_dec PeanoNat.Nat.eq_dec _ _ with
    | left _ => Result.Err [(l, Result.MultipleDeclaration (fst b) Result.DeclInput Result.DeclOutput)]
    | right h => Result.Ok h
  end) _.


Definition n_inputs_equations (l: Result.location) (temp: common_temp) body:
  Result.t Target.type (incl (List.map (fun '((n, ty) as b) => (n, existT Target.exp ty (Target.EInput b))) (n_in temp)) body).
Proof.
  refine (Result.bind (Result.list_map _ _) (fun H => Result.Ok (proj2 (incl_Forall_in_iff _ _) H))).
  intros [n [ty e]].
  exact (match In_dec (prod_dec PeanoNat.Nat.eq_dec (sigT_dec Target.type_dec (@Target.exp_dec))) _ _ with
    | left h => Result.Ok h
    | right _ => Result.Err [(l, Result.InternalError "Missing extra input equation")]
    end).
Defined.


Definition n_no_einputs_in_other (l: Result.location) (temp: common_temp) (body: list Target.equation):
  Result.t Target.type (Forall (fun '(name, existT _ _ exp) => ~ In name (map fst (n_in temp)) -> Target.has_einput exp = false) body).
Proof.
  refine (Result.list_map _ _).
  intros [n [ty e]].
  refine (match ListDec.In_dec PeanoNat.Nat.eq_dec _ _ with left h => Result.Ok (fun f => False_ind _ (f h)) | right h => _ end).
  destruct (Target.has_einput e); [ refine (Result.Err [(l, Result.InternalError "Non-input equation contains an EInput")]) | left; reflexivity ].
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
  do '(exist _ n_body assigned_vars_are_vars) <- check_body temp entry;
  do '(conj check_assigned (conj n_out_is_not_an_input (conj n_inputs_equations n_no_einputs_in_other))) <-
    Result.combine_prop (check_assigned_out (Source.n_loc entry) temp n_body) (
    Result.combine_prop (n_out_is_not_an_input (Source.n_loc entry) temp) (
    Result.combine_prop (n_inputs_equations (Source.n_loc entry) temp n_body) (
                        (n_no_einputs_in_other (Source.n_loc entry) temp n_body))));
  Result.Ok {|
      Target.n_loc := Source.n_loc entry;
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
