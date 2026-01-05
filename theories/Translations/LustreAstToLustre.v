Set Default Goal Selector "!".

From Reactive.Datatypes Require Hashtable Result.
From Reactive.Languages Require LustreAst Lustre.
From Reactive.Languages Require Import Semantics.
From Reactive.Props Require Import Dec Forall Identifier.

From Stdlib Require ListDec FMaps.
From Stdlib Require Import Bool List Nat Permutation Sorting String.

Import ListNotations.

Module Source := LustreAst.
Module Target := Lustre.

From Stdlib Require FMaps.

Module StringKey.
  Definition t : Type := string.
  Definition eq (s1 s2 : t) := s1 = s2.
  Definition lt (s1 s2 : t) := ltb s1 s2 = true.
  Definition eq_refl : forall s : t, eq s s := @eq_refl _.
  Definition eq_sym : forall s1 s2 : t, eq s1 s2 -> eq s2 s1 := @eq_sym _.
  Definition eq_trans : forall s1 s2 s3 : t, eq s1 s2 -> eq s2 s3 -> eq s1 s3 := @eq_trans _.
  Definition lt_trans : forall s1 s2 s3 : t, lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Proof using.
    unfold lt, ltb.
    intros s1 s2 s3 H12 H23.
    induction s1 as [|c1 s1 IH1] in s2, s3, H12, H23 |- *.
    1: destruct s2; [discriminate H12|destruct s3; [discriminate H23|reflexivity]].
    destruct s2 as [|c2 s2]; [discriminate H12|].
    destruct s3 as [|c3 s3]; [discriminate H23|].
    cbn in *.
    destruct (Ascii.compare c1 c2) as [| |] eqn:eq12; [apply Ascii.compare_eq_iff in eq12; subst c1|clear H12|discriminate H12].
    1: destruct (Ascii.compare c2 c3); [exact (IH1 _ _ H12 H23)|reflexivity|discriminate H23].
    destruct (Ascii.compare c2 c3) eqn:eq23; [| |discriminate H23].
    1: apply Ascii.compare_eq_iff in eq23; subst c3; rewrite eq12; reflexivity.
    unfold Ascii.compare in eq12; rewrite BinNat.N.compare_lt_iff in eq12.
    unfold Ascii.compare in eq23; rewrite BinNat.N.compare_lt_iff in eq23.
    specialize (BinNat.N.lt_trans _ _ _ eq12 eq23) as lt13.
    apply BinNat.N.compare_lt_iff in lt13.
    unfold Ascii.compare; rewrite lt13.
    reflexivity.
  Defined.
  Definition lt_not_eq : forall s1 s2 : t, lt s1 s2 -> ~ eq s1 s2.
  Proof using.
    intros s ? H <-.
    induction s as [|c s IH]; [discriminate H|refine (IH _)].
    unfold lt, ltb, compare, Ascii.compare in *; fold compare in *.
    rewrite (BinNat.N.compare_refl _) in H.
    exact H.
  Defined.
  Definition compare : forall s1 s2 : t, OrderedType.Compare lt eq s1 s2.
  Proof using.
    intros s1 s2; destruct (String.compare s1 s2) eqn:eqcmp;
      [refine (OrderedType.EQ _)|refine (OrderedType.LT _)|refine (OrderedType.GT _)].
    1: apply String.compare_eq_iff; exact eqcmp.
    1: unfold lt, ltb; rewrite eqcmp; reflexivity.
    1: unfold lt, ltb; rewrite String.compare_antisym, eqcmp; reflexivity.
  Defined.
  Definition eq_dec : forall s1 s2 : t, { eq s1 s2 } + { ~ eq s1 s2 } := String.string_dec.
End StringKey.
Module StringMap <: FMapInterface.S with Module E := StringKey := FMapList.Make(StringKey).

Record common_temp : Type := {
  orig :> Source.node;
  
  smap: StringMap.t (ident * Result.declaration_location);
  n_in: list binder;
  n_out: list binder;
  n_locals: list binder;
  
  nvars := n_in ++ n_out ++ n_locals;
  Hnvars:
    Forall2 (fun '(x, tx) '(l, (v, tv)) =>
        StringMap.find v smap = Some (x, l) /\
        tx = tv)
      nvars
      (map (pair Result.DeclInput) orig.(Source.n_in) ++
       map (pair Result.DeclOutput) orig.(Source.n_out) ++
       map (pair Result.DeclLocal) orig.(Source.n_locals));
  
  seed: ident;
  Hseed: forall n, ~ In (iter n next_ident seed) (map fst nvars);
  
  env: Dict.t type;
  Henv: forall x t, Dict.maps_to x t env <-> In (x, t) (n_in ++ n_out ++ n_locals);
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
Definition typecheck_exp {P : forall ty, Target.exp ty -> Prop} (loc: Result.location) (e: { ty & sig (P ty) }) (t: type):
    Result.t type (sig (P t)) := match e, t with
  | existT _ TVoid (exist _ e H), TVoid => Result.Ok (exist _ e H)
  | existT _ TBool (exist _ e H), TBool => Result.Ok (exist _ e H)
  | existT _ TInt (exist _ e H), TInt => Result.Ok (exist _ e H)
  | existT _ ety _, _ => Result.Err [(loc, Result.BadType [t] ety)]
end.

Fixpoint check_exp (temp: common_temp) (e: Source.exp): Result.t type
  { ty & { exp : Target.exp ty | incl (Target.var_of_exp exp) (nvars temp) } }.
Proof.
  destruct e as [ l c | l n | l op e | l op e1 e2 | l e1 e2 e3 ].
  - left.
    destruct c as [ b | n ].
    + exists TBool, (Target.EConst l (CBool b)); intros ? [].
    + exists TInt, (Target.EConst l (CInt n)); intros ? [].
  - destruct (StringMap.find n (smap temp)) as [ [ i dl ] | ] eqn:eqi.
    2: right; exact [(l, Result.UndeclaredVariable n)].
    destruct (Dict.find i (env temp)) as [ ty | ] eqn:eqty.
    2: right; exact [(l, Result.InternalError ("Variable " ++ n ++ " has an ID but no type"))].
    left.
    exists ty, (Target.EVar l (i, ty)).
    intros ? [<-|[]]; cbn.
    apply temp.(Henv).
    exact eqty.
  - refine (Result.bind (check_exp temp e) _).
    intros e'.
    destruct (translate_unop op) as [ tin [ tout top ]].
    refine (Result.bind (typecheck_exp l e' tin) _).
    intros [ e'' He ].
    refine (Result.Ok _); exists tout, (Target.EUnop l top e'').
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
    refine (Result.Ok _); exists tout, (Target.EBinop l top e1'' e2'').
    cbn; rewrite Target.var_of_exp_aux_eq.
    apply incl_app; assumption.
  - refine (Result.bind (check_exp temp e1) _).
    intros e1'.
    refine (Result.bind (typecheck_exp l e1' TBool) _).
    intros [ e1'' He1 ].
    refine (Result.bind (check_exp temp e2) _).
    intros e2'.
    refine (Result.bind (check_exp temp e3) _).
    intros e3'.
    destruct e2' as [t [e2'' He2]].
    refine (Result.bind (typecheck_exp l e3' t) _).
    intros [ e3'' He3 ].
    refine (Result.Ok _); exists t, (Target.EIfte l e1'' e2'' e3'').
    cbn; rewrite !Target.var_of_exp_aux_eq, app_nil_r.
    repeat apply incl_app; assumption.
Defined.

Definition check_body (temp: common_temp) (entry: Source.node): Result.t type
  { body : list Target.equation
  | Permutation (map Target.equation_dest body) (n_out temp ++ n_locals temp) /\
    Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in temp ++ n_out temp ++ n_locals temp)) body }.
Proof.
  destruct entry as [nloc n nin out loc eqs]; clear n nin out loc.
  refine (Result.bind _
    (fun res : { rem & { body | Permutation (rem ++ map Target.equation_dest body) (n_out temp ++ n_locals temp) /\
                                Forall (fun eq => incl (Target.var_of_exp (projT2 (snd eq))) (n_in temp ++ n_out temp ++ n_locals temp)) body } } =>
      match res with
      | existT _ [] ret => Result.Ok ret
      | existT _ ((i, ty) :: _) _ => Result.Err [(nloc, Result.MissingAssignment "<information lost>" i ty)] end)).
  induction eqs as [ | [ l [ n e ] ] tl IH ].
  - refine (Result.Ok (existT _ (n_out temp ++ n_locals temp) (exist _ [] _))); split.
    1: rewrite app_nil_r; exact (Permutation_refl _).
    exact (Forall_nil _).
  - refine (Result.bind (Result.combine (check_exp temp e) IH) _); clear IH.
    destruct (StringMap.find n (smap temp)) as [ [ i l' ] | ] eqn:eqni.
    2: intros _; exact (Result.Err [(l, Result.UndeclaredVariable n)]).
    intros [ [ ty [ e' He ] ] [ rem [ eqs [ IH1 IH2 ] ] ] ].
    pose (rev_lhs := @nil (ident * type)); change rem with (rev_lhs ++ rem) in IH1.
    generalize dependent rev_lhs; induction rem as [ | [ i' ty' ] rem IH ]; intros rev_lhs Hperm.
    1: refine (Result.Err [(l, _)]); destruct temp as [? ? ? nin ? ? ?]; clear - n i nin.
    1: induction nin as [|[hdn hdt] tl IH].
    1:  exact (Result.UndeclaredVariable n).
    1: destruct (PeanoNat.Nat.eq_dec i hdn) as [_|_].
    1:  exact (Result.AssignToInput n i hdt).
    1: exact IH.
    destruct (PeanoNat.Nat.eq_dec i i') as [ <- | nnei ].
    2: refine (IH ((i', ty') :: rev_lhs) (Permutation_trans (Permutation_app_tail _ _) Hperm)).
    2: rewrite (app_assoc _ [_] _ : _ ++ (i', ty') :: _ = _).
    2: exact (Permutation_app_tail _ (Permutation_cons_append _ _)).
    destruct (type_dec ty ty') as [ <- | nety ].
    2: exact (Result.Err [(l, Result.IncompatibleTypeAssignment n i ty' ty)]).
    refine (Result.Ok (existT _ (rev_append rev_lhs rem) (exist _ ((i, existT Target.exp ty e') :: eqs) _))).
    split; [|refine (Forall_cons _ _ IH2); exact He].
    rewrite (app_assoc _ [_] _ : _ ++ map Target.equation_dest ((_, _) :: _) = (_ ++ _) ++ map _ _), rev_append_rev.
    refine (Permutation_trans (Permutation_app_tail _ _) Hperm); unfold Target.equation_dest, fst, snd, projT1.
    rewrite <-app_assoc; exact (Permutation_sym (Permutation_app (Permutation_rev _) (Permutation_cons_append _ _))).
Defined.

Definition n_assigned_vars (body: list Target.equation) :=
  map Target.equation_dest body.

Scheme Equality for list.

(* TODO: merge with check_Henv *)
Definition vars_unique (l: Result.location) (temp: common_temp) :
  Result.t type (NoDup ((map fst (n_in temp ++ n_out temp ++ n_locals temp)))).
Proof using.
  induction (n_in temp) as [ | hd tl IH ].
  2:{
    refine (Result.bind (Result.combine_prop _ IH) (fun '(conj H1 H2) => Result.Ok (NoDup_cons _ H1 H2))); clear IH.
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst tl)) as [ _ | nin ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration "<information lost>" (fst hd) Result.DeclInput Result.DeclInput)]).
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst (n_out temp))) as [ _ | nout ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration "<information lost>" (fst hd) Result.DeclInput Result.DeclOutput)]).
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst (n_locals temp))) as [ _ | nloc ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration "<information lost>" (fst hd) Result.DeclInput Result.DeclLocal)]).
    refine (Result.Ok _).
    rewrite !map_app, !in_app_iff; tauto.
  }
  induction (n_out temp) as [ | hd tl IH ].
  2:{
    refine (Result.bind (Result.combine_prop _ IH) (fun '(conj H1 H2) => Result.Ok (NoDup_cons _ H1 H2))); clear IH.
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst tl)) as [ _ | nin ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration "<information lost>" (fst hd) Result.DeclOutput Result.DeclOutput)]).
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst (n_locals temp))) as [ _ | nloc ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration "<information lost>" (fst hd) Result.DeclOutput Result.DeclLocal)]).
    refine (Result.Ok _).
    rewrite !map_app, !in_app_iff; tauto.
  }
  induction (n_locals temp) as [ | hd tl IH ].
  2:{
    refine (Result.bind (Result.combine_prop _ IH) (fun '(conj H1 H2) => Result.Ok (NoDup_cons _ H1 H2))); clear IH.
    destruct (In_dec PeanoNat.Nat.eq_dec (fst hd) (map fst tl)) as [ _ | nin ].
    1: exact (Result.Err [(l, Result.MultipleDeclaration "<information lost>" (fst hd) Result.DeclLocal Result.DeclLocal)]).
    refine (Result.Ok _).
    rewrite !map_app, !in_app_iff; tauto.
  }
  exact (Result.Ok (NoDup_nil _)).
Defined.

Definition build_map (entry: Source.node) :
  { sm & { seed & Result.t type { n_in & { n_out & { n_locals & { sm_inv : Hashtable.t ident string |
    Forall (fun v => forall ty', In (fst v, ty') n_in -> ty' = snd v) n_in /\
    Forall (fun v => forall ty', In (fst v, ty') n_out -> ty' = snd v) n_out /\
    Forall (fun v => forall ty', In (fst v, ty') n_locals -> ty' = snd v) n_locals /\
    Forall (fun v => ~ In (fst v) (map fst n_out)) n_in /\
    Forall (fun v => ~ In (fst v) (map fst n_locals)) n_in /\
    Forall (fun v => ~ In (fst v) (map fst n_locals)) n_out /\
    Forall2 (fun '(x, tx) '(l, (v, tv)) =>
        StringMap.find v sm = Some (x, l) /\
        tx = tv)
      (n_in ++ n_out ++ n_locals)
      (map (pair Result.DeclInput) entry.(Source.n_in) ++
       map (pair Result.DeclOutput) entry.(Source.n_out) ++
       map (pair Result.DeclLocal) entry.(Source.n_locals)) /\
    (forall n, ~ In (iter n next_ident seed) (map fst (n_in ++ n_out ++ n_locals))) /\
    (forall x, Hashtable.InMap x sm_inv <-> In x (map fst (n_in ++ n_out ++ n_locals))) } } } } } }.
Proof using.
  destruct entry as [l n nin out loc body]; unfold Source.n_in, Source.n_out, Source.n_locals; clear n body.
  induction nin as [ | [n ty] vars (sm & seed & IH) ].
  2:{
    destruct (StringMap.find n sm) as [ [ i dl ] | ] eqn:eqnsm.
    1: exists sm, seed;
       exact (Result.Err ((l, Result.MultipleDeclaration n i Result.DeclInput dl) :: match IH with Result.Ok _ => [] | Result.Err es => es end)).
    exists (StringMap.add n (seed, Result.DeclInput) sm), (next_ident seed);
      refine (Result.bind IH _); clear IH;
      intros (IHnin & IHout & IHloc & IHsm_inv & IHii & IHoo & IHll & IHio & IHil & IHol & IH1 & IH2 & IHinv);
      left; exists ((seed, ty) :: IHnin), IHout, IHloc, (Hashtable.add IHsm_inv seed n (fun H => IH2 O (proj1 (IHinv _) H))).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    + constructor; [intros ty' [[=<-]|H]; [exact eq_refl|exfalso; refine (IH2 O _)]|].
      1: rewrite map_app; exact (in_or_app _ _ _ (or_introl (in_map fst _ _ H))).
      assert (Hseed : ~ In seed (map fst IHnin))
        by (rewrite map_app in IH2; exact (fun f => IH2 O (in_or_app _ _ _ (or_introl f)))).
      clear - IHii Hseed.
      refine (proj2 (Forall_forall _ _) _).
      intros [v tv] Hv ty' [[=f _]|H]; [contradict Hseed; subst; exact (in_map fst _ _ Hv)|].
      exact (proj1 (Forall_forall _ _) IHii _ Hv _ H).
    + constructor; [|assumption]. refine (fun f => IH2 O _).
      rewrite map_app; refine (in_or_app _ _ _ (or_intror _)).
      rewrite map_app; exact (in_or_app _ _ _ (or_introl f)).
    + constructor; [|assumption]. refine (fun f => IH2 O _).
      rewrite map_app; refine (in_or_app _ _ _ (or_intror _)).
      rewrite map_app; exact (in_or_app _ _ _ (or_intror f)).
    + constructor; [split; [|exact eq_refl]|].
      1: exact (StringMap.find_1 (StringMap.add_1 _ _ eq_refl)).
      refine (Forall2_impl _ _ IH1); clear - eqnsm.
      intros [x tx] [l' [v tv]] [H1 H2]; split; [clear tx tv H2|exact H2].
      refine (StringMap.find_1 (StringMap.add_2 _ _ (StringMap.find_2 H1))).
      intros <-; rewrite eqnsm in H1; discriminate H1.
    + intros k [H|H]; [|exact (eq_ind _ (fun v => ~ In v _) (IH2 (S k)) _ (PeanoNat.Nat.iter_succ_r _ _ _ _) H)].
      cbn in H; clear - H.
      assert (tmp : seed < iter k next_ident (S seed)); [|rewrite H in tmp at 1; exact (PeanoNat.Nat.lt_irrefl _ tmp)].
      induction k as [|n IH] in seed |- *; [exact (le_n _)|].
      exact (le_S _ _ (IH _)).
    + intros x; split.
      1: intros H; apply Hashtable.In_add_inv in H; destruct H as [->|H]; [left; exact eq_refl|right; apply IHinv; exact H].
      1: intros [[=->]|H]; [exact (Hashtable.In_add_same _ _ _ _)|refine (Hashtable.In_add_pre _ _); apply IHinv; exact H].
  }
  refine (match _ : { sm & { seed & Result.t _ { n_out & { n_locals & { sm_inv |
                      _ /\ _ /\ _ /\ Forall2 _ (n_out ++ _) (map _ out ++ _) /\ (forall n, ~ In _ (map _ (n_out ++ _))) /\
                      (forall x, _ <-> In x (map fst (n_out ++ _)))}}}}} with
    | existT _ sm (existT _ seed (Result.Ok (existT _ n_out (existT _ n_locals
         (exist _ sm_inv (conj Hoo (conj Hll (conj Hol (conj H1 (conj H2 H3)))))))))) =>
        existT _ sm (existT _ seed (Result.Ok (
          existT _ [] (existT _ n_out (existT _ n_locals (exist _ sm_inv
            (conj (Forall_nil _) (conj Hoo (conj Hll (conj (Forall_nil _) (conj (Forall_nil _) (conj Hol (conj H1 (conj H2 H3))))))))))))))
    | existT _ sm (existT _ seed (Result.Err e)) => existT _ sm (existT _ seed (Result.Err e)) end).
  induction out as [ | [n ty] vars (sm & seed & IH) ].
  2:{
    destruct (StringMap.find n sm) as [ [ i dl ] | ] eqn:eqnsm.
    1: exists sm, seed;
       refine (Result.Err ((l, Result.MultipleDeclaration n i Result.DeclOutput dl) :: match IH with Result.Ok _ => [] | Result.Err es => es end)).
    exists (StringMap.add n (seed, Result.DeclOutput) sm), (next_ident seed);
      refine (Result.bind IH _);
      intros (IHout & IHloc & IHsm_inv & IHoo & IHll & IHol & IH1 & IH2 & IHinv);
      left; exists ((seed, ty) :: IHout), IHloc, (Hashtable.add IHsm_inv seed n (fun H => IH2 O (proj1 (IHinv _) H))).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    + constructor; [intros ty' [[=<-]|H]; [exact eq_refl|exfalso; refine (IH2 O _)]|].
      1: rewrite map_app; exact (in_or_app _ _ _ (or_introl (in_map fst _ _ H))).
      assert (Hseed : ~ In seed (map fst IHout))
        by (rewrite map_app in IH2; exact (fun f => IH2 O (in_or_app _ _ _ (or_introl f)))).
      clear - IHoo Hseed.
      refine (proj2 (Forall_forall _ _) _).
      intros [v tv] Hv ty' [[=f _]|H]; [contradict Hseed; subst; exact (in_map fst _ _ Hv)|].
      exact (proj1 (Forall_forall _ _) IHoo _ Hv _ H).
    + constructor; [|assumption]. refine (fun f => IH2 O _).
      rewrite map_app; exact (in_or_app _ _ _ (or_intror f)).
    + constructor; [split; [|exact eq_refl]|].
      1: exact (StringMap.find_1 (StringMap.add_1 _ _ eq_refl)).
      refine (Forall2_impl _ _ IH1); clear - eqnsm.
      intros [x tx] [l' [v tv]] [H1 H2]; split; [clear tx tv H2|exact H2].
      refine (StringMap.find_1 (StringMap.add_2 _ _ (StringMap.find_2 H1))).
      intros <-; rewrite eqnsm in H1; discriminate H1.
    + intros k [H|H]; [|exact (eq_ind _ (fun v => ~ In v _) (IH2 (S k)) _ (PeanoNat.Nat.iter_succ_r _ _ _ _) H)].
      cbn in H; clear - H.
      assert (tmp : seed < iter k next_ident (S seed)); [|rewrite H in tmp at 1; exact (PeanoNat.Nat.lt_irrefl _ tmp)].
      induction k as [|n IH] in seed |- *; [exact (le_n _)|].
      exact (le_S _ _ (IH _)).
    + intros x; split.
      1: intros H; apply Hashtable.In_add_inv in H; destruct H as [->|H]; [left; exact eq_refl|right; apply IHinv; exact H].
      1: intros [[=->]|H]; [exact (Hashtable.In_add_same _ _ _ _)|refine (Hashtable.In_add_pre _ _); apply IHinv; exact H].
  }
  refine (match _ : { sm & { seed & Result.t _ { n_locals & { sm_inv |
                      _ /\ Forall2 _ n_locals (map _ _) /\ (forall n, ~ In _ (map _ n_locals)) /\ (forall x, _ <-> In _ (map _ n_locals))}}}} with
    | existT _ sm (existT _ seed (Result.Ok (existT _ n_locals (exist _ sm_inv (conj Hll (conj H1 (conj H2 H3))))))) =>
        existT _ sm (existT _ seed (Result.Ok (
          existT _ [] (existT _ n_locals (exist _ sm_inv
            (conj (Forall_nil _) (conj Hll (conj (Forall_nil _) (conj H1 (conj H2 H3))))))))))
    | existT _ sm (existT _ seed (Result.Err e)) => existT _ sm (existT _ seed (Result.Err e)) end).
  induction loc as [ | [n ty] vars (sm & seed & IH) ].
  2:{
    destruct (StringMap.find n sm) as [ [ i dl ] | ] eqn:eqnsm.
    1: exists sm, seed;
       refine (Result.Err ((l, Result.MultipleDeclaration n i Result.DeclLocal dl) :: match IH with Result.Ok _ => [] | Result.Err es => es end)).
    exists (StringMap.add n (seed, Result.DeclLocal) sm), (next_ident seed);
      refine (Result.bind IH _);
      intros (IHloc & IHsm_inv & IHll & IH1 & IH2 & IHinv);
      left; exists ((seed, ty) :: IHloc), (Hashtable.add IHsm_inv seed n (fun H => IH2 O (proj1 (IHinv _) H))).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    + constructor; [intros ty' [[=<-]|H]; [exact eq_refl|exfalso; refine (IH2 O _)]|].
      1: exact (in_map fst _ _ H).
      assert (Hseed : ~ In seed (map fst IHloc))
        by (exact (fun f => IH2 O f)).
      clear - IHll Hseed.
      refine (proj2 (Forall_forall _ _) _).
      intros [v tv] Hv ty' [[=f _]|H]; [contradict Hseed; subst; exact (in_map fst _ _ Hv)|].
      exact (proj1 (Forall_forall _ _) IHll _ Hv _ H).
    + constructor; [split; [|exact eq_refl]|].
      1: exact (StringMap.find_1 (StringMap.add_1 _ _ eq_refl)).
      refine (Forall2_impl _ _ IH1); clear - eqnsm.
      intros [x tx] [l' [v tv]] [H1 H2]; split; [clear tx tv H2|exact H2].
      refine (StringMap.find_1 (StringMap.add_2 _ _ (StringMap.find_2 H1))).
      intros <-; rewrite eqnsm in H1; discriminate H1.
    + intros k [H|H]; [|exact (eq_ind _ (fun v => ~ In v _) (IH2 (S k)) _ (PeanoNat.Nat.iter_succ_r _ _ _ _) H)].
      cbn in H; clear - H.
      assert (tmp : seed < iter k next_ident (S seed)); [|rewrite H in tmp at 1; exact (PeanoNat.Nat.lt_irrefl _ tmp)].
      induction k as [|n IH] in seed |- *; [exact (le_n _)|].
      exact (le_S _ _ (IH _)).
    + intros x; split.
      1: intros H; apply Hashtable.In_add_inv in H; destruct H as [->|H]; [left; exact eq_refl|right; apply IHinv; exact H].
      1: intros [[=->]|H]; [exact (Hashtable.In_add_same _ _ _ _)|refine (Hashtable.In_add_pre _ _); apply IHinv; exact H].
  }
  exists (StringMap.empty _), O; left; exists [], (Hashtable.create _ _ O); split; [exact (Forall_nil _)|split; [exact (Forall2_nil _)|]].
  split; [intros ? f; exact f|intros x; split; [intros H; exact (Hashtable.In_create H)|intros []]].
Defined.

Lemma check_Henv {n_in n_out n_loc} :
  Forall (fun v => forall ty', In (fst v, ty') n_in -> ty' = snd v) n_in ->
  Forall (fun v => forall ty', In (fst v, ty') n_out -> ty' = snd v) n_out ->
  Forall (fun v => forall ty', In (fst v, ty') n_loc -> ty' = snd v) n_loc ->
  Forall (fun v => ~ In (fst v) (map fst n_out)) n_in ->
  Forall (fun v => ~ In (fst v) (map fst n_loc)) n_in ->
  Forall (fun v => ~ In (fst v) (map fst n_loc)) n_out ->
  forall n t,
    Dict.maps_to n t
      (fold_left (fun acc '(n, t) => Dict.add n t acc)
       (n_in ++ n_out ++ n_loc)
       (Dict.empty type)) <->
    In (n, t) (n_in ++ n_out ++ n_loc)%list.
Proof using.
  rename n_in into nin, n_out into nout, n_loc into nloc.
  intros innotdup' outnotdup' locnotdup' innotout' innotloc' outnotloc' n t.
  match goal with |- Dict.maps_to _ _ (fold_left ?f ?l ?d) <-> _ =>
  rewrite <-(fold_left_rev_right (fun x y => f y x) l d) end.
  rewrite (in_rev (nin ++ nout ++ nloc) (n, t)),
          !rev_app_distr, <-!app_assoc.
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

Import Result.notations.

Definition check_node_prop (entry: Source.node): Result.t type (Hashtable.t ident string * Target.node) :=
  let '(existT _ sm (existT _ seed tmp)) := build_map entry in
  do '(existT _ n_in (existT _ n_out (existT _ n_loc (exist _ sm_inv
        (conj Hii (conj Hoo (conj Hll (conj Hio (conj Hil (conj Hol (conj Hnvars (conj Hseed _)))))))))))) <- tmp;
  let Henv := check_Henv Hii Hoo Hll Hio Hil Hol in
  let temp := {|
    orig := entry;
    n_in := n_in;
    n_out := n_out;
    n_locals := n_loc;
    
    Hnvars := Hnvars;
    
    seed := seed;
    Hseed := Hseed;
    
    env := fold_left (fun acc '(n, t) => Dict.add n t acc) (n_in ++ n_out ++ n_loc) (Dict.empty _);
    Henv := Henv;
  |} in
  do '(exist _ n_body (conj vars_all_assigned vars_exist), vars_unique) <-
    Result.combine (check_body temp entry) (vars_unique (Source.n_loc entry) temp);
  Result.Ok (sm_inv, {|
      Target.n_loc := Source.n_loc entry;
      Target.n_name := Source.n_name entry;
      Target.n_in := n_in;
      Target.n_out := n_out;
      Target.n_locals := n_loc;
      Target.n_body := n_body;
      Target.n_all_vars_exist := vars_exist;
      Target.n_vars_all_assigned := vars_all_assigned;
      Target.n_vars_unique := vars_unique;
      Target.n_seed := seed;
      Target.n_seed_always_fresh := Hseed;
    |}).
