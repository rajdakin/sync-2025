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

Lemma type_conversion (t1 t2 : Source.type):
  t1 = t2 <-> convert_type t1 = convert_type t2.
Proof.
  destruct t1, t2.
  all: firstorder.
  all: discriminate.
Qed.

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
  n_in: list Target.binder;
  n_out: list Target.binder;
  n_locals: list Target.binder;
  
  nvars := n_in ++ n_out ++ n_locals;
  Hnvars:
    Forall2 (fun '(x, tx) '(l, (v, tv)) =>
        StringMap.find v smap = Some (x, l) /\
        tx = convert_type tv)
      nvars
      (map (pair Result.DeclInput) orig.(Source.n_in) ++
       map (pair Result.DeclOutput) orig.(Source.n_out) ++
       map (pair Result.DeclLocal) orig.(Source.n_locals));
  
  seed: ident;
  Hseed: forall n, ~ In (iter n next_ident seed) (map fst nvars);
  
  env: Dict.t Target.type;
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
  - destruct (StringMap.find n (smap temp)) as [ [ i l' ] | ].
    2: right; exact [(l, Result.UndeclaredInput n None)].
    refine (match l' with Result.DeclInput => _ | _ => Result.Err [(l, Result.UndeclaredInput n (Some i))] end).
    clear l'.
    destruct (Dict.find i (env temp)) as [ ty | ].
    2: right; exact [(l, Result.InternalError ("Input " ++ n ++ " has an ID but no type"))].
    left.
    exists ty.
    exact (Target.EInput (i, ty)).
  - destruct (StringMap.find n (smap temp)) as [ [ i _ ] | ].
    2: right; exact [(l, Result.UndeclaredVariable n)].
    destruct (Dict.find i (env temp)) as [ ty | ].
    2: right; exact [(l, Result.InternalError ("Variable " ++ n ++ " has an ID but no type"))].
    left.
    exists ty.
    exact (Target.EVar (i, ty)).
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
    destruct (StringMap.find n (smap temp)) as [ [ i l' ] | ].
    2: exact (Result.Err [(l, Result.UndeclaredVariable n)]).
    destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Target.type_dec) (i, ty) (nvars temp)) as [Hin|_].
    2: refine (Result.Err [(l, _)]).
    2: destruct temp as [? ? ? ? ? nvars H ? H']; cbn; fold nvars; clear H H' IH; generalize dependent nvars; intros nvars; clear - n i ty nvars.
    2: induction nvars as [|[hdn hdt] tl IH].
    2:  exact (Result.UndeclaredVariable n).
    2: destruct (PeanoNat.Nat.eq_dec i hdn) as [neqhdn|_].
    2:  exact (Result.IncompatibleTypeAssignment hdn hdt ty).
    2: exact IH.
    left.
    exists ((i, existT Target.exp ty e') :: eqs).
    intros a [<-|H]; [exact Hin|exact (IH _ H)].
Defined.

Definition n_assigned_vars (body: list Target.equation) :=
  map Target.equation_dest body.

Scheme Equality for list.

Definition check_assigned_out (l: Result.location) (temp: common_temp) body: Result.t Target.type (incl (n_out temp) (n_assigned_vars body)).
Proof.
  refine (Result.bind (Result.list_map _ _) (fun H => Result.Ok (proj2 (incl_Forall_in_iff _ _) H))).
  intros b.
  destruct (In_dec (prod_dec PeanoNat.Nat.eq_dec Target.type_dec) b (n_assigned_vars body)) as [Hin|Hnin].
  1: exact (Result.Ok Hin).
  exact (Result.Err [(l, Result.NeverAssigned "<information lost>" (fst b) (snd b))]).
Defined.

Definition n_out_is_not_an_input (l: Result.location) (temp: common_temp) :
  Result.t Target.type (Forall (fun b => ~ In (fst b) (map fst (n_in temp))) (n_out temp)) :=
  Result.list_map (fun b => match In_dec PeanoNat.Nat.eq_dec _ _ with
    | left _ => Result.Err [(l, Result.MultipleDeclaration "<information lost>" (fst b) Result.DeclInput Result.DeclOutput)]
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

Lemma Forall_univ : forall [A] (P : A -> Prop), (forall x, P x) -> forall l, Forall P l.
Proof using.
  intros A P HP l; induction l as [|hd tl IH]; constructor; [exact (HP _)|exact IH].
Qed.

Definition build_map (entry: Source.node) :
  { sm & { seed & Result.t Target.type { n_in & { n_out & { n_locals |
    Forall (fun v => forall ty', In (fst v, ty') n_in -> ty' = snd v) n_in /\
    Forall (fun v => forall ty', In (fst v, ty') n_out -> ty' = snd v) n_out /\
    Forall (fun v => forall ty', In (fst v, ty') n_locals -> ty' = snd v) n_locals /\
    Forall (fun v => ~ In (fst v) (map fst n_out)) n_in /\
    Forall (fun v => ~ In (fst v) (map fst n_locals)) n_in /\
    Forall (fun v => ~ In (fst v) (map fst n_locals)) n_out /\
    Forall2 (fun '(x, tx) '(l, (v, tv)) =>
        StringMap.find v sm = Some (x, l) /\
        tx = convert_type tv)
      (n_in ++ n_out ++ n_locals)
      (map (pair Result.DeclInput) entry.(Source.n_in) ++
       map (pair Result.DeclOutput) entry.(Source.n_out) ++
       map (pair Result.DeclLocal) entry.(Source.n_locals)) /\
    (forall n, ~ In (iter n next_ident seed) (map fst (n_in ++ n_out ++ n_locals))) } } } } }.
Proof using.
  destruct entry as [l n nin out loc body]; unfold Source.n_in, Source.n_out, Source.n_locals; clear n body.
  induction nin as [ | [n ty] vars (sm & seed & IH) ].
  2:{
    destruct (StringMap.find n sm) as [ [ i dl ] | ] eqn:eqnsm.
    1: exists sm, seed;
       refine (Result.Err ((l, Result.MultipleDeclaration n i Result.DeclInput dl) :: match IH with Result.Ok _ => [] | Result.Err es => es end)).
    exists (StringMap.add n (seed, Result.DeclInput) sm), (next_ident seed);
      refine (Result.bind IH _);
      intros (IHnin & IHout & IHloc & IHii & IHoo & IHll & IHio & IHil & IHol & IH1 & IH2);
      left; exists ((seed, convert_type ty) :: IHnin), IHout, IHloc; repeat split; try assumption.
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
  }
  refine (match _ : { sm & { seed & Result.t _ { n_out & { n_locals |
                      _ /\ _ /\ _ /\ Forall2 _ (n_out ++ _) (map _ out ++ _) /\ (forall n, ~ In _ (map _ (n_out ++ _)))}}}} with
    | existT _ sm (existT _ seed (Result.Ok (existT _ n_out (exist _ n_locals (conj Hoo (conj Hll (conj Hol (conj H1 H2)))))))) =>
        existT _ sm (existT _ seed (Result.Ok (
          existT _ [] (existT _ n_out (exist _ n_locals
            (conj (Forall_nil _) (conj Hoo (conj Hll (conj (Forall_nil _) (conj (Forall_nil _) (conj Hol (conj H1 H2))))))))))))
    | existT _ sm (existT _ seed (Result.Err e)) => existT _ sm (existT _ seed (Result.Err e)) end).
  induction out as [ | [n ty] vars (sm & seed & IH) ].
  2:{
    destruct (StringMap.find n sm) as [ [ i dl ] | ] eqn:eqnsm.
    1: exists sm, seed;
       refine (Result.Err ((l, Result.MultipleDeclaration n i Result.DeclOutput dl) :: match IH with Result.Ok _ => [] | Result.Err es => es end)).
    exists (StringMap.add n (seed, Result.DeclOutput) sm), (next_ident seed);
      refine (Result.bind IH _);
      intros (IHout & IHloc & IHoo & IHll & IHol & IH1 & IH2);
      left; exists ((seed, convert_type ty) :: IHout), IHloc; repeat split; try assumption.
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
  }
  refine (match _ : { sm & { seed & Result.t _ { n_locals |
                      _ /\ Forall2 _ n_locals (map _ _) /\ (forall n, ~ In _ (map _ n_locals))}}} with
    | existT _ sm (existT _ seed (Result.Ok (exist _ n_locals (conj Hll (conj H1 H2))))) =>
        existT _ sm (existT _ seed (Result.Ok (
          existT _ [] (exist _ n_locals
            (conj (Forall_nil _) (conj Hll (conj (Forall_nil _) (conj H1 H2))))))))
    | existT _ sm (existT _ seed (Result.Err e)) => existT _ sm (existT _ seed (Result.Err e)) end).
  induction loc as [ | [n ty] vars (sm & seed & IH) ].
  2:{
    destruct (StringMap.find n sm) as [ [ i dl ] | ] eqn:eqnsm.
    1: exists sm, seed;
       refine (Result.Err ((l, Result.MultipleDeclaration n i Result.DeclLocal dl) :: match IH with Result.Ok _ => [] | Result.Err es => es end)).
    exists (StringMap.add n (seed, Result.DeclLocal) sm), (next_ident seed);
      refine (Result.bind IH _);
      intros (IHloc & IHll & IH1 & IH2);
      left; exists ((seed, convert_type ty) :: IHloc); repeat split; try assumption.
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
  }
  exists (StringMap.empty _), O; left; exists []; split; [exact (Forall_nil _)|split; [exact (Forall2_nil _)|intros ? f; exact f]].
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
       (Dict.empty Target.type)) <->
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

Definition check_node_prop (entry: Source.node): Result.t Target.type Target.node :=
  let '(existT _ sm (existT _ seed tmp)) := build_map entry in
  do '(existT _ n_in (existT _ n_out (exist _ n_loc
        (conj Hii (conj Hoo (conj Hll (conj Hio (conj Hil (conj Hol (conj Hnvars Hseed)))))))))) <- tmp;
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
      Target.n_locals := n_loc;
      Target.n_body := n_body;
      Target.n_assigned_vars_are_vars := assigned_vars_are_vars;
      Target.n_assigned_out := check_assigned;
      Target.n_out_is_not_an_input := n_out_is_not_an_input;
      Target.n_inputs_equations := n_inputs_equations;
      Target.n_no_einputs_in_other := n_no_einputs_in_other;
      Target.n_seed := seed;
      Target.n_seed_always_fresh := Hseed;
    |}.
