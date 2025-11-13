From Reactive Require Import Base.

From Reactive.Datatypes Require Array Hashtable Result Sorted.
From Reactive.Languages Require Lustre LustreOrdered.

From Stdlib Require Import Sorting Permutation.


Module Source := Lustre.
Module Target := LustreOrdered.


Definition list_eq_dec_binder :=
  List.list_eq_dec Source.binder_dec.

Definition list_eq_dec_equation :=
  List.list_eq_dec Source.equation_dec.

Definition check_eq_node (source: Source.node) (guess: list Source.equation): Permutation source.(Source.n_body) guess -> (
  Permutation source.(Source.n_body) guess /\
  Forall (fun eq => incl (Source.var_of_exp (projT2 (snd eq))) source.(Source.n_vars)) guess).
Proof.
  intros H; refine (conj H _).
  apply Forall_forall; intros eq Heq; apply (Permutation_in _ (Permutation_sym H)) in Heq.
  exact (proj1 (Forall_forall _ _) source.(Source.n_all_vars_exist) _ Heq).
Defined.


Import Result.notations.

Fixpoint find_in {B} (l: list (nat * B)) (x: nat): In x (map fst l) -> B.
Proof using.
  destruct l as [|[hdn hdv] tl]; [intros []|].
  destruct (hdn =? x) eqn:eqxhd.
  1: intros _; exact hdv.
  intros h; refine (find_in B tl x _).
  destruct h as [hdeqx|h]; [|exact h].
  rewrite (proj2 (PeanoNat.Nat.eqb_eq _ _) (hdeqx : hdn = x)) in eqxhd.
  discriminate eqxhd.
Defined.

Lemma find_in_ext {B} (l: list (nat * B)) x H1 H2: find_in l x H1 = find_in l x H2.
Proof using.
  revert H1 H2; induction l as [|[hdn hdv] tl IH]; intros H1 H2.
  1: contradiction H1.
  cbn.
  refine (match hdn =? x as a return forall P : (hdn =? x) = a,
            (if a as b return ((hdn =? x) = b -> _) then _ else _) P _ =
            (if a as b return ((hdn =? x) = b -> _) then _ else _) P _ with true => _ | false => _ end eq_refl).
  1: intros _; exact eq_refl.
  intros ?; exact (IH _ _).
Qed.

Lemma find_in_prop {B} (l: list (nat * B)) x y H: NoDup (map fst l) -> In (x, y) l -> find_in l x H = y.
Proof using.
  induction l as [|[hdn hdv] tl IH].
  1: contradiction H.
  intros Hd Hi.
  cbn; refine (match hdn =? x as a return forall P : (hdn =? x) = a,
                 (if a as b return ((hdn =? x) = b -> _) then _ else _) P _ = y with true => _ | false => _ end eq_refl).
  1: intros h; destruct Hi as [[=_ eqhd]|f]; [exact eqhd|].
  1: apply PeanoNat.Nat.eqb_eq in h; subst hdn.
  1: apply NoDup_cons_iff, proj1 in Hd; contradiction (Hd (in_map fst _ _ f)).
  intros hdnex.
  refine (IH _ (proj2 (proj1 (NoDup_cons_iff _ _) Hd)) _).
  destruct Hi as [[=hdeqx _]|Hi]; [|exact Hi].
  apply PeanoNat.Nat.eqb_eq in hdeqx; rewrite hdeqx in hdnex; discriminate hdnex.
Qed.

Lemma find_in_wd {B} (l : list (nat * B)) x H: In (x, find_in l x H) l.
Proof using.
  induction l as [|[hdn hdv] l IH]; [contradiction H|].
  cbn in H.
  refine (match hdn =? x as a return forall P : (hdn =? x) = a,
            In (_, (if a as b return ((hdn =? x) = b -> _) then _ else _) P _) _ with true => _ | false => _ end eq_refl).
  1: intros h; apply PeanoNat.Nat.eqb_eq in h; subst x; left; exact eq_refl.
  fold @find_in.
  intros P.
  destruct H as [H|H].
  1: exfalso; apply PeanoNat.Nat.eqb_neq in P; exact (P H).
  right; exact (IH _).
Qed.

Fixpoint reorder_list (source: list Source.equation) (ord: list nat):
  incl ord (map fst source) -> list Source.equation.
Proof using.
  destruct ord as [|i ord].
  1: intros _; exact [].
  intros h; refine ((i, find_in source i (h _ (or_introl eq_refl))) :: reorder_list source ord (fun _ h2 => h _ (or_intror h2))).
Defined.

Lemma reorder_list_ext l1 l2 Hl1 Hl2: reorder_list l1 l2 Hl1 = reorder_list l1 l2 Hl2.
Proof using.
  revert l1 Hl1 Hl2; induction l2 as [|n l2 IH]; intros l1 Hl1 Hl2.
  1: exact eq_refl.
  exact (f_equal2 (fun v1 v2 => (n, v1) :: v2) (find_in_ext _ _ _ _) (IH _ _ _)).
Qed.

Lemma reorder_list_prop' ref subref idxs Hl: NoDup (map fst ref) -> incl subref ref ->
  Permutation (map fst subref) idxs -> Permutation subref (reorder_list ref idxs Hl).
Proof using.
  rename ref into l0, subref into l1, idxs into l2; intros Hd.
  revert l1; induction l2 as [|n l2 IH]; intros l1 Hl0 H.
  1: apply Permutation_sym, Permutation_nil in H; destruct l1; [exact (perm_nil _)|discriminate H].
  apply Permutation_vs_cons_inv in H as tmp; destruct tmp as [fstl11 [fstl12 eqmap]].
  apply map_eq_app in eqmap; destruct eqmap as [l11 [l12 [-> [<- eq3]]]].
  destruct l12 as [|[i tye] l12]; [discriminate eq3|injection eq3 as <- <-].
  cbn.
  rewrite (find_in_prop _ _ _ _ Hd (Hl0 _ (in_or_app _ (_ :: _) _ (or_intror (or_introl eq_refl))))).
  refine (Permutation_elt _ _ [] _ _ (IH _ _ _ _)).
  1: intros j Hj; apply in_app_or in Hj; apply Hl0, in_or_app; destruct Hj as [Hj|Hj]; [left|right; right]; exact Hj.
  rewrite map_app in H |- *; cbn in H.
  exact (Permutation_app_inv _ _ [] _ _ H).
Qed.
Lemma reorder_list_prop l1 l2 Hl: NoDup (map fst l1) -> Permutation (map fst l1) l2 -> Permutation l1 (reorder_list l1 l2 Hl).
Proof using.
  intros Hd HP.
  exact (reorder_list_prop' _ _ _ _ Hd (fun _ h => h) HP).
Qed.

Lemma in_reorder_list_iff x y l1 l2 H: NoDup (map fst l1) -> In (x, y) (reorder_list l1 l2 H) <-> In (x, y) l1 /\ In x l2.
Proof using.
  intros Hd; split.
  - intros Hxy; induction l2 as [|hd tl IH].
    1: contradiction Hxy.
    destruct Hxy as [[=<- <-]|Hxy].
    2: specialize (IH (fun _ h => H _ (or_intror h)) Hxy); exact (conj (proj1 IH) (or_intror (proj2 IH))).
    clear IH; refine (conj (find_in_wd _ _ _) (or_introl eq_refl)).
  - intros [Hxy Hx]; induction l2 as [|hd tl IH].
    1: exact Hx.
    destruct Hx as [[=<-]|Hx].
    1: left; exact (f_equal (pair _) (find_in_prop _ _ _ _ Hd Hxy)).
    right; exact (IH (fun _ h => H _ (or_intror h)) Hx).
Qed.

Definition check_order (source: Source.node) (guess: list Source.equation) Hperm Hord: Target.node_ordered :=
  {|
    Target.node_ordered_is_node := {|
      Lustre.n_loc := Lustre.n_loc source;
      Lustre.n_name := Lustre.n_name source;
      Lustre.n_in := Lustre.n_in source;
      Lustre.n_out := Lustre.n_out source;
      Lustre.n_locals := Lustre.n_locals source;
      Lustre.n_body := guess;
      Lustre.n_vars_all_assigned := Permutation_trans (Permutation_map _ (Permutation_sym Hperm)) (Lustre.n_vars_all_assigned source);
      Lustre.n_vars_unique := Lustre.n_vars_unique source;
      Lustre.n_all_vars_exist := proj2 (Forall_forall _ _) (fun eq Heq =>
        proj1 (Forall_forall _ _) source.(Source.n_all_vars_exist) eq (Permutation_in _ (Permutation_sym Hperm) Heq));
    |};
    Target.ordered := Hord;
  |}.

Definition graph := Array.t (list ident).
Definition vertex := nat.

Fixpoint List_mem : ident -> list ident -> bool.
Proof using.
  intros x l.
  destruct l as [|hd tl].
  1: exact false.
  destruct (PeanoNat.Nat.eq_dec x hd); [exact true|exact (List_mem x tl)].
Defined.

Lemma mem_wd : forall x l, List_mem x l = true <-> In x l.
Proof using.
  intros x l; split; induction l as [|hd tl IH]; cbn.
  1: discriminate 1.
  2: intros f; contradiction f.
  1: intros h; destruct (PeanoNat.Nat.eq_dec x hd) as [Heq|]; [left; exact (eq_sym Heq)|right; exact (IH h)].
  destruct (PeanoNat.Nat.eq_dec x hd) as [_|f]; [intros _; exact eq_refl|].
  intros [H|H]; [contradiction (f (eq_sym H))|exact (IH H)].
Qed.

Definition remove_dup : list vertex -> list vertex.
Proof using.
  fix inner 1.
  intros [|hd tl].
  1: exact [].
  pose (tl' := inner tl).
  destruct (List_mem hd tl') eqn:tmp.
  1: exact tl'.
  exact (hd :: tl').
Defined.

Lemma remove_dup_wd : forall l, incl l (remove_dup l) /\ incl (remove_dup l) l /\ NoDup (remove_dup l).
Proof using.
  intros l; split; [|split]; induction l as [|hd tl IH].
  1,3: intros ? [].
  3: exact (NoDup_nil _).
  1: intros x [<-|H]; cbn.
  3: intros x H; cbn in H |- *.
  4: cbn.
  all: destruct (List_mem hd (remove_dup tl)) as [|] eqn:eqmem.
  6: destruct H as [<-|H].
  1: apply mem_wd in eqmem; exact eqmem.
  1,5: left; exact eq_refl.
  1: exact (IH _ H).
  1,2,3: right; exact (IH _ H).
  1: exact IH.
  constructor; [intros f|exact IH].
  apply mem_wd in f; congruence.
Qed.

Definition node_to_graph_fun0 rt :=
  forall (vmap : Hashtable.t ident vertex) (imap : Hashtable.t vertex ident) (nxt : nat), rt vmap imap nxt.
Definition node_to_graph_fun rt := node_to_graph_fun0 (fun _ _ _ => rt).

Definition node_to_graph_consistency (v0 : Hashtable.t ident vertex) (i0 : Hashtable.t vertex ident) (n0 : nat) v1 i1 n1 :=
  (exists Hvar0var : forall x, Hashtable.InMap x v0 -> Hashtable.InMap x v1,
  (forall x H, Hashtable.find v0 x H = Hashtable.find v1 x (Hvar0var _ H))) /\
  (exists Hidx0idx : forall x, Hashtable.InMap x i0 -> Hashtable.InMap x i1,
  (forall x H, Hashtable.find i0 x H = Hashtable.find i1 x (Hidx0idx _ H))) /\
  n0 <= n1.
Definition node_to_graph_assumptions (vmap : Hashtable.t ident vertex) (imap : Hashtable.t vertex ident) (n : nat) :=
  (forall x H, exists H', Hashtable.find imap (Hashtable.find vmap x H) H' = x) /\
  (forall x H, exists H', Hashtable.find vmap (Hashtable.find imap x H) H' = x) /\
  (forall x1 x2 H1 H2, Hashtable.find imap x1 H1 = Hashtable.find imap x2 H2 -> x1 = x2) /\
  (forall x H, Hashtable.find vmap x H < n) /\
  (forall j, j < n -> exists x H, Hashtable.find vmap x H = j).
Definition node_to_graph_assumption_n (Vars : list ident) (vmap : Hashtable.t ident vertex) n :=
  (n = List.length (fst (partition (fun i => match Hashtable.find_opt vmap i with None => false | Some _ => true end) (remove_dup Vars)))) /\
  (forall i, Hashtable.InMap i vmap -> In i Vars).

Definition node_to_graph_fun'0 rt := node_to_graph_fun0 (fun v i n => node_to_graph_assumptions v i n -> rt v i n).
Definition node_to_graph_fun' rt := node_to_graph_fun'0 (fun _ _ _ => rt).

Definition node_to_graph_ret rt :=
  @sig (Hashtable.t ident vertex * Hashtable.t vertex ident * nat * rt)%type (fun r =>
    let '(v1, i1, n1, _) := r in node_to_graph_assumptions v1 i1 n1).
Definition node_to_graph_ret' v0 i0 n0 rt :=
  @sig (Hashtable.t ident vertex * Hashtable.t vertex ident * nat * rt)%type (fun r =>
    let '(v1, i1, n1, _) := r in node_to_graph_consistency v0 i0 n0 v1 i1 n1 /\ node_to_graph_assumptions v1 i1 n1).

Definition node_to_graph_consistent_prop {A} P : Prop :=
  forall v0 i0 n0 v1 i1 n1, node_to_graph_consistency v0 i0 n0 v1 i1 n1 -> forall x : A, P v0 i0 n0 x -> P v1 i1 n1 x.

Lemma node_to_graph_consistency_refl : forall {v i n}, node_to_graph_consistency v i n v i n.
Proof using.
  intros v i n; repeat split.
  3: exact (le_n _).
  all: exists (fun _ h => h); exact (fun _ _ => eq_refl).
Qed.
Lemma node_to_graph_consistency_trans : forall {v1 i1 n1 v2 i2 n2 v3 i3 n3},
  node_to_graph_consistency v1 i1 n1 v2 i2 n2 ->
  node_to_graph_consistency v2 i2 n2 v3 i3 n3 ->
  node_to_graph_consistency v1 i1 n1 v3 i3 n3.
Proof using.
  intros v1 i1 n1 v2 i2 n2 v3 i3 n3 ([H121 H122] & [H123 H124] & H125) ([H231 H232] & [H233 H234] & H235).
  split; [exists (fun _ h => H231 _ (H121 _ h))|split; [exists (fun _ h => H233 _ (H123 _ h))|exact (PeanoNat.Nat.le_trans _ _ _ H125 H235)]].
  1: exact (fun _ h => eq_trans (H122 _ h) (H232 _ (H121 _ h))).
  exact (fun _ h => eq_trans (H124 _ h) (H234 _ (H123 _ h))).
Qed.

Fixpoint List_filter_map_fold : forall {A B},
  node_to_graph_fun'0 (fun v0 i0 n0 =>
    forall l : list A,
    (node_to_graph_fun'0 (fun v0 i0 n0 => forall x : A, In x l -> option (node_to_graph_ret' v0 i0 n0 B))) ->
    node_to_graph_ret' v0 i0 n0 (list B)).
Proof using.
  intros A B i1 i2 i3 Hi l f.
  destruct l as [|hd tl].
  1: exists (i1, i2, i3, []); exact (conj node_to_graph_consistency_refl Hi).
  pose (f' := fun i1 i2 i3 Hi x (Hx : In _ _) => f i1 i2 i3 Hi x (or_intror Hx)).
  destruct (f i1 i2 i3 Hi hd (or_introl eq_refl)) as [[[[[n1 n2] n3] fhd] [Hcin Hn]]|].
  2: exact (List_filter_map_fold _ _ i1 i2 i3 Hi tl f').
  destruct (List_filter_map_fold _ _ n1 n2 n3 Hn tl f') as [[[[f1 f2] f3] ftl] [Hcnf Hf]].
  exists (f1, f2, f3, fhd :: ftl); exact (conj (node_to_graph_consistency_trans Hcin Hcnf) Hf).
Defined.

Lemma List_filter_map_fold_prop : forall Vars {A B} PB,
  (forall x, node_to_graph_consistent_prop (PB x)) ->
  forall v0 i0 n0 H0, node_to_graph_assumption_n Vars v0 n0 ->
  forall (l : list A) (f : node_to_graph_fun'0 (fun v0 i0 n0 => forall x : A, In x l -> option (node_to_graph_ret' v0 i0 n0 B))),
  (forall v0 i0 n0 H0, node_to_graph_assumption_n Vars v0 n0 ->
    forall x Hx v1 i1 n1 y H1, f v0 i0 n0 H0 x Hx = Some (exist _ (v1, i1, n1, y) H1) ->
    node_to_graph_assumption_n Vars v1 n1 /\
    PB x v1 i1 n1 y
  ) ->
  let '(exist _ (v1, i1, n1, ys) H1) := List_filter_map_fold v0 i0 n0 H0 l f in
  node_to_graph_assumption_n Vars v1 n1 /\
  Forall (fun y => exists x, In x l /\ PB x v1 i1 n1 y) ys.
Proof using.
  intros Vars A B PB HP i1 i2 i3 Hi1 Hi2 l f Hfun.
  revert i1 i2 i3 Hi1 Hi2; induction l as [|hd tl IH]; intros i1 i2 i3 Hi1 Hi2.
  1: unfold List_filter_map_fold; split; [exact Hi2|exact (Forall_nil _)].
  pose (f' := fun i1 i2 i3 Hi x (Hx : In _ _) => f i1 i2 i3 Hi x (or_intror Hx)); cbn; fold f'.
  specialize (IH f' (fun _ _ _ h1 h2 _ hx => Hfun _ _ _ h1 h2 _ (or_intror hx))).
  destruct (f i1 i2 i3 Hi1 hd (or_introl eq_refl)) as [[[[[n1 n2] n3] fhd] [Hcin Hn]]|] eqn:eqfhd.
  2:{
    specialize (IH i1 i2 i3 Hi1 Hi2).
    destruct (List_filter_map_fold i1 i2 i3 Hi1 tl f') as [[[[fv fi] fn] ys] [Hcif Hf]].
    destruct IH as (Hn1 & Hn2); split; [exact Hn1|refine (Forall_impl _ _ Hn2)]; clear.
    intros y [x [Hx Hy]]; exists x; split; [right|]; assumption.
  }
  specialize (Hfun i1 i2 i3 Hi1 Hi2 hd (or_introl eq_refl) _ _ _ _ _ eqfhd) as Hhd; destruct Hhd as (Hnn & HPhd).
  specialize (IH n1 n2 n3 Hn Hnn).
  destruct (List_filter_map_fold n1 n2 n3 Hn tl f') as [[[[fv fi] fn] ys] [Hcnf Hf]].
  destruct IH as (Hf1 & Hf2).
  split; [exact Hf1|].
  constructor; [refine (ex_intro _ _ (conj (or_introl eq_refl) _))|refine (Forall_impl _ _ Hf2); clear].
  1: exact (HP _ _ _ _ _ _ _ Hcnf _ HPhd).
  intros y [x [Hx Hy]]; exists x; split; [right|]; assumption.
Qed.

Lemma In_List_filter_map_fold : forall Vars {A B} i1 i2 i3 Hi, node_to_graph_assumption_n Vars i1 i3 ->
  forall l (f : node_to_graph_fun'0 _),
  (forall v0 i0 n0 H0, node_to_graph_assumption_n Vars v0 n0 ->
    forall x Hx v1 i1 n1 y H1, f v0 i0 n0 H0 x Hx = Some (exist _ (v1, i1, n1, y) H1) ->
    node_to_graph_assumption_n Vars v1 n1) ->
  forall y,
  let img := @List_filter_map_fold A B i1 i2 i3 Hi l f in
  In y (snd (proj1_sig img)) ->
  exists x Hx im1 im2 im3 Hm im' H',
    f im1 im2 im3 Hm x Hx = Some (exist _ (im', y) H') /\
    node_to_graph_consistency i1 i2 i3 im1 im2 im3 /\
    node_to_graph_consistency (fst (fst im')) (snd (fst im')) (snd im')
      (fst (fst (fst (proj1_sig img)))) (snd (fst (fst (proj1_sig img)))) (snd (fst (proj1_sig img))).
Proof using.
  intros Vars A B i1 i2 i3 Hi1 Hi2 l f Hf y img Hy; subst img; cbn in *.
  revert f Hf i1 i2 i3 Hi1 Hi2 Hy;
    induction l as [|hd tl IH]; intros f Hf i1 i2 i3 Hi1 Hi2 Hy; [contradiction Hy|cbn in Hy].
  cbn.
  destruct (f i1 i2 i3 Hi1 hd (or_introl eq_refl)) as [[[[[ix1 ix2] ix3] fx] [Hcix Hx]]|] eqn:eqfx.
  2:{
    match type of Hy with In _ (snd (proj1_sig (List_filter_map_fold _ _ _ _ _ ?f))) =>
      specialize (IH f (fun _ _ _ _ h2 _ h => Hf _ _ _ _ h2 _ (or_intror h)) i1 i2 i3 Hi1 Hi2 Hy) end.
    destruct IH as (x & Hx & H).
    exists x, (or_intror Hx); exact H.
  }
  specialize (Hf _ _ _ _ Hi2 _ _ _ _ _ _ _ eqfx) as Hnx.
  match type of Hy with In _ (snd (proj1_sig (let (_, _) := List_filter_map_fold _ _ _ _ _ ?f in _))) =>
    specialize (IH f (fun _ _ _ _ h2 _ h => Hf _ _ _ _ h2 _ (or_intror h)) ix1 ix2 ix3 Hx Hnx) end.
  match type of Hy with In _ (snd (proj1_sig (let (_, _) := ?xy in _))) =>
    destruct xy as [[[[ie1 ie2] ie3] fm] [Hcxe He]] eqn:eqfm end.
  cbn in *.
  destruct Hy as [<-|Hy].
  1: exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (ex_intro _ _
           (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (ex_intro _ _
           (conj eqfx (conj node_to_graph_consistency_refl Hcxe)))))))))).
  clear eqfm eqfx.
  destruct (IH Hy) as (x & Hx' & im1 & im2 & im3 & Hm & im' & H' & eqfx & Hc1 & Hc2);
    exists x, (or_intror Hx'), im1, im2, im3, Hm, im', H'; split; [exact eqfx|split; [|exact Hc2]].
  exact (node_to_graph_consistency_trans Hcix Hc1).
Qed.

Lemma fwd_List_filter_map_fold : forall Vars {A B} i1 i2 i3 Hi, node_to_graph_assumption_n Vars i1 i3 ->
  forall l (f : node_to_graph_fun'0 _),
  (forall v0 i0 n0 H0, node_to_graph_assumption_n Vars v0 n0 ->
    forall x Hx v1 i1 n1 y H1, f v0 i0 n0 H0 x Hx = Some (exist _ (v1, i1, n1, y) H1) ->
    node_to_graph_assumption_n Vars v1 n1) ->
  forall x Hx (P : _ -> _ -> _ -> Prop),
  let img := @List_filter_map_fold A B i1 i2 i3 Hi l f in
  (forall im1 im2 im3 Hm, node_to_graph_assumption_n Vars im1 im3 ->
    node_to_graph_consistency i1 i2 i3 im1 im2 im3 ->
    f im1 im2 im3 Hm x Hx = None ->
    forall if1 if2 if3,
      node_to_graph_assumptions if1 if2 if3 -> node_to_graph_assumption_n Vars if1 if3 ->
      node_to_graph_consistency im1 im2 im3 if1 if2 if3 ->
      P if1 if2 if3) ->
  (forall im1 im2 im3 Hm im' y H', node_to_graph_assumption_n Vars im1 im3 ->
    node_to_graph_consistency i1 i2 i3 im1 im2 im3 ->
    f im1 im2 im3 Hm x Hx = Some (exist _ (im', y) H') ->
    In y (snd (proj1_sig img)) ->
    forall if1 if2 if3,
      node_to_graph_assumptions if1 if2 if3 -> node_to_graph_assumption_n Vars if1 if3 ->
      node_to_graph_consistency (fst (fst im')) (snd (fst im')) (snd im') if1 if2 if3 ->
      P if1 if2 if3) ->
  P (fst (fst (fst (proj1_sig img)))) (snd (fst (fst (proj1_sig img)))) (snd (fst (proj1_sig img))).
Proof using.
  intros Vars A B i1 i2 i3 Hi1 Hi2 l f Hfun x Hx P.
  revert i1 i2 i3 Hi1 Hi2 f Hfun x Hx; induction l as [|hd tl IH]; intros i1 i2 i3 Hi1 Hi2 f Hfun x Hx img Hnone Hsome.
  1: contradiction Hx.
  cbn in img.
  destruct Hx as [->|Hx].
  - clear IH.
    destruct (f i1 i2 i3 Hi1 x (or_introl eq_refl)) as [[[[[im1 im2] im3] y] [Hcim Hm]]|] eqn:eqfx.
    + subst img; match goal with |- context[let (_, _) := ?fm in _] =>
        destruct fm as [[[[if1 if2] if3] y0] [Hcmf Hf]] eqn:eqfm; cbn end.
      specialize (Hfun _ _ _ _ Hi2 _ (or_introl eq_refl) _ _ _ _ _ eqfx) as Hnm.
      refine (Hsome _ _ _ _ _ _ _ Hi2 node_to_graph_consistency_refl eqfx (or_introl eq_refl) _ _ _ Hf _ Hcmf); cbn.
      specialize (eq_ind (List_filter_map_fold _ _ _ _ _ _) (fun v => let 'exist _ (_, _, _, _) _ := v in _)
        (List_filter_map_fold_prop Vars (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ => I)
          _ _ _ _ Hnm
          _ _ (fun _ _ _ h1 h2 _ hx _ _ _ _ _ heq => conj (Hfun _ _ _ h1 h2 _ (or_intror hx) _ _ _ _ _ heq) I))
        (exist _ (_, _, _, _) _) eqfm) as [Haf _]; cbn in Haf.
      exact Haf.
    + subst img; match goal with |- context[proj1_sig ?fm] =>
        destruct fm as [[[[if1 if2] if3] y0] [Hcmf Hf]] eqn:eqfm; cbn end.
      specialize (eq_ind (List_filter_map_fold _ _ _ _ _ _) (fun v => let 'exist _ (_, _, _, _) _ := v in _)
        (List_filter_map_fold_prop Vars (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ => I)
          _ _ _ _ Hi2
          _ _ (fun _ _ _ h1 h2 _ hx _ _ _ _ _ heq => conj (Hfun _ _ _ h1 h2 _ (or_intror hx) _ _ _ _ _ heq) I))
        (exist _ (_, _, _, _) _) eqfm) as [Haf _]; cbn in Haf.
      exact (Hnone _ _ _ Hi1 Hi2 node_to_graph_consistency_refl eqfx _ _ _ Hf Haf Hcmf).
  - destruct (f i1 i2 i3 Hi1 hd (or_introl eq_refl)) as [[[[[im1 im2] im3] y] [Hcim Hm]]|] eqn:eqfx.
    + specialize (Hfun _ _ _ _ Hi2 _ (or_introl eq_refl) _ _ _ _ _ eqfx) as Hnm.
      specialize (IH _ _ _ Hm Hnm (fun i1 i2 i3 Hi x hx => f i1 i2 i3 Hi x (or_intror hx)) (fun _ _ _ _ h2 _ hx => Hfun _ _ _ _ h2 _ (or_intror hx)) _ Hx).
      destruct (List_filter_map_fold im1 im2 im3 Hm tl
        (fun i1 i2 i3 Hi x hx => f i1 i2 i3 Hi x (or_intror hx)))
        as [[[[if1 if2] if3] lf] [Hf Hcmf]] eqn:eqtl.
      unfold img; cbn; cbn in IH.
      refine (IH _ _).
      * intros ? ? ? Ha11 Ha12 Hcm1.
        exact (Hnone _ _ _ Ha11 Ha12 (node_to_graph_consistency_trans Hcim Hcm1)).
      * intros ? ? ? ? ? ? Ha11 Ha12 Hc1q H1 H2.
        exact (Hsome _ _ _ _ _ _ _ Ha12 (node_to_graph_consistency_trans Hcim Hc1q) H1 (or_intror H2)).
    + exact (IH _ _ _ Hi1 Hi2 _ (fun _ _ _ _ h2 _ hx => Hfun _ _ _ _ h2 _ (or_intror hx)) _ Hx Hnone Hsome).
Qed.

Definition var_idx : node_to_graph_fun'0 (fun v0 i0 n0 => ident -> node_to_graph_ret' v0 i0 n0 vertex).
Proof using.
  intros var_table index_table nxt H n.
  destruct (Hashtable.find_opt var_table n) as [value|] eqn:eqfind.
  1: exists (var_table, index_table, nxt, value); split; [exact node_to_graph_consistency_refl|assumption].
  unshelve refine (exist _ (Hashtable.add var_table n nxt _, Hashtable.add index_table nxt n _, S nxt, nxt)
    (conj (conj _ (conj _ _)) (conj _ (conj _ (conj _ (conj _ _)))))).
  - apply Hashtable.find_opt_None; exact eqfind.
  - intros f.
    destruct H as (H1 & H2 & H3 & H4 & H5).
    destruct (H2 _ f) as [f2 f3].
    specialize (H4 _ f2).
    rewrite f3 in H4.
    exact (PeanoNat.Nat.lt_irrefl _ H4).
  - exists (fun i Hi => Hashtable.In_add_pre _ Hi).
    clear; intros i Hi.
    exact (eq_sym (Hashtable.find_ne _ _ _)).
  - exists (fun v Hv => Hashtable.In_add_pre _ Hv).
    clear; intros v Hv.
    exact (eq_sym (Hashtable.find_ne _ _ _)).
  - exact (le_S _ _ (le_n _)).
  - intros i Hi.
    apply Hashtable.In_add_inv in Hi as tmp; destruct tmp as [<-|Hin].
    1: rewrite Hashtable.find_add; exists (Hashtable.In_add_same _ _ _ _); rewrite !Hashtable.find_add; exact eq_refl.
    rewrite (Hashtable.find_ne _ _ Hin).
    destruct H as (H & ? & ? & ?).
    specialize (H _ Hin) as tmp; destruct tmp as [Hin2 Heq].
    exists (Hashtable.In_add_pre _ Hin2).
    rewrite (Hashtable.find_ne _ _ Hin2).
    exact Heq.
  - intros v Hv.
    apply Hashtable.In_add_inv in Hv as tmp; destruct tmp as [<-|Hin].
    1: rewrite Hashtable.find_add; exists (Hashtable.In_add_same _ _ _ _); rewrite !Hashtable.find_add; exact eq_refl.
    rewrite (Hashtable.find_ne _ _ Hin).
    destruct H as (? & H & ? & ?).
    specialize (H _ Hin) as tmp; destruct tmp as [Hin2 Heq].
    exists (Hashtable.In_add_pre _ Hin2).
    rewrite (Hashtable.find_ne _ _ Hin2).
    exact Heq.
  - intros v1 v2 Hv1 Hv2 Hv.
    destruct H as (_ & h2 & H & h4 & _).
    apply Hashtable.In_add_inv in Hv1 as tmp; destruct tmp as [<-|Hin1].
    1-2: apply Hashtable.In_add_inv in Hv2 as tmp; destruct tmp as [<-|Hin2].
    1: exact eq_refl.
    1: rename Hin2 into Hin.
    2: rename Hin1 into Hin.
    1,2: rewrite Hashtable.find_add, (Hashtable.find_ne _ _ Hin) in Hv; (rewrite Hv in eqfind || rewrite <-Hv in eqfind); clear - h2 eqfind Hin.
    1,2:  specialize (h2 _ Hin) as [Hin' _]; apply Hashtable.find_opt_None in eqfind; contradiction (eqfind Hin').
    rewrite (Hashtable.find_ne _ _ Hin1), (Hashtable.find_ne _ _ Hin2) in Hv.
    exact (H _ _ _ _ Hv).
  - intros i Hi.
    apply Hashtable.In_add_inv in Hi as tmp; destruct tmp as [<-|Hin].
    1: rewrite Hashtable.find_add; exact (le_n _).
    rewrite (Hashtable.find_ne _ _ Hin).
    destruct H as (? & ? & ? & H & ?).
    exact (le_S _ _ (H _ Hin)).
  - intros k Hk.
    inversion Hk; subst.
    1: exists _, (Hashtable.In_add_same _ _ _ _); rewrite !Hashtable.find_add; exact eq_refl.
    destruct H as (? & ? & ? & ? & H).
    specialize (H _ H1) as tmp; destruct tmp as [x [Hx Hxk]].
    exists x, (Hashtable.In_add_pre _ Hx).
    rewrite (Hashtable.find_ne _ _ Hx).
    exact Hxk.
Defined.

Lemma partition_ext : forall {A} (l : list A) P Q, (forall x, In x l -> P x = Q x) -> partition P l = partition Q l.
Proof using.
  intros A l P Q H; induction l as [|hd tl IH].
  1: exact eq_refl.
  cbn.
  exact (f_equal2 (fun (v1 : bool) (v2 : list A * list A) => let (g, d) := v2 in if v1 then _ else _)
           (H _ (or_introl eq_refl)) (IH (fun x Hx => H x (or_intror Hx)))).
Qed.

Lemma var_idx_prop Vars :
  forall v0 i0 n0 H0, node_to_graph_assumption_n Vars v0 n0 ->
  forall i, In i Vars ->
  let 'exist _ (v1, i1, n1, v) H1 := var_idx v0 i0 n0 H0 i in
  node_to_graph_assumption_n Vars v1 n1 /\
  Hashtable.find_opt v1 i = Some v.
Proof using.
  intros v0 i0 n0 H1 H2 i Hi.
  unfold var_idx.
  pose (ov := Hashtable.find_opt v0 i).
  remember (eq_refl (Hashtable.find_opt v0 i)) as Heq eqn:eqHeq.
  pose (tmp := Heq : Hashtable.find_opt v0 i = ov).
  refine (_ : let 'exist _ (_, _, _, _) _ := match ov as o return Hashtable.find_opt v0 i = o -> _ with Some y => _ | None => _ end tmp in _).
  generalize dependent tmp; generalize dependent ov; clear Heq eqHeq.
  intros [v|].
  1: intros h; split; assumption.
  intros Hfind.
  split; [destruct H1 as (H11 & H12 & H13 & H14); split|].
  - unfold node_to_graph_assumption_n in H2 |- *; destruct H2 as [H2 _].
    pose (y := n0); fold vertex in y; change (Hashtable.add v0 i n0) with (Hashtable.add v0 i y).
    generalize dependent y; intros y.
    match goal with |- context[Hashtable.add _ _ _ ?H0] => remember H0 as Hnin eqn:tmp; clear tmp end.
    rewrite H2.
    clear - Hi Hfind; rename v0 into vmap, i into i0, Hfind into Hi0eq, Hi into Hi0in'.
    pose (P (vmap : Hashtable.t ident vertex) := fun i => match Hashtable.find_opt vmap i with Some _ => true | None => false end).
    fold (P vmap) (P (Hashtable.add vmap i0 y Hnin)).
    specialize (remove_dup_wd Vars) as [Hi0in [_ Hndup]].
    specialize (Hi0in _ Hi0in').
    remember (remove_dup Vars) as vs eqn:tmp; unfold vertex in vs; fold ident in vs; clear Vars Hi0in' tmp.
    induction vs as [|hd tl IH]; [contradiction Hi0in|].
    apply NoDup_cons_iff in Hndup; destruct Hndup as [Hhdnin Hndup].
    cbn in Hi0in |- *.
    destruct Hi0in as [->|Hi0in].
    + clear IH Hndup.
      assert (H : forall x, In x tl -> P vmap x = P (Hashtable.add vmap i0 y Hnin) x).
      1:{
        clear - Hhdnin; intros x Hx; unfold P.
        assert (xnei0 := fun (xeqi0 : x = i0) => eq_ind _ (fun v => ~ In v _) Hhdnin _ (eq_sym xeqi0) Hx);
          clear Hhdnin; fold (not (x = i0)) in xnei0.
        destruct (Hashtable.find_opt vmap x) as [?|] eqn:eq1.
        1: apply Hashtable.find_opt_Some_In in eq1.
        1: rewrite (Hashtable.find_opt_In _ _ (Hashtable.In_add_pre _ eq1)); exact eq_refl.
        apply Hashtable.find_opt_None in eq1.
        destruct (Hashtable.find_opt (Hashtable.add vmap i0 y Hnin) x) as [?|] eqn:eq2.
        2: exact eq_refl.
        apply Hashtable.find_opt_Some_In, Hashtable.In_add_inv in eq2.
        tauto.
      }
      assert (Hl : P vmap i0 = false).
      1:{ unfold P. rewrite Hi0eq. exact eq_refl. }
      assert (Hr : P (Hashtable.add vmap i0 y Hnin) i0 = true).
      1:{ unfold P. rewrite (Hashtable.find_opt_In _ _ (Hashtable.In_add_same _ _ _ _)). exact eq_refl. }
      rewrite Hl, Hr.
      assert (eqpart := partition_ext tl (P vmap) (P (Hashtable.add vmap i0 y Hnin)) H).
      refine (eq_trans _ (f_equal (fun (p: list ident * list ident) => List.length (fst (let (g, d) := p in _))) eqpart)).
      destruct (partition (P vmap) tl); exact eq_refl.
    + specialize (IH Hi0in Hndup).
      assert (Hhd : P vmap hd = P (Hashtable.add vmap i0 y Hnin) hd).
      1:{
        assert (hdnei0 := fun (hdeqi0 : hd = i0) => eq_ind _ (fun v => ~ In v _) Hhdnin _ hdeqi0 Hi0in);
          clear Hhdnin; fold (not (hd = i0)) in hdnei0.
        clear - hdnei0; subst P; cbn.
        destruct (Hashtable.find_opt vmap hd) as [?|] eqn:eq1.
        1: apply Hashtable.find_opt_Some_In in eq1.
        1: rewrite (Hashtable.find_opt_In _ _ (Hashtable.In_add_pre _ eq1)); exact eq_refl.
        apply Hashtable.find_opt_None in eq1.
        destruct (Hashtable.find_opt (Hashtable.add vmap i0 y Hnin) hd) as [?|] eqn:eq2.
        2: exact eq_refl.
        apply Hashtable.find_opt_Some_In, Hashtable.In_add_inv in eq2.
        tauto.
      }
      clear - IH Hhd.
      destruct (partition (P vmap) tl).
      destruct (partition (P (Hashtable.add vmap i0 y Hnin)) tl).
      cbn in IH |- *; rewrite <-Hhd; clear - IH.
      destruct (P vmap hd); [exact (f_equal S IH)|exact IH].
  - intros j Hj.
    unfold node_to_graph_assumption_n in H2 |- *; destruct H2 as [_ H2].
    apply Hashtable.In_add_inv in Hj; destruct Hj as [->|Hj]; [exact Hi|exact (H2 _ Hj)].
  - rewrite (Hashtable.find_opt_In _ _ (Hashtable.In_add_same _ _ _ _)); f_equal.
    exact (Hashtable.find_add _ _).
Qed.

Definition node_to_graph_filtering (excl : list ident) (expvars: list (ident * Source.type)) :
  node_to_graph_fun'0 (fun v0 i0 n0 => forall x : ident * Source.type, In x expvars -> option (node_to_graph_ret' v0 i0 n0 vertex)).
Proof using.
  intros i1 i2 i3 Hi [i ty'] _.
  destruct (List_mem i excl) as [|] eqn:eqm.
  1: exact None.
  exact (Some (var_idx i1 i2 i3 Hi i)).
Defined.

Lemma node_to_graph_filtering_prop (excl : list ident) (expvars: list (ident * Source.type)) Vars :
  incl (map fst expvars) (excl ++ Vars) ->
  forall v0 i0 n0 H1, node_to_graph_assumption_n Vars v0 n0 ->
  forall x Hx,
  match node_to_graph_filtering excl expvars v0 i0 n0 H1 x Hx with
  | None => In (fst x) excl
  | Some (exist _ (v1, i1, n1, v) _) =>
      ~ In (fst x) excl /\ node_to_graph_assumption_n Vars v1 n1 /\
      Hashtable.find_opt i1 v = Some (fst x)
  end.
Proof using.
  intros He.
  intros v0 i0 n0 H1 H2 [i ty'] Hi.
  unfold node_to_graph_filtering.
  destruct (List_mem i excl) as [|] eqn:eqm.
  1: exact (proj1 (mem_wd _ _) eqm).
  specialize (He _ (in_map _ _ _ Hi)) as HiineV; cbn in HiineV.
  apply in_app_iff in HiineV; destruct HiineV as [f|Hi2].
  1: apply mem_wd in f; rewrite f in eqm; discriminate eqm.
  specialize (var_idx_prop Vars v0 i0 n0 H1 H2 i Hi2) as Hcall.
  destruct (var_idx v0 i0 n0 H1 i) as [[[[v1 i1] n1] v] [_ (H & _ & _)]].
  split.
  1: intros f; apply mem_wd in f; cbn in f; rewrite eqm in f; discriminate f.
  split; [tauto|cbn].
  destruct Hcall as [_ Heq]; clear - H Heq.
  apply Hashtable.find_opt_Some in Heq; destruct Heq as [Hin Heq].
  specialize (H _ Hin) as [Hin' Heq'].
  rewrite <-Heq.
  exact (eq_trans (Hashtable.find_opt_In _ _ _) (f_equal Some Heq')).
Qed.

Lemma node_to_graph_filtering_inv :
  forall x : ident * Source.type, node_to_graph_consistent_prop (fun _ imap _ y => Hashtable.find_opt imap y = Some (fst x)).
Proof using.
  intros x _ i0 _ _ i1 _ (_ & [H1 H2] & _) y H.
  apply Hashtable.find_opt_Some in H; destruct H as [Hin Heq]; rewrite <-Heq; clear Heq.
  specialize (H1 _ Hin) as Hin2.
  exact (eq_trans (Hashtable.find_opt_In _ _ _) (f_equal Some (eq_sym (H2 _ _)))).
Qed.

Definition node_to_graph_iter (excl : list ident) :
  node_to_graph_fun' (graph -> Source.equation -> node_to_graph_ret graph).
Proof using.
  intros i1 i2 i3 Hi g0 eqn.
  destruct eqn as [i [ty exp]].
  pose (raw_vars := Source.var_of_exp exp).
  pose (tmp := @List_filter_map_fold _ vertex i1 i2 i3 Hi raw_vars (node_to_graph_filtering excl raw_vars)).
  destruct tmp as [[[[m1 m2] m3] vl] [Hcim Hm]] eqn:eq1.
  pose (vars := remove_dup vl).
  destruct (var_idx m1 m2 m3 Hm i) as [[[[f1 f2] f3] v] [Hcmf Hf]].
  pose (g := Array.set g0 v vars).
  exists (f1, f2, f3, g).
  exact Hf.
Defined.

Lemma node_to_graph_iter_prop Vars (excl : list ident) :
  forall v0 i0 n0 H1, node_to_graph_assumption_n Vars v0 n0 ->
  forall (g0 : graph),
  List.length Vars <= Array.length g0 ->
  forall (e : Source.equation),
  In (fst e) Vars ->
  incl (map fst (Source.var_of_exp (projT2 (snd e)))) (excl ++ Vars) ->
  let 'exist _ (v1, i1, n1, g) _ := node_to_graph_iter excl v0 i0 n0 H1 g0 e in
  node_to_graph_consistency v0 i0 n0 v1 i1 n1 /\
  node_to_graph_assumption_n Vars v1 n1 /\
  exists v,
  Hashtable.find_opt v1 (fst e) = Some v /\
  (forall i, i <> v -> Array.get g i = Array.get g0 i) /\
  let vars := Array.get g v in
  incl (map (Hashtable.find_opt i1) vars) (map (fun p => Some (fst p)) (Source.var_of_exp (projT2 (snd e)))) /\
  incl (map (fun p => Some (fst p)) (Source.var_of_exp (projT2 (snd e)))) (map Some excl ++ map (Hashtable.find_opt i1) vars).
Proof using.
  intros i1 i2 i3 Hi Hni g0 Hlen0 eqn Hxin He.
  unfold node_to_graph_iter.
  destruct eqn as [i [ty exp]]; unfold fst in Hxin; unfold snd, projT1, projT2 in He.
  simpl (snd (_, _)); simpl (projT2 (existT _ _ _)); simpl projT1.
  pose (raw_vars := Source.var_of_exp exp); fold raw_vars in He |- *.
  cbn; generalize dependent raw_vars; clear exp; intros raw_vars He.
  specialize (List_filter_map_fold_prop Vars _ node_to_graph_filtering_inv
    _ _ _ Hi Hni raw_vars (node_to_graph_filtering excl raw_vars)) as tmp.
  specialize (fwd_List_filter_map_fold Vars _ _ _ Hi Hni raw_vars (node_to_graph_filtering excl raw_vars)) as tmp2.
  match type of tmp with ?p -> _ => assert (tmp3 : p) end.
  1:{
    clear - Vars excl raw_vars He; intros i1 i2 i3 Hi Hni x Hx f1 f2 f3 y [Hcif Hf] Heq.
    specialize (node_to_graph_filtering_prop excl raw_vars Vars He _ _ _ Hi Hni x Hx).
    rewrite Heq.
    tauto.
  }
  specialize (tmp tmp3).
  specialize (tmp2 (fun v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 => proj1 (tmp3 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13))).
  clear tmp3.
  match type of tmp with let 'exist _ _ _ := ?fm in _ => destruct fm as [[[[m1 m2] m3] vl] [Hcim Hm]] end.
  cbn in tmp2.
  destruct tmp as [Hnm Hvl].
  specialize (var_idx_prop Vars _ _ _ Hm Hnm i Hxin) as tmp.
  destruct (var_idx _ _ _ Hm i) as [[[[f1 f2] f3] v] [Hcmf Hf]], tmp as [Hnf Himgi].
  split; [exact (node_to_graph_consistency_trans Hcim Hcmf)|].
  split; [exact Hnf|].
  exists v.
  assert (vltg0 : v < Array.length g0).
  1:{ destruct Hf as (Hf1 & Hf2 & _ & Hf3 & Hf4).
    assert (tmp' := Hf3 _ (Hashtable.find_opt_Some_In _ _ _ Himgi)).
    rewrite (Hashtable.find_opt_Some_eq _ _ _ Himgi) in tmp'.
    refine (PeanoNat.Nat.lt_le_trans _ _ _ tmp' (PeanoNat.Nat.le_trans _ _ _ _ Hlen0)).
    clear - Hnf; unfold node_to_graph_assumption_n in Hnf; destruct Hnf as [Hnf _]; subst.
    match goal with |- context[partition ?f ?l] => destruct (partition f l) as [l1 l2] eqn:eq end; cbn.
    refine (PeanoNat.Nat.le_trans _ _ _ (PeanoNat.Nat.le_add_r _ _) (eq_ind _ (fun v => v <= _) _ _ (partition_length _ _ eq))).
    exact (NoDup_incl_length (proj2 (proj2 (remove_dup_wd _))) (proj1 (proj2 (remove_dup_wd _)))).
  }
  split; [exact Himgi|split].
  2: rewrite <-(map_map fst Some).
  2: rewrite (Array.get_set_same _ _ _ vltg0); clear g0 Hlen0 i Hxin v Himgi vltg0.
  2: split.
  - intros j Hj.
    exact (Array.get_set_other _ _ _ _ vltg0 (fun e => Hj (eq_sym e))).
  - intros j Hj.
    apply in_map_iff in Hj as Hj'; destruct Hj' as [v [<- Hv]]; clear Hj.
    apply (proj1 (proj2 (remove_dup_wd _))) in Hv.
    specialize (proj1 (Forall_forall _ _) Hvl _ Hv) as Hv2; cbn in Hv2.
    destruct Hv2 as [[i ty'] [Hin Heq]]; cbn in Heq; apply (in_map fst) in Hin; cbn in Hin; clear ty'.
    destruct Hcmf as (_ & [Hcmf2i Hcmf2e] & _).
    specialize (Hashtable.find_opt_Some_eq _ _ _ Heq) as Heq2.
    rewrite Hcmf2e in Heq2.
    rewrite (eq_trans (Hashtable.find_opt_In _ _ _) (f_equal Some Heq2)).
    apply in_map.
    exact Hin.
  - intros j Hj.
    apply in_map_iff in Hj; destruct Hj as [j' [<- Hj]]; rename j' into j.
    apply in_map_iff in Hj; destruct Hj as [[j' ty'] [[=->] Hj]].
    apply in_app_iff.
    destruct (List_mem j excl) as [|] eqn:eqmem.
    1: left; apply mem_wd in eqmem; exact (in_map Some _ _ eqmem).
    right.
    apply in_map_iff.
    refine (match _ with ex_intro _ x (conj H1 H2) => ex_intro _ x (conj H1 (proj1 (remove_dup_wd _) _ H2)) end).
    apply in_map_iff.
    assert (go_back : In (Some j) (map (Hashtable.find_opt m2) vl) -> In (Some j) (map (Hashtable.find_opt f2) vl));
      [|apply go_back; clear go_back].
    { destruct Hcmf as (_ & [Hconv Heq] & _); clear - Hconv Heq.
      intros h.
      apply in_map_iff in h; destruct h as [v [eqv Hin]].
      apply in_map_iff; exists v; split; [|exact Hin].
      specialize (Hashtable.find_opt_iff m2 v); rewrite eqv; intros [H eqj].
      rewrite Heq in eqj.
      specialize (Hashtable.find_opt_iff f2 v); destruct (Hashtable.find_opt f2 v); [|intros f; contradiction (f (Hconv _ H))].
      intros [H' eqi].
      rewrite (eq_trans (Hashtable.find_ext _ _ _ _) eqi) in eqj.
      exact (f_equal _ eqj). }
    clear - He Hj eqmem tmp2.
    specialize (tmp2 _ Hj (fun _ i _ => In (Some j) (map (Hashtable.find_opt i) vl))).
    refine (tmp2 _ _); clear - He eqmem.
    + intros m1 m2 m3 Hm Hnm Hcim e f1 f2 f3 Hf Hnf Hcmf.
      specialize (node_to_graph_filtering_prop excl raw_vars Vars He _ _ _ Hm Hnm _ Hj) as tmp.
      rewrite e in tmp.
      cbn in tmp.
      apply mem_wd in tmp.
      rewrite eqmem in tmp.
      discriminate tmp.
    + intros m1 m2 m3 Hm [[e1 e2] e3] y [Hcme He0] Hnm Hcim e Hin f1 f2 f3 Hf Hnf Hcef.
      specialize (node_to_graph_filtering_prop excl raw_vars Vars He _ _ _ Hm Hnm _ Hj) as tmp.
      rewrite e in tmp.
      cbn in tmp; destruct tmp as [_ [_ Heq]].
      specialize (Hashtable.find_opt_Some_eq _ _ _ Heq) as Heq2.
      destruct Hcef as (_ & [Hcef2i Hcef2e] & _).
      rewrite Hcef2e in Heq2.
      rewrite <-(eq_trans (Hashtable.find_opt_In _ _ _) (f_equal Some Heq2)).
      exact (in_map (Hashtable.find_opt f2) _ _ Hin).
Qed.

Definition node_to_graph (source: Source.node): graph * Hashtable.t vertex ident.
Proof using.
  destruct source as [loc _ n_in n_out n_locals n_body n_vars _ _ _ _]; clear n_vars.
  pose (excl := map fst n_in).
  pose (n := List.length n_out + List.length n_locals).
  pose (g := Array.make n [] : graph).
  pose (var_table := Hashtable.create ident vertex n).
  pose (index_table := Hashtable.create vertex ident n).
  pose (nxt := O).
  assert (H : node_to_graph_assumptions var_table index_table nxt).
  1:{
    split; [|split; [|split; [|split]]].
    3: intros ? ? f; contradiction (Hashtable.In_create f).
    1-3: intros ? f; exfalso; exact (Hashtable.In_create f).
    intros ? f; inversion f.
  }
  pose (f := node_to_graph_iter excl).
  unshelve refine (
    let 'exist _ (_, idx_map, _, g) _ := (fix inner (body : list _) i1 i2 i3 Hi g {struct body} := _) n_body var_table index_table nxt H g
      : node_to_graph_ret graph
    in (g, idx_map)); clear - f inner body i1 i2 i3 Hi g.
  destruct body as [|e tl].
  1: exists (i1, i2, i3, g); exact Hi.
  destruct (f _ _ _ Hi g e) as [[[[m1 m2] m3] g'] Hm] eqn:eqf.
  exact (inner tl m1 m2 m3 Hm g').
Defined.

(* TODO move this? *)
Lemma nodup_remove_dup : forall l, NoDup l -> remove_dup l = l.
Proof using.
  intros l; induction l as [|hd tl IH]; intros h.
  1: exact eq_refl.
  inversion h as [|? ? Hhd Htl]; subst; clear h.
  cbn.
  destruct (List_mem hd (remove_dup tl)) as [|] eqn:eqm; [|clear eqm].
  1: apply mem_wd in eqm; contradict Hhd.
  1: exact (proj1 (proj2 (remove_dup_wd _)) _ eqm).
  exact (f_equal (cons hd) (IH Htl)).
Qed.

Definition graph_prop (g: graph): Prop :=
  forall k, k < Array.length g -> Forall (fun v : vertex => v < Array.length g) (Array.get g k).

Definition graph_imap_prop (source: Source.node) n (g: graph) (imap: Hashtable.t vertex ident) :=
  Array.length g = n /\
  (forall v, Hashtable.InMap v imap <-> v < n) /\
  (forall k1 k2 H1 H2, Hashtable.find imap k1 H1 = Hashtable.find imap k2 H2 -> k1 = k2) /\
  (forall v H, In (Hashtable.find imap v H) (map fst source.(Source.n_assigned_vars))) /\
  (forall i, In i source.(Source.n_assigned_vars) -> exists v, Hashtable.find_opt imap v = Some (fst i)) /\
  Forall (fun '(i, existT _ ty e) =>
    forall v, Hashtable.find_opt imap v = Some i ->
    incl (map (Hashtable.find_opt imap) (Array.get g v))
         (map (fun p => Some (fst p)) (Source.var_of_exp e)) /\
    incl (map (fun p => Some (fst p)) (Source.var_of_exp e))
         (map Some (map fst source.(Source.n_in)) ++
          map (Hashtable.find_opt imap) (Array.get g v))) source.(Source.n_body).

Lemma graph_prop_is_graph_wd {source n g imap}: graph_imap_prop source n g imap ->
  forall i, i < Array.length g -> Forall (fun k => k < n) (Array.get g i).
Proof using.
  intros (h1 & h2 & h3 & h4 & h5 & h6) v Hv.
  rewrite h1, <-h2 in Hv.
  specialize (h4 v Hv) as Hin.
  unfold Source.n_assigned_vars in Hin; rewrite map_map in Hin; cbn in Hin.
  apply in_map_iff in Hin; destruct Hin as [[i [ty e]] [eqi Hity]].
  specialize (proj1 (Forall_forall _ _) h6 _ Hity v) as tmp.
  specialize (Hashtable.find_opt_In _ _ Hv) as tmp2; rewrite <-eqi in tmp2; specialize (tmp tmp2); clear tmp2.
  destruct tmp as [tmp _]; clear - tmp h2.
  apply Forall_forall; intros w Hw; apply h2.
  specialize (tmp _ (in_map _ _ _ Hw)); apply in_map_iff in tmp; destruct tmp as [[i ty'] [Hity _]]; cbn in Hity.
  exact (Hashtable.find_opt_Some_In _ _ _ (eq_sym Hity)).
Qed.

Lemma node_to_graph_prop' (source: Source.node):
  let n := List.length source.(Source.n_out) + List.length source.(Source.n_locals) in
  let (g, imap) := node_to_graph source in
  graph_imap_prop source n g imap.
Proof using.
  intros n.
  unfold graph_imap_prop, node_to_graph;
    destruct source as [loc n_name n_in n_out n_locals n_body n_vars n_assigned_vars n_all_vars_exist n_vars_all_assigned n_vars_unique];
    simpl in n |- *.
  unfold Source.n_assigned_vars, Source.n_body; fold n_assigned_vars.
  pose (Vars := map fst n_assigned_vars).
  pose (excl := map fst n_in); fold excl.
  fold n.
  pose (g := Array.make n (@nil ident) : graph); fold g.
  assert (Hg : Array.length g = n) by exact (Array.length_make _ _).
  assert (HVars : List.length Vars <= n).
  1:{
    unfold Vars, n.
    rewrite (length_map (A:=Source.binder)), (Permutation_length n_vars_all_assigned), length_app.
    exact (le_n _).
  }
  pose (var_table := Hashtable.create ident vertex n); fold var_table.
  pose (index_table := Hashtable.create vertex ident n); fold index_table.
  pose (nxt := O).
  match goal with |- context[?f0 n_body var_table index_table O ?P0] =>
    pose (f := f0); pose (P := P0 : node_to_graph_assumptions _ _ nxt); fold f P end.
  match goal with |- let (g0, imap) := _ in ?ret =>
    change (let (g0, imap) := let 'exist _ (_, idx_map, _, g0) _ := f n_body var_table index_table nxt P g
            in (g0, idx_map) in ret) end.
  rename var_table into i1, index_table into i2, nxt into i3, P into Hi.
  assert (Hni : node_to_graph_assumption_n Vars i1 i3).
  1:{
    split.
    2: intros ? Hf; contradict Hf.
    2: solve [apply Hashtable.In_create].
    assert (tmp : NoDup Vars).
    1:{ unfold Vars, n_assigned_vars in *; unfold n_vars in n_vars_unique.
      apply (Permutation_NoDup (Permutation_map _ (Permutation_sym n_vars_all_assigned))); clear - n_vars_unique.
      induction n_in as [|hd tl IH]; [exact n_vars_unique|].
      inversion n_vars_unique; apply IH; assumption. }
    unfold node_to_graph_assumption_n.
    rewrite (nodup_remove_dup _ tmp).
    unfold Vars, i1, i3, n_assigned_vars in n_vars_all_assigned |- *; clear - n_vars_all_assigned.
    refine (f_equal (fun v => List.length (fst v)) (x := ([], map fst (map Source.equation_dest n_body))) _).
    clear; induction n_body as [|[i tmp] tl IH]; [exact eq_refl|cbn; rewrite <-IH; clear tmp IH].
    rewrite (proj2 (Hashtable.find_opt_None _ _) (@Hashtable.In_create _ _ _ _)).
    exact eq_refl.
  }
  destruct (f n_body i1 i2 i3 Hi g) as [[[[f1 f2] f3] fg] Hf] eqn:eqf.
  refine (match _ :
    (forall k,
      (forall i, In i (map Source.equation_dest n_body) -> Hashtable.find_opt f2 k <> Some (fst i)) ->
      Array.get g k = Array.get fg k) /\
    node_to_graph_assumption_n Vars f1 f3 /\
    node_to_graph_consistency i1 i2 i3 f1 f2 f3 /\
    _ /\
    (forall k, In (Hashtable.find_opt f2 k) (map Some Vars) \/ f3 <= k) /\
    _ /\
    _ with conj _ (conj Hnf (conj Hcif (conj H1 (conj H3 (conj H4 H5))))) =>
    conj H1 (conj _ (conj (proj1 (proj2 (proj2 Hf))) (conj _ (conj H4 H5)))) end).
  2:{
    destruct Hnf as [eqf3 _].
    destruct Hf as (Hf1 & Hf2 & Hf3 & Hf4 & Hf5); clear - Hf1 Hf2 Hf4 Hf5 eqf3 H4 n_vars_unique n_vars_all_assigned.
    assert (Hf5' : forall j, j < f3 -> Hashtable.InMap j f2).
    1:{
      clear - Hf1 Hf5.
      intros v Hv; specialize (Hf5 v Hv) as [i [Hi eqv]].
      rewrite <-eqv.
      specialize (Hf1 _ Hi) as [Hv' tmp].
      exact Hv'.
    }
    assert (Hf3 : f3 = n).
    1:{
      rewrite eqf3.
      clear Hf1 Hf4 Hf5.
      unfold Vars, n; rewrite <-length_app, <-(Permutation_length n_vars_all_assigned).
      unfold n_vars in n_vars_unique; rewrite map_app in n_vars_unique; apply NoDup_app_remove_l in n_vars_unique.
      rewrite <-(Permutation_map _ n_vars_all_assigned) in n_vars_unique.
      fold Source.binder; rewrite (nodup_remove_dup _ n_vars_unique), <-(length_map (A := Source.binder) fst n_assigned_vars).
      refine (f_equal (fun p => List.length (fst p)) (y := (_, [])) _).
      assert (tmp : Forall (fun i => Hashtable.InMap i f1) (map (A:=Source.binder) fst n_assigned_vars)).
      1:{
        apply Forall_forall; intros i Hi.
        apply in_map_iff in Hi; destruct Hi as [b [<- Hb]].
        specialize (H4 _ Hb) as [v Hv].
        specialize (Hashtable.find_opt_Some _ _ _ Hv) as [Hin Heq].
        rewrite <-Heq.
        specialize (Hf2 _ Hin) as [Hin2 Heq2].
        exact Hin2.
      }
      pose (l := map (A:=Source.binder) fst n_assigned_vars); fold l in tmp |- *; generalize dependent l.
      clear; intros l Hl; induction l as [|hd tl IH]; [exact eq_refl|cbn].
      inversion Hl as [|? ? Hh Ht]; subst; rewrite (IH Ht).
      destruct (Hashtable.find_opt f1 hd) as [?|] eqn:eq; [exact eq_refl|contradiction (proj1 (Hashtable.find_opt_None _ _) eq Hh)].
    }
    clear eqf3; subst f3.
    intros v; split; [intros Hv|exact (Hf5' v)].
    specialize (Hf2 _ Hv) as [Hiin Hieq].
    rewrite <-Hieq.
    exact (Hf4 _ _).
  }
  2:{
    unfold Vars; clear - Hf H3; rename H3 into H.
    intros v Hv.
    specialize (H v) as [H|H].
    1: rewrite (Hashtable.find_opt_In _ _ Hv) in H; apply in_map_iff in H.
    1:  destruct H as [? [[=->] H]]; exact H.
    contradict H.
    destruct Hf as (H1 & H2 & H3 & H4 & H5).
    specialize (H2 v Hv) as [Hi Heq].
    specialize (H4 (Hashtable.find f2 v Hv) Hi); rewrite Heq in H4.
    exact (Arith_base.lt_not_le_stt _ _ H4).
  }
  subst n_assigned_vars; subst n_vars.
  assert (HinVars : incl (map fst n_body) Vars).
  1:{ unfold Vars; clear; intros i Hi.
    apply in_map_iff in Hi; destruct Hi as [[j te] [<- Hj]].
    rewrite map_map; apply in_map; exact Hj.
  }
  assert (HexpVars : Forall (fun ie => incl (map fst (Source.var_of_exp (projT2 (snd ie)))) (excl ++ Vars)) n_body).
  1:{ unfold excl, Vars.
    refine (Forall_impl _ _ n_all_vars_exist); clear - n_vars_all_assigned.
    intros [i [ty e]] H; cbn in H |- *.
    rewrite <-map_app; apply incl_map.
    intros ity Hity.
    specialize (H _ Hity).
    apply in_or_app.
    apply in_app_or in H; destruct H as [H|H]; [left; exact H|right].
    exact (Permutation_in _ (Permutation_sym n_vars_all_assigned) H).
  }
  assert (Hnodup_body : NoDup (map fst n_body)).
  1: rewrite <-(map_map Source.equation_dest fst);
       refine (Permutation_NoDup (Permutation_sym (Permutation_map fst n_vars_all_assigned)) _).
  1: rewrite map_app in n_vars_unique; exact (NoDup_app_remove_l _ _ n_vars_unique).
  clear n_all_vars_exist n_vars_all_assigned n_vars_unique.
  generalize dependent Vars; intros Vars HVars Hni HinVars HexpVars.
  generalize dependent fg; generalize dependent f3; generalize dependent f2; generalize dependent f1;
  generalize dependent g;
  generalize dependent Hi; generalize dependent Hni; generalize dependent i3; generalize dependent i2; generalize dependent i1.
  induction n_body as [|hd tl IH]; intros i1 i2 i3 Hni Hi g Hg f1 f2 f3 Hf fg Heqf.
  - injection Heqf as <- <- <- <-; repeat match goal with |- _ /\ _ => split end; try assumption.
    + intros k _; exact eq_refl.
    + exact node_to_graph_consistency_refl.
    + intros v; cbn in *; clear g Hg Hf f.
      destruct Hi as (H1 & H2 & H3 & H4 & H5).
      destruct (PeanoNat.Nat.lt_ge_cases v i3) as [vlti3|i3lev]; [left|right; exact i3lev].
      destruct (H5 _ vlti3) as [i [Hi <-]].
      specialize (H1 i Hi) as [Hv Heq].
      rewrite (Hashtable.find_opt_In _ _ Hv); apply in_map; rewrite Heq.
      apply Hni.
      exact Hi.
    + intros ? [].
    + exact (Forall_nil _).
  - cbn in Heqf.
    destruct (node_to_graph_iter excl i1 i2 i3 Hi g) as [[[[m1 m2] m3] g'] Hm] eqn:eqiter.
    inversion HexpVars as [|tmp1 tmp2 HeVars HbodyVars]; subst tmp1 tmp2.
    inversion Hnodup_body as [|tmp1 tmp2 Hhd_not_tl Hnodup_tl]; subst tmp1 tmp2.
    specialize (node_to_graph_iter_prop
      Vars excl i1 i2 i3 Hi Hni g
      (eq_ind _ (fun v => _ <= v) HVars _ (eq_sym Hg))
      hd (HinVars _ (or_introl eq_refl)) HeVars) as Hiter.
    rewrite eqiter in Hiter.
    destruct Hiter as [Hcim [Hnm [v (Hv1 & Hv2 & Hv3)]]].
    assert (Hg' : Array.length g' = n).
    1:{
      rewrite <-Hg; clear - eqiter.
      unfold node_to_graph_iter in eqiter; destruct hd as [i [ty e]].
      destruct (List_filter_map_fold i1 i2 i3 Hi (Source.var_of_exp e) (node_to_graph_filtering excl (Source.var_of_exp e))) as [[[[l1 l2] l3] vl] [Hcil Hl]].
      destruct (var_idx l1 l2 l3 Hl i) as [[[[v1 v2] v3] v] [Hclv Hv]].
      injection eqiter as <- <- <- <-.
      exact (Array.length_set _ _ _).
    }
    specialize (IH Hnodup_tl (fun _ h => HinVars _ (or_intror h)) HbodyVars m1 m2 m3 Hnm Hm g' Hg' f1 f2 f3 Hf fg Heqf); clear Hg'.
    destruct IH as (IH1 & Hnf & Hcmf & IH2 & IH3 & IH4 & IH5).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    + intros v' Hv'.
      rewrite <-(IH1 v' (fun i Hi => Hv' i (or_intror Hi))); clear f IH1 IH2 IH3 IH4 IH5 fg Heqf.
      apply eq_sym, Hv2.
      specialize (Hv' _ (or_introl eq_refl)); cbn in Hv'.
      intros ->.
      destruct Hcmf as (_ & [HcIn HcEq] & _), Hm as (Hm & ?).
      clear - Hv' Hv1 Hv2 HcIn HcEq Hm.
      contradict Hv'.
      specialize (Hashtable.find_opt_Some _ _ _ Hv1) as [Hvin Hveq]; rewrite <-Hveq; clear Hv1.
      specialize (Hm _ Hvin) as [Hhdin Hhdeq].
      specialize (HcEq _ Hhdin); rewrite Hhdeq in HcEq.
      exact (eq_trans (Hashtable.find_opt_In _ _ _) (f_equal Some (eq_sym HcEq))).
    + exact (node_to_graph_consistency_trans Hcim Hcmf).
    + intros j [<-|Hj]; [|exact (IH4 j Hj)].
      exists v.
      apply Hashtable.find_opt_Some in Hv1; destruct Hv1 as [Hv1i Hv1e].
      destruct Hcmf as ([Hci Hce] & _).
      specialize (Hce _ Hv1i); rewrite Hv1e in Hce; rewrite Hce.
      destruct Hf as (Hf & ?).
      specialize (Hf _ (Hci _ Hv1i)) as tmp; destruct tmp as [Hv2i Hv2e].
      exact (eq_trans (Hashtable.find_opt_In _ _ _) (f_equal Some Hv2e)).
    + refine (Forall_cons _ _ IH5).
      destruct hd as [i [ty e]].
      cbn in Hv1.
      intros w Hwf.
      assert (tmp : v = w).
      1:{
        specialize (Hashtable.find_opt_Some _ _ _ Hwf) as [Hwinf Hweqf].
        rewrite <-Hweqf in Hv1.
        specialize (Hashtable.find_opt_Some _ _ _ Hv1) as [Hiinm Hieqm].
        specialize (proj1 Hcmf) as [Hc1 Hc2].
        rewrite Hc2 in Hieqm.
        specialize (proj1 (proj2 Hf) w Hwinf) as [Hwinf' eqw]; exact (eq_trans (eq_sym Hieqm) (eq_trans (Hashtable.find_ext _ _ _ _) eqw)).
      }
      subst w.
      refine (eq_ind _ (fun l => incl (map _ l) _ /\ incl _ (_ ++ map _ l)) _ _ (IH1 _ _)).
      2: intros [j jty] Hj; rewrite Hwf; intros [=<-]; apply (in_map fst) in Hj; rewrite map_map in Hj; exact (Hhd_not_tl Hj).
      cbn in Hv3; destruct Hcmf as (? & [Hcmfi Hcmfe] & ?).
      unfold Source.var_of_exp; rewrite <-(map_map fst Some) in Hv3 |- *; remember (map fst (Source.var_of_exp_aux e [])) as l0 eqn:eql0.
      remember (Array.get g' v) as l eqn:eql.
      subst excl; clear - Hv3 Hcmfi Hcmfe.
      split; [destruct Hv3 as [H _]; induction l as [|hd tl IH]|destruct Hv3 as [_ H]; induction l0 as [|hd tl IH]].
      1,3: intros ? [].
      1,2: intros ? [<-|h]; [|exact (IH (fun _ h => H _ (or_intror h)) _ h)].
      1,2: specialize (H _ (or_introl eq_refl)).
      2: apply in_app_iff in H; apply in_app_iff; destruct H as [H|H]; [left; exact H|right].
      1,2: apply in_map_iff in H; destruct H as [x [Hx1 Hx2]]; apply in_map_iff; exists x; split; [|exact Hx2].
      1: apply eq_sym in Hx1; apply eq_sym.
      1,2: apply Hashtable.find_opt_Some in Hx1; destruct Hx1 as [Hxin Hx1]; rewrite Hcmfe in Hx1.
      1,2: exact (eq_trans (Hashtable.find_opt_In _ _ _) (f_equal Some Hx1)).
Qed.

Definition node_to_graph_prop (source: Source.node) : forall g imap, (g, imap) = node_to_graph source -> _ :=
  fun g imap Heq => eq_ind_r (fun gimap => let '(g, imap) := gimap in _) (node_to_graph_prop' source) Heq.

Lemma graph_imap_prop_graph_prop source n g imap: graph_imap_prop source n g imap -> graph_prop g.
Proof using.
  intros (<- & H2 & H3 & H4 & H5 & H6) v Hv. clear - Hv H2 H4 H6.
  apply H2 in Hv.
  specialize (H4 _ Hv).
  unfold Source.n_assigned_vars in H4.
  rewrite map_map, in_map_iff in H4; destruct H4 as [[i [ty e]] [[=->] Hity]].
  rewrite Forall_forall in H6; specialize (H6 _ Hity v (Hashtable.find_opt_In _ _ _)) as [H6 _].
  apply Forall_forall; intros w Hw.
  specialize (H6 (Hashtable.find_opt imap w) (in_map _ _ _ Hw)); apply in_map_iff in H6; destruct H6 as [jty' [eqj Hjty]].
  apply H2.
  exact (Hashtable.find_opt_Some_In _ _ _ (eq_sym eqj)).
Qed.


Inductive color := White | Grey | Black.

Definition List_mem_vertex : vertex -> list vertex -> bool := List_mem.
Definition mem_vertex_wd : forall (x : vertex) (l : list vertex), List_mem_vertex x l = true <-> In x l := mem_wd.

Fixpoint map_in {A B} (l : list A) (f : forall x : A, In x l -> B) : list B.
Proof using.
  destruct l as [|hd tl]; [exact []|exact (f hd (or_introl eq_refl) :: map_in _ _ tl (fun _ h => f _ (or_intror h)))].
Defined.
Definition rev_map_in {A B} l f := rev (@map_in A B l f).

Fixpoint visit_node_inner
  (n: nat) (imap: Hashtable.t vertex ident)
  (rec: Array.t color -> forall v : vertex, v < n /\ Hashtable.InMap v imap -> list vertex -> Result.t Source.type (Array.t color * list vertex))
  (cs: Array.t color)
  (neighs: list vertex)
  (Hneighs: Forall (fun v => v < n /\ Hashtable.InMap v imap) neighs)
  (acc: list vertex)
  {struct neighs}:
  Result.t Source.type (Array.t color * list vertex).
Proof using.
  destruct neighs as [|hd tl]; [exact (Result.Ok (cs, acc))|].
  refine (Result.bind (rec cs hd (Forall_inv Hneighs) acc) _); clear cs acc.
  intros [cs acc].
  exact (visit_node_inner n imap rec cs tl (Forall_inv_tail Hneighs) acc).
Defined.

Fixpoint visit_node (loc: Result.location)
  (g: graph) (Hg : forall k, k < Array.length g -> Forall (fun v => v < Array.length g) (Array.get g k))
  (imap: Hashtable.t vertex ident)
  (Himapg : forall k, k < Array.length g -> Forall (fun v => Hashtable.InMap v imap) (Array.get g k))
  (cs: Array.t color) (fuel: nat)
  (hist: list vertex) (Himaph : Forall (fun v => Hashtable.InMap v imap) hist)
  (cur: vertex) (Hcur : cur < Array.length g) (Himapc : Hashtable.InMap cur imap)
  (acc: list vertex) {struct fuel}: Result.t Source.type (Array.t color * list vertex).
Proof using.
  destruct fuel as [|fuel]; [exact (Result.Err [(loc, Result.InternalError "topological sort ran out of fuel")])|].
  pose (hist' := cur :: hist).
  assert (Himaph' := Forall_cons cur Himapc Himaph : Forall _ hist').
  refine (match Array.get cs cur with
    | White => _
    | Grey => Result.Err [(loc, Result.CyclicDependency (rev_map_in hist' (fun v Hv => Hashtable.find imap v (proj1 (Forall_forall _ _) Himaph' _ Hv))))]
    | Black => Result.Ok (cs, acc)
    end).
  pose (cs' := Array.set cs cur Grey).
  refine (Result.bind
    (visit_node_inner _ _
      (fun cs cur Hcur acc => visit_node loc g Hg imap Himapg cs fuel hist' Himaph' cur (proj1 Hcur) (proj2 Hcur) acc)
      cs' (Array.get g cur) _ acc) _).
  1: exact (proj2 (Forall_forall (fun v => v < Array.length g /\ Hashtable.InMap v imap) (Array.get g cur))
       (fun v Hv => conj (proj1 (Forall_forall _ _) (Hg _ Hcur) _ Hv) (proj1 (Forall_forall _ _) (Himapg _ Hcur) _ Hv))).
  intros [cs'' acc'].
  pose (csf := Array.set cs'' cur Black).
  exact (Result.Ok (csf, cur :: acc')).
Defined.

Inductive accessible (g: graph) (dst: vertex) |: vertex -> nat -> Prop :=
  | accessible_end: accessible dst O
  | accessible_step (cur nxt: vertex) (rem: nat): In nxt (Array.get g cur) -> accessible nxt rem -> accessible cur (S rem)
.
Inductive has_cycle_from (g: graph) (v: vertex) | (c: vertex): nat -> Prop :=
  | cycle_end: In v (Array.get g c) -> has_cycle_from c O
  | cycle_step (n: vertex) (rem: nat): In n (Array.get g c) -> has_cycle_from n rem -> has_cycle_from c (S rem)
.
Definition has_cycle_len (g: graph) (n: nat): Prop := exists v, v < Array.length g /\ has_cycle_from g v v n.
Definition has_cycle (g: graph): Prop := exists n, has_cycle_len g n.

Fixpoint accessibility_witness (g: graph) (src: vertex) (w: list vertex) (dst: vertex): Prop := match w with
  | [] => src = dst
  | nxt :: tl => In nxt (Array.get g src) /\ accessibility_witness g nxt tl dst
  end.

Lemma accessibility_witness_app g src w1 v w2 dst:
  accessibility_witness g src (w1 ++ v :: w2) dst <->
  accessibility_witness g src (w1 ++ [v]) v /\ accessibility_witness g v w2 dst.
Proof using.
  split; revert src; induction w1 as [|hd tl IH]; intros src [H1 H2]; split.
  2,6: exact H2.
  1: split; [exact H1|exact eq_refl].
  1: split; [exact H1|exact (proj1 (IH _ H2))].
  1: exact (proj2 (IH _ H2)).
  1,2: exact (proj1 H1).
  exact (IH _ (conj (proj2 H1) H2)).
Qed.

Lemma has_cycle_accessible: forall g v c n, has_cycle_from g v c n <-> accessible g v c (S n).
Proof using.
  intros g v c n; split; intros H; [|remember (S n) as m eqn:eqm; revert n eqm]; induction H.
  1: apply accessible_step with v; [assumption|exact (accessible_end _ _)].
  1: apply accessible_step with n; assumption.
  1: intros n f; discriminate f.
  intros [|n] [=->].
  1: inversion H0; subst; apply cycle_end; assumption.
  apply cycle_step with nxt; [assumption|auto].
Qed.

Lemma accessible_iff_witness : forall g v c n, accessible g v c n <-> exists l, List.length l = n /\ accessibility_witness g c l v.
Proof using.
  intros g v c n; split.
  - intros H; induction H as [|c n k H1 H2 [l [IH1 IH2]]].
    1: exists []; split; exact eq_refl.
    exists (n :: l); split; [exact (f_equal S IH1)|exact (conj H1 IH2)].
  - intros [l [<- Ha]].
    revert c Ha; induction l as [|hd tl IH]; intros c Ha; [cbn in Ha; subst; exact (accessible_end _ _)|destruct Ha as [Hhd Ha]].
    specialize (IH _ Ha).
    exact (accessible_step _ _ _ _ _ Hhd IH).
Qed.

Lemma nodup_of_lt_has_length : forall l n, NoDup l -> Forall (fun i => i < n) l -> List.length l <= n.
Proof using.
  intros l n Hdup Hel.
  assert (Hincl : incl l (iter n (fun l0 => O :: map S l0) [])).
  - intros k Hk.
    rewrite Forall_forall in Hel; apply Hel in Hk; clear - Hk.
    revert n Hk; induction k as [|k IHk]; (intros [|n] Hk; [inversion Hk|]).
    1: left; exact eq_refl.
    right; apply in_map; exact (IHk _ (le_S_n _ _ Hk)).
  - refine (eq_ind _ (fun k => _ <= k) (NoDup_incl_length Hdup Hincl) _ _); clear.
    induction n as [|n IHn]; [exact eq_refl|].
    simpl; rewrite length_map; exact (f_equal S IHn).
Qed.

Lemma has_cycle_red g: graph_prop g -> has_cycle g -> exists n, n <= Array.length g /\ has_cycle_len g n.
Proof using.
  unfold graph_prop; intros gprop [n [v [Hv Hg]]].
  apply has_cycle_accessible, accessible_iff_witness in Hg.
  destruct Hg as [l [Hn Hl]].
  pose (acc := @nil vertex).
  rewrite (eq_refl : l = rev acc ++ l) in Hn, Hl.
  assert (H := NoDup_nil _ : NoDup acc).
  assert (H2 := Forall_nil _ : Forall (fun v : vertex => v < Array.length g) acc).
  generalize dependent acc; induction l as [|hd tl IH]; intros acc Hn Hl H H2.
  - exists n.
    split.
    2: exists v; split; [|apply has_cycle_accessible, accessible_iff_witness; exists (rev acc ++ []); split]; assumption.
    rewrite app_nil_r in Hn, Hl.
    apply gprop in Hv.
    refine (PeanoNat.Nat.le_trans _ _ _ _ (nodup_of_lt_has_length _ (Array.length g) H H2)).
    fold vertex; rewrite <-length_rev, Hn; exact (le_S _ _ (le_n _)).
  - destruct (List_mem_vertex hd acc) as [|] eqn:eqhd.
    + apply mem_vertex_wd, in_split in eqhd; destruct eqhd as [acc1 [acc2 ->]].
      exists (List.length acc1); split.
      1: apply NoDup_app_remove_r in H.
      1: apply Forall_app, proj1 in H2.
      1: exact (nodup_of_lt_has_length _ (Array.length g) H H2).
      exists hd; split.
      1: exact (Forall_elt _ _ _ H2).
      clear - Hl; rewrite rev_app_distr, <-app_assoc in Hl; cbn in Hl.
      rewrite <-app_assoc in Hl; cbn in Hl.
      apply accessibility_witness_app in Hl; destruct Hl as [_ Hl].
      apply accessibility_witness_app in Hl; destruct Hl as [Hl _].
      apply has_cycle_accessible, accessible_iff_witness.
      refine (ex_intro _ _ (conj _ Hl)).
      rewrite length_app, length_rev, PeanoNat.Nat.add_comm; exact eq_refl.
    + refine (IH (hd :: acc) _ _ (NoDup_cons _ _ H) (Forall_cons _ _ H2)).
      * rewrite length_app, length_rev; rewrite length_app, length_rev, length_cons, PeanoNat.Nat.add_succ_r in Hn; exact Hn.
      * cbn; rewrite <-app_assoc; exact Hl.
      * intros f; apply mem_vertex_wd in f; rewrite f in eqhd; discriminate eqhd.
      * clear - Hv Hl gprop.
        pose (w := v).
        change v with w in Hl at 1; fold w in Hv.
        generalize dependent w; induction (rev acc) as [|hd1 tl1 IH]; intros w Hw Hacc.
        1: exact (proj1 (Forall_forall _ _) (gprop _ Hw) _ (proj1 Hacc)).
        refine (IH _ _ (proj2 Hacc)).
        exact (proj1 (Forall_forall _ _) (gprop _ Hw) _ (proj1 Hacc)).
Qed.

Lemma accessibility_witness_and : forall g v l1 w l2 x,
  accessibility_witness g v l1 w -> accessibility_witness g w l2 x -> accessibility_witness g v (l1 ++ l2) x.
Proof using.
  intros g v l1 w l2 x Hvw Hwx; revert v Hvw; induction l1 as [|hd tl IH]; intros v Hvw.
  1: exact (eq_ind_r (fun a => accessibility_witness _ a _ _) Hwx Hvw).
  exact (conj (proj1 Hvw) (IH _ (proj2 Hvw))).
Qed.

Definition has_reachable_cycle_from (g: graph) (v: vertex) : Prop :=
  exists vc nr nc, accessible g vc v nr /\ has_cycle_from g vc vc nc.

Definition coherent_coloring (g: graph) (hist: list vertex) (col: Array.t color): Prop :=
  Array.length g = Array.length col /\
  NoDup hist /\
  (forall v : vertex, In v hist -> v < Array.length g) /\
  (forall v : vertex, v < Array.length g -> Array.get col v = Grey <-> In v hist) /\
  (forall v : vertex, v < Array.length g -> Array.get col v = Black ->
    ~ has_reachable_cycle_from g v /\
    forall w : vertex, In w (Array.get g v) -> Array.get col w = Black).

Fixpoint coherent_hist (g: graph) (hist: list vertex) (cur: vertex) := match hist with
  | [] => True
  | v :: tl => In cur (Array.get g v) /\ coherent_hist g tl v
  end.

Lemma coherent_is_witness g hist cur: coherent_hist g hist cur -> accessibility_witness g (hd cur (rev hist)) (tl (rev (cur :: hist))) cur.
Proof using.
  intros H.
  rewrite <-(rev_involutive hist) in H.
  cbn; remember (rev hist) as h eqn:eqh; clear hist eqh.
  destruct h as [|hd tl]; [exact eq_refl|cbn].
  rewrite <-(rev_involutive tl); cbn in H.
  remember (rev tl) as hist eqn:eqh; clear tl eqh.
  revert cur hd H; induction hist as [|hd2 tl IH]; intros cur hd H.
  1: exact (conj (proj1 H) eq_refl).
  exact (accessibility_witness_and _ _ _ _ [cur] _ (IH _ _ (proj2 H)) (conj (proj1 H) eq_refl)).
Qed.

Fixpoint correct_sort_result_fix (g: graph) (s: list vertex) := match s with
  | [] => True
  | hd :: tl => Forall (fun v : vertex => In v tl) (Array.get g hd) /\ correct_sort_result_fix g tl
  end.
Definition correct_sort_result' (g: graph) (s: list vertex) :=
  correct_sort_result_fix g s /\
  NoDup s.
Definition correct_sort_result (g: graph) (cs: Array.t color) (s: list vertex) :=
  correct_sort_result' g s /\
  (forall k, In k s -> k < Array.length g) /\
  (forall k, k < Array.length g -> Array.get cs k = Black <-> In k s).

Fixpoint white_count_inner (cs: Array.t color) (n: nat) := match n with
  | O => O
  | S n => match Array.get cs n with White => S (white_count_inner cs n) | _ => white_count_inner cs n end
  end.
Definition white_count (cs: Array.t color) := white_count_inner cs (Array.length cs).

Lemma visit_node_prop : forall loc (g: graph) Hg imap Himapg cs fuel hist Himaph cur Hcur Himapc acc,
  white_count cs < fuel ->
  coherent_coloring g hist cs ->
  coherent_hist g hist cur ->
  correct_sort_result g cs acc ->
  Forall (fun v => v < Array.length g) hist ->
  (exists cs' acc',
     coherent_coloring g hist cs' /\
     Array.get cs' cur = Black /\ (forall i, Array.get cs i = Black -> Array.get cs' i = Black) /\
     correct_sort_result g cs' acc' /\ incl acc acc' /\
     visit_node loc g Hg imap Himapg cs fuel hist Himaph cur Hcur Himapc acc = Result.Ok (cs', acc')) \/
  (exists l1 l2,
     l1 <> [] /\ map (Hashtable.find_opt imap) l1 = map Some l2 /\
     (exists r1 r2 l11 l12, l1 = l11 ++ r2 :: l12 ++ [r2] /\ accessibility_witness g r1 (tl l1) r2) /\
     visit_node loc g Hg imap Himapg cs fuel hist Himaph cur Hcur Himapc acc = Result.Err [(loc, Result.CyclicDependency l2)]).
Proof using.
  intros loc g Hg imap Himapg cs fuel hist Himaph cur Hcur1 Himapc acc eqfuel Hcoh Hcur2 Hacc Hhist.
  revert cs hist Himaph cur Hcur1 Hcur2 Himapc acc eqfuel Hcoh Hacc Hhist; induction fuel as [|fuel IH];
    intros cs hist Himaph cur Hcur1 Hcur2 Himapc acc eqfuel Hcoh Hacc Hhist.
  1: inversion eqfuel.
  match goal with |- (exists _ _, _ /\ _ /\ _ /\ _ /\ _ /\ ?f0 = _) \/ _ => remember f0 as f eqn:eqf end.
  cbn in eqf.
  destruct (Array.get cs cur) eqn:eqcol.
  2:{
    right; subst.
    refine (ex_intro _ (rev (cur :: hist)) (ex_intro _ _ (conj _ (conj _ (conj _ eq_refl))))).
    1: cbn; destruct (rev hist); discriminate.
    1:{
      rewrite (eq_refl : rev _ ++ [_] = rev (_ :: _)).
      rewrite !map_rev; refine (f_equal (@rev _) _).
      cbn; refine (f_equal2 cons (Hashtable.find_opt_In _ _ _) _).
      clear.
      match goal with |- _ = map _ (map_in _ ?f0) => pose (f := f0); fold f end.
      assert (tmp : forall v Hv, Hashtable.find_opt imap v = Some (f v Hv))
       by (intros v Hv; exact (Hashtable.find_opt_In _ _ _)).
      generalize dependent f; intros f Hf; clear - Hf.
      induction hist as [|hd tl IH]; [exact eq_refl|cbn; refine (f_equal2 cons (Hf _ _) (IH _ (fun v Hv => Hf _ (or_intror Hv))))].
    }
    exists (hd cur (rev hist)), cur.
    specialize (in_split _ _ (proj1 (in_rev _ _) (proj1 (proj1 (proj2 (proj2 (proj2 Hcoh))) cur Hcur1) eqcol))) as [l11 [l12 Heq]].
    exists l11, l12.
    split; [|exact (coherent_is_witness _ _ _ Hcur2)].
    cbn; rewrite (app_assoc _ (_ :: _) _ : _ ++ _ :: _ ++ _ = _); exact (f_equal (fun v => v ++ _) Heq).
  }
  2: left; subst; exact (ex_intro _ _ (ex_intro _ _ (conj Hcoh (conj eqcol (conj (fun _ h => h) (conj Hacc (conj (fun _ h => h) eq_refl))))))).
  match type of eqf with _ = Result.bind (visit_node_inner _ _ _ ?cs0 _ ?P0 _) _ => remember cs0 as cs' eqn:eqcs; remember P0 as P eqn:eqP end.
  clear eqP.
  specialize (Hg _ Hcur1) as Hneighslt.
  specialize (Himapg _ Hcur1) as Hneighsin.
  remember (Array.get g cur) as neighs eqn:eqneighs.
  assert (Hneighs: incl neighs (Array.get g cur)) by (subst neighs; exact (fun _ h => h)).
  specialize (fun cs acc v (Hcur : v < Array.length g /\ Hashtable.InMap v imap) H1 Hfuel =>
    IH cs (cur :: hist) (Forall_cons cur Himapc Himaph) v
      (proj1 Hcur)
      (conj (Hneighs _ H1) Hcur2 : In v (Array.get g cur) /\ coherent_hist g hist cur)
      (proj2 Hcur)
      acc
      Hfuel).
  assert (Hother_neighs: Forall (fun v => ~ In v neighs -> Array.get cs' v = Black) (Array.get g cur))
    by (subst neighs; apply Forall_forall; exact (fun _ h f => False_ind _ (f h))).
  assert (Hcoh': coherent_coloring g (cur :: hist) cs').
  1:{ subst cs'; destruct Hcoh as (H1 & H2 & H3 & H4 & H5); split; repeat match goal with |- _ /\ _ => split end.
    1: rewrite Array.length_set; exact H1.
    1: refine (NoDup_cons _ _ H2).
    1:  rewrite <-(H4 _ Hcur1); rewrite eqcol; discriminate.
    1: intros v [<-|Hv]; [exact Hcur1|exact (proj1 (Forall_forall _ _) Hhist _ Hv)].
    1: intros v Hv; destruct (PeanoNat.Nat.eq_dec cur v) as [->|curnev].
    1:  split; [intros _; left; exact eq_refl|intros _; exact (Array.get_set_same _ _ _ (eq_ind _ (lt v) Hcur1 _ H1))].
    1:  rewrite (Array.get_set_other _ _ _ _ (eq_ind _ (lt cur) Hcur1 _ H1) curnev), (H4 _ Hv).
    1: split; [intros h; right; exact h|intros [f2|h]; [contradiction (curnev f2)|exact h]].
    intros v Hv1 Hv2; destruct (PeanoNat.Nat.eq_dec cur v) as [->|curnev].
    1: rewrite (Array.get_set_same _ _ _ (eq_ind _ (lt v) Hcur1 _ H1)) in Hv2; discriminate Hv2.
    rewrite (Array.get_set_other _ _ _ _ (eq_ind _ (lt cur) Hcur1 _ H1) curnev) in Hv2.
    specialize (H5 v Hv1 Hv2).
    refine (conj (proj1 H5) _).
    intros w Hw.
    destruct (PeanoNat.Nat.eq_dec cur w) as [->|curnew].
    2: rewrite (Array.get_set_other _ _ _ _ (eq_ind _ (lt cur) Hcur1 _ H1) curnew); exact (proj2 H5 _ Hw).
    apply proj2 in H5; specialize (H5 w Hw); rewrite H5 in eqcol; discriminate eqcol.
  }
  assert (Hcoh_visit : forall i, Array.get cs i = Black -> Array.get cs' i = Black).
  1:{ subst cs'.
    intros v H.
    refine (eq_trans (Array.get_set_other _ _ _ _ (eq_ind _ (lt _) Hcur1 _ (proj1 Hcoh)) _) H).
    intros ->; rewrite eqcol in H; discriminate H.
  }
  assert (Hacc' : correct_sort_result g cs' acc).
  1:{ refine (conj (proj1 Hacc) (conj (proj1 (proj2 Hacc)) _)); subst cs'.
    intros k Hk1; split.
    - intros Hk2; refine (proj1 (proj2 (proj2 Hacc) k Hk1) _); rewrite (proj1 Hcoh) in Hcur1.
      refine (eq_trans (eq_sym (Array.get_set_other _ _ _ _ Hcur1 _)) Hk2).
      intros ->; rewrite (Array.get_set_same _ _ _ Hcur1) in Hk2; discriminate Hk2.
    - intros Hk2; rewrite <-(proj2 (proj2 (proj2 Hacc) k Hk1) Hk2); rewrite (proj1 Hcoh) in Hcur1.
      refine (Array.get_set_other _ _ _ _ Hcur1 _).
      intros ->; rewrite <-(proj2 (proj2 Hacc) k Hk1), eqcol in Hk2; discriminate Hk2.
  }
  clear Hacc.
  clear eqneighs eqcol eqcs; rename cs into cs0, Hcoh into Hcoh0.
  revert cs' Hcoh_visit Hother_neighs Hcoh' acc IH eqf Hacc'; induction neighs as [|hd tl IHn];
    intros cs Hcoh_visit Hother_neighs Hcoh acc IH eqf Hacc.
  - subst f; left; refine (ex_intro _ _ (ex_intro _ (_ :: _) (conj _ (conj _ (conj _ (conj _ (conj (fun _ h => or_intror h) eq_refl))))))).
    2: refine (Array.get_set_same _ _ _ _); rewrite <-(proj1 Hcoh); exact Hcur1.
    2: intros v Hv; destruct (PeanoNat.Nat.eq_dec cur v) as [->|curnev].
    2:  exact (Array.get_set_same _ _ _ (eq_ind _ (lt _) Hcur1 _ (proj1 Hcoh))).
    2: exact (eq_trans (Array.get_set_other _ _ _ _ (eq_ind _ (lt _) Hcur1 _ (proj1 Hcoh)) curnev) (Hcoh_visit v Hv)).
    2:{ split; [split; [split; [|exact (proj1 (proj1 Hacc))]|refine (NoDup_cons _ _ (proj2 (proj1 Hacc)))]|split].
      2: rewrite <-(proj2 (proj2 Hacc) _ Hcur1), (proj2 (proj1 (proj2 (proj2 (proj2 Hcoh))) _ Hcur1) (or_introl eq_refl)); discriminate.
      2: intros ? [->|Hk]; [exact Hcur1|exact (proj1 (proj2 Hacc) _ Hk)].
      1: apply Forall_forall; intros v Hv; refine (proj1 (proj2 (proj2 Hacc) _ _) _); [exact (proj1 (Forall_forall _ _) (Hg _ Hcur1) _ Hv)|].
      1:  exact (proj1 (Forall_forall _ _) Hother_neighs _ Hv (fun f => f)).
      intros k Hk1; split; intros Hk2.
      1: destruct (PeanoNat.Nat.eq_dec cur k) as [cureqk|curnek]; [left; exact cureqk|right; refine (proj1 (proj2 (proj2 Hacc) k Hk1) _)].
      1: exact (eq_trans (eq_sym (Array.get_set_other _ _ _ _ (eq_ind _ (lt _) Hcur1 _ (proj1 Hcoh)) curnek)) Hk2).
      destruct (PeanoNat.Nat.eq_dec cur k) as [->|curnek].
      1: exact (Array.get_set_same _ _ _ (eq_ind _ (lt _) Hk1 _ (proj1 Hcoh))).
      destruct Hk2 as [e|kinacc].
      1: contradiction (curnek e).
      rewrite <-(proj2 (proj2 (proj2 Hacc) k Hk1) kinacc); exact (Array.get_set_other _ _ _ _ (eq_ind _ (lt _) Hcur1 _ (proj1 Hcoh)) curnek).
    }
    destruct Hcoh as (h1 & h2 & h3 & h4 & h5).
    split; [rewrite Array.length_set; exact h1|].
    split; [exact (proj2 (proj1 (NoDup_cons_iff _ _) h2))|].
    split; [exact (fun v Hv => h3 v (or_intror Hv))|].
    split.
    + intros v Hv; split.
      1: intros h; assert (curnev : cur <> v).
      1:  intros ->; rewrite (Array.get_set_same _ _ _ (eq_ind _ (lt _) Hcur1 _ h1)) in h; discriminate h.
      1: rewrite (Array.get_set_other _ _ _ _ (eq_ind _ (lt _) Hcur1 _ h1) curnev) in h.
      1: apply (h4 _ Hv) in h as h'; destruct h' as [f|h']; [contradiction (curnev f)|exact h'].
      intros h.
      refine (eq_trans (Array.get_set_other _ _ _ _ (eq_ind _ (lt _) Hcur1 _ h1) _) (proj2 (h4 _ Hv) (or_intror h))).
      intros ->; exact (proj1 (proj1 (NoDup_cons_iff _ _) h2) h).
    + intros v Hv1 Hv2.
      assert (tmp : (forall w, In w (Array.get g v) -> Array.get cs w = Black) ->
                    (forall w, In w (Array.get g v) -> Array.get (Array.set cs cur Black) w = Black)).
      1: intros h w Hw; destruct (PeanoNat.Nat.eq_dec cur w) as [<-|curnew]; [exact (Array.get_set_same _ _ _ (eq_ind _ (lt _) Hcur1 _ h1))|].
      1: exact (eq_trans (Array.get_set_other _ _ _ _ (eq_ind _ (lt _) Hcur1 _ h1) curnew) (h w Hw)).
      destruct (PeanoNat.Nat.eq_dec cur v) as [<-|curnev]; [|refine (match h5 v Hv1 _ with conj h1 h2 => conj h1 (tmp h2) end)].
      2: exact (eq_trans (eq_sym (Array.get_set_other _ _ _ _ (eq_ind _ (lt _) Hcur1 _ h1) curnev)) Hv2).
      assert (neigh_black := fun v Hv => proj1 (Forall_forall _ _) Hother_neighs v Hv (fun f => f)).
      split; [|exact (tmp neigh_black)].
      assert (neigh_no_cycle := fun v Hv => proj1 (h5 v (proj1 (Forall_forall _ _) (Hg _ Hcur1) v Hv) (neigh_black v Hv))).
      intros [cycle_root [[|nr] [nc [Ha Hc]]]]; inversion Ha as [eq1 eq2|? nxt ? Hnxt_neigh Ha2]; [subst; clear eq2 Ha|subst].
      2: exact (neigh_no_cycle nxt Hnxt_neigh (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj Ha2 Hc))))).
      apply has_cycle_accessible in Hc as Ha; apply accessible_iff_witness in Ha; destruct Ha as [[|hd tl] [Hl1 Hl2]]; [discriminate Hl1|].
      refine (neigh_no_cycle hd (proj1 Hl2) _).
      injection Hl1 as Hl1.
      exists cur, nc, nc; split; [apply accessible_iff_witness; exists tl; exact (conj Hl1 (proj2 Hl2))|exact Hc].
  - cbn in eqf.
    assert (IH0 := IH).
    assert (Hfuel : white_count cs < fuel).
    1:{
      refine (PeanoNat.Nat.le_trans _ _ _ _ (le_S_n _ _ eqfuel)).
      clear - Hcoh Hcoh0 Hcoh_visit Hcur1.
      unfold white_count.
      assert (Hlen := eq_trans (eq_sym (proj1 Hcoh0)) (proj1 Hcoh)).
      rewrite <-(proj1 Hcoh0), <-(proj1 Hcoh); remember (Array.length g) as n eqn:eqn.
      assert (Hn := eq_ind _ _ (le_n _) _ (eq_trans eqn (proj1 Hcoh)) : n <= Array.length _).
      destruct Hcoh0 as (_ & _ & _ & h1 & _).
      destruct Hcoh as (eqleng & curninhist & _ & h2 & _).
      apply NoDup_cons_iff, proj1 in curninhist.
      rewrite eqleng in h1, h2.
      refine (eq_ind _ (fun b : bool => if b then _ else white_count_inner cs n <= white_count_inner cs0 n)
                _ _ (proj2 (PeanoNat.Nat.ltb_lt _ _) Hcur1)).
      clear g eqn eqleng Hcur1.
      induction n as [|n IH]; [exact (le_n _)|cbn].
      specialize (IH (le_S_n _ _ (le_S _ _ Hn))).
      specialize (PeanoNat.Nat.le_gt_cases cur n) as [curlen|curgtn].
      1: rewrite (proj2 (PeanoNat.Nat.leb_le _ _) curlen); apply PeanoNat.Nat.lt_eq_cases in curlen; destruct curlen as [curltn| ->].
      - rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _) curltn) in IH.
        destruct (Array.get cs0 n) eqn:eqcn.
        3: rewrite (Hcoh_visit _ eqcn); exact IH.
        2: rewrite (proj2 (h2 n Hn) (or_intror (proj1 (h1 n Hn) eqcn))); exact IH.
        destruct (Array.get cs n); try exact (le_S _ _ IH); exact (le_n_S _ _ IH).
      - rewrite PeanoNat.Nat.ltb_irrefl in IH.
        rewrite (proj2 (h2 _ Hn) (or_introl eq_refl)).
        destruct (Array.get cs0 n) eqn:eqcn; [exact (le_n_S _ _ IH)|exfalso|exfalso].
        1: rewrite (h1 _ Hn) in eqcn; exact (curninhist eqcn).
        apply Hcoh_visit in eqcn; rewrite (proj2 (h2 _ Hn) (or_introl eq_refl)) in eqcn.
        discriminate eqcn.
      - rewrite (proj2 (Compare_dec.leb_iff_conv _ _) curgtn).
        rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _) (le_S_n _ _ (le_S _ _ curgtn))) in IH.
        destruct (Array.get cs0 n) eqn:eqcn.
        3: rewrite (Hcoh_visit _ eqcn); exact IH.
        2: rewrite (proj2 (h2 n Hn) (or_intror (proj1 (h1 n Hn) eqcn))); exact IH.
        destruct (Array.get cs n); try exact (le_S _ _ IH); exact (le_n_S _ _ IH).
    }
    specialize (IH cs acc hd (Forall_inv P) (or_introl eq_refl) Hfuel Hcoh Hacc (Forall_cons (P:=fun v => v < _) _ Hcur1 Hhist)).
    clear Hacc.
    destruct (List_mem_vertex hd (cur :: hist)) as [|] eqn:eqmem.
    + destruct fuel as [|fuel]; [inversion Hfuel|]; cbn in IH, eqf.
      apply mem_vertex_wd in eqmem.
      rewrite (proj2 (proj1 (proj2 (proj2 (proj2 Hcoh))) hd
                        (proj1 (Forall_forall _ _) (Forall_cons (P:=fun v => v < _) _ Hcur1 Hhist) _ eqmem)) eqmem)
        in IH, eqf.
      cbn in IH, eqf; subst; right.
      destruct IH as [[? [? [_ [_ [_ [_ [_ f]]]]]]]|IH]; [discriminate f|exact IH].
    + assert (hdnin := (fun h => eq_ind false (fun b => match b with false => True | true => False end) I _
                       (eq_trans (eq_sym eqmem) (proj2 (mem_vertex_wd hd (cur :: hist)) h))) : ~ In _ _).
      destruct IH as [[cs' [acc' [Hcoh' [IH1 [IH2 [IHacc [IHincl IH3]]]]]]]|[l1 [l2 [Hl1 [Hl2 [Hacc eqv]]]]]].
      2: right; exists l1, l2; split; [exact Hl1|split; [exact Hl2|split; [exact Hacc|]]].
      2: exact (eq_trans eqf (f_equal (fun v => Result.bind (Result.bind v _) _) eqv)).
      assert (eqf' := eq_trans eqf (f_equal (fun v => Result.bind (Result.bind v _) _) IH3)); clear eqf; rename eqf' into eqf.
      cbn in eqf.
      refine (match IHn (Forall_inv_tail P) (Forall_inv_tail Hneighslt) (Forall_inv_tail Hneighsin) (fun _ h => Hneighs _ (or_intror h)) cs'
        (fun v Hv => IH2 v (Hcoh_visit v Hv)) _ Hcoh' _ (fun _ _ _ _ h => IH0 _ _ _ _ (or_intror h)) eqf IHacc
        with or_intror h => or_intror h
        | or_introl (ex_intro _ w1 (ex_intro _ w2 (conj h1 (conj h2 (conj h3 (conj h4 (conj h5 h6))))))) =>
          or_introl (ex_intro _ w1 (ex_intro _ w2 (conj h1 (conj h2 (conj h3 (conj h4 (conj (fun _ h => h5 _ (IHincl _ h)) h6)))))))
        end).
      clear - IH1 IH2 Hother_neighs Hcoh'; apply Forall_forall; intros v Hv1 Hv2.
      rewrite Forall_forall in Hother_neighs.
      specialize (fun h : _ <> _ => IH2 _ (Hother_neighs v Hv1 (fun f => match f with or_introl f => h f | or_intror f => Hv2 f end))).
      destruct (PeanoNat.Nat.eq_dec hd v) as [->|hdnev]; [exact IH1|exact (IH2 hdnev)].
Qed.

Fixpoint topological_sort_inner (loc: Result.location)
  (g: graph) (Hg : forall k, k < Array.length g -> Forall (fun v => v < Array.length g) (Array.get g k))
  (imap: Hashtable.t vertex ident) (Himap : forall k, k < Array.length g -> Hashtable.InMap k imap)
  (cs: Array.t color)
  (cur: vertex) (Hcur : cur < Array.length g)
  (acc: list vertex) {struct cur}: Result.t Source.type (Array.t color * list vertex).
Proof using.
  assert (Himap' : forall k, k < Array.length g -> Forall (fun v => Hashtable.InMap v imap) (Array.get g k)).
  1:{
    intros k Hk; apply Forall_forall; intros v Hv.
    exact (Himap _ (proj1 (Forall_forall _ _) (Hg _ Hk) _ Hv)).
  }
  assert (Himapc := Himap _ Hcur : Hashtable.InMap cur imap).
  pose (ret := visit_node loc g Hg imap Himap' cs (S (S cur)) [] (Forall_nil _) cur Hcur Himapc acc).
  destruct cur as [|cur].
  1: exact ret.
  refine (Result.bind ret _); clear Himap' Himapc ret cs acc.
  intros [cs acc].
  assert (Hcur' := le_S_n _ _ (le_S _ _ Hcur) : cur < _).
  refine (topological_sort_inner loc g Hg imap Himap cs cur Hcur' acc).
Defined.

Definition topological_sort_inner_eq : forall loc (g: graph) Hg imap Himap cs cur Hcur acc,
  topological_sort_inner loc g Hg imap Himap cs cur Hcur acc =
  match cur as n return
    Result.t Source.type (Array.t color * list vertex) ->
    n < Array.length g -> Hashtable.InMap n imap ->
    Result.t Source.type (Array.t color * list vertex) with
  | O => fun v _ _ => v
  | S n => fun v Hcur0 Himapc0 =>
      Result.bind v (fun ret => let (t, l) := ret in let Hcur' := le_S_n _ _ (le_S _ _ Hcur0) in topological_sort_inner loc g Hg imap Himap t n Hcur' l)
  end
  (visit_node loc g Hg imap _ cs (S (S cur)) [] (Forall_nil (fun v : vertex => Hashtable.InMap v imap)) cur Hcur (Himap cur Hcur) acc)
  Hcur (Himap cur Hcur)
:= ltac:(intros; destruct cur; exact eq_refl).

Lemma white_count_inner_le cs n: white_count_inner cs n <= n.
Proof using.
  induction n as [|n IHn]; [exact (le_n _)|cbn; destruct (Array.get cs n); try exact (le_S _ _ IHn); exact (le_n_S _ _ IHn)].
Qed.

Lemma limit_white_count (g: graph) cs n:
  Array.length g = Array.length cs ->
  (forall k, n <= k < Array.length g -> Array.get cs k = Black) -> white_count cs <= n.
Proof using.
  intros eqlen H; unfold white_count.
  specialize (eq_ind_r (le _) (le_n _) eqlen) as Hk; clear eqlen.
  induction (Array.length cs) as [|k IH]; [exact (le_0_n _)|].
  destruct (PeanoNat.Nat.le_gt_cases (S k) n) as [Sklen|Skgtn]; [exact (PeanoNat.Nat.le_trans _ _ _ (white_count_inner_le _ _) Sklen)|cbn].
  rewrite (H _ (conj (le_S_n _ _ Skgtn) Hk)).
  exact (IH (le_S_n _ _ (le_S _ _ Hk))).
Qed.

Lemma topological_sort_inner_prop : forall loc (g: graph) Hg imap Himap cs cur Hcur acc,
  coherent_coloring g [] cs ->
  correct_sort_result g cs acc ->
  (forall k, cur < k < Array.length g -> In k acc /\ Array.get cs k = Black) ->
  match topological_sort_inner loc g Hg imap Himap cs cur Hcur acc with
  | Result.Ok (cs', s) =>
      coherent_coloring g [] cs' /\
      correct_sort_result g cs' s /\
      (forall k, k < Array.length g <-> In k s) /\
      (forall k, k < Array.length g -> Array.get cs' k = Black)
  | Result.Err e =>
      exists l1 l2,
      l1 <> [] /\ map (Hashtable.find_opt imap) l1 = map Some l2 /\
      (exists r1 r2 l11 l12, l1 = l11 ++ r2 :: l12 ++ [r2] /\ accessibility_witness g r1 (tl l1) r2) /\
      e = [(loc, Result.CyclicDependency l2)]
  end.
Proof using.
  intros loc g Hg imap Himap cs cur Hcur acc H1 H2 H3.
  revert cur Hcur cs acc H1 H2 H3; fix IH 1; intros cur Hcur cs acc H1 H2 H3.
  rewrite topological_sort_inner_eq.
  match goal with |- match match _ with _ => _ end (visit_node _ _ _ _ ?himap _ _ _ _ _ _ _ _) _ _ with _ => _ end =>
    remember himap as Himap' eqn:eqhimap end.
  specialize (visit_node_prop loc g Hg imap Himap' cs (S (S cur)) [] (Forall_nil _) cur Hcur (Himap cur Hcur) acc) as tmp.
  specialize (tmp (le_n_S _ _ (limit_white_count _ _ _ (proj1 H1) (fun k Hk => proj2 (H3 k Hk)))) H1 I H2 (Forall_nil _))
    as [[cs' [acc' (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6)]]|[l1 [l2 (Hl1 & Hl2 & Hc & Heq)]]].
  - rewrite Hc6; cbn.
    destruct cur as [|n]; [split; [|split; [|split]]; try assumption|cbn].
    + intros k; split.
      2: exact (proj1 (proj2 Hc4) _).
      destruct k as [|k]; intros Hk.
      2: specialize (H3 (S k) (conj (le_n_S _ _ (le_0_n _)) Hk)); exact (Hc5 _ (proj1 H3)).
      exact (proj1 (proj2 (proj2 Hc4) _ Hk) Hc2).
    + intros [|k] Hk.
      2: specialize (H3 (S k) (conj (le_n_S _ _ (le_0_n _)) Hk)); exact (Hc3 _ (proj2 H3)).
      exact Hc2.
    + refine (IH n (le_S_n _ _ (le_S _ _ Hcur)) cs' acc' Hc1 Hc4 _).
      intros k [Hk1 Hk2].
      inversion Hk1 as [|? Hk1']; subst.
      1: exact (conj (proj1 (proj2 (proj2 Hc4) _ Hk2) Hc2) Hc2).
      specialize (H3 _ (conj (le_n_S _ _ Hk1') Hk2)) as [H31 H32].
      exact (conj (Hc5 _ H31) (Hc3 _ H32)).
  - rewrite Heq; destruct cur; cbn; exists l1, l2; (split; [|split; [|split]]); try assumption; exact eq_refl.
Qed.

Definition topological_sort (loc: Result.location)
  (g: graph) (Hg : forall k, k < Array.length g -> Forall (fun v => v < Array.length g) (Array.get g k))
  (imap: Hashtable.t vertex ident) (Himap : forall k, k < Array.length g -> Hashtable.InMap k imap)
  : Result.t Source.type (list vertex).
Proof using.
  pose (n := Array.length g).
  assert (Hn := le_n n : n <= Array.length g).
  destruct n as [|n]; [exact (Result.Ok [])|].
  pose (visited := Array.make (S n) White).
  refine (Result.bind (topological_sort_inner loc g Hg imap Himap visited n Hn []) _); clear.
  intros [_ ret]; exact (Result.Ok ret).
Defined.

Lemma topological_sort_prop : forall loc (g: graph) Hg imap Himap,
  match topological_sort loc g Hg imap Himap with
  | Result.Ok s => correct_sort_result' g s /\ forall k, k < Array.length g <-> In k s
  | Result.Err e =>
      exists l1 l2,
      l1 <> [] /\ map (Hashtable.find_opt imap) l1 = map Some l2 /\
      (exists r1 r2 l11 l12, l1 = l11 ++ r2 :: l12 ++ [r2] /\ accessibility_witness g r1 (tl l1) r2) /\
      e = [(loc, Result.CyclicDependency l2)]
  end.
Proof using.
  intros loc g Hg imap Himap.
  unfold topological_sort.
  refine (match Array.length g as k return (k = Array.length g -> forall P : k <= Array.length g,
            match match k as n return n <= Array.length g -> _ with
              | O => fun _ => Result.Ok []
              | S n => _ end P
            with Result.Ok s => correct_sort_result' g s /\ _ | Result.Err e => _ end)
          with O => fun _ _ => conj (conj I (NoDup_nil _)) _ | S n => _ end eq_refl (le_n _)).
  1: rewrite <-e; intros ?; split; [intros f; inversion f|intros []].
  intros Heqn Hlen.
  specialize (topological_sort_inner_prop loc g Hg imap Himap (Array.make (S n) White) n Hlen []) as tmp.
  specialize (fun h2 => tmp (conj (eq_sym (eq_trans (Array.length_make _ _) Heqn)) (conj (NoDup_nil _) h2))).
  specialize (fun h1 h2 => tmp (conj (fun _ f => False_ind _ f) (conj h1 h2))).
  match type of tmp with ?p1 -> ?p2 -> ?p3 -> ?p4 -> _ => assert (tmp2 : (p1 /\ p2) /\ p3 /\ p4);
    [split; split|specialize (tmp (proj1 (proj1 tmp2)) (proj2 (proj1 tmp2)) (proj1 (proj2 tmp2)) (proj2 (proj2 tmp2))); clear tmp2] end.
  1: intros v Hv; split; [intros f; rewrite Heqn, (Array.get_make _ _ _ Hv) in f; discriminate f|intros []].
  1: intros v Hv f; rewrite Heqn, (Array.get_make _ _ _ Hv) in f; discriminate f.
  1: split; [split; [exact I|exact (NoDup_nil _)]|split; [intros ? []|]].
  1: intros v Hv; split; [intros f; rewrite Heqn, (Array.get_make _ _ _ Hv) in f; discriminate f|intros []].
  1: intros k [Hk1 Hk2]; contradict Hk1; rewrite <-Heqn in Hk2; apply PeanoNat.Nat.nlt_ge; exact (le_S_n _ _ Hk2).
  match type of tmp with match ?v with _ => _ end => destruct v as [[cs' ret]|e] end; cbn.
  2: exact tmp.
  split; [exact (proj1 (proj1 (proj2 tmp)))|].
  exact (proj1 (proj2 (proj2 tmp))).
Qed.

Lemma in_map_in_iff : forall [A B] l (f : forall x : A, In x l -> B) y,
  In y (map_in l f) <-> exists x Hx, f x Hx = y.
Proof using.
  intros A B l f y; split; revert f; induction l as [|hd tl IH]; intros f.
  - intros [].
  - intros [H|H]; [exact (ex_intro _ _ (ex_intro _ _ H))|].
    destruct (IH _ H) as [x [Hx Hy]]; exists x, (or_intror Hx); exact Hy.
  - intros [x [[] _]].
  - intros [x [[->|Hx] Hy]]; [left; exact Hy|right; apply IH].
    exists x, Hx; exact Hy.
Qed.

Lemma ident_types_same : forall source i ty1 ty2,
  In (i, ty1) source.(Source.n_vars) ->
  In (i, ty2) (source.(Source.n_in) ++ source.(Source.n_assigned_vars)) ->
  ty1 = ty2.
Proof using.
  intros source i ty1 ty2 H1 H2.
  rewrite source.(Source.n_vars_all_assigned) in H2.
  fold source.(Source.n_vars) in H2.
  assert (Hd := source.(Source.n_vars_unique)).
  remember source.(Source.n_vars) as l; clear - H1 H2 Hd.
  induction l as [|hd tl IH].
  1: contradiction H1.
  cbn in *; apply NoDup_cons_iff in Hd; specialize (fun H1 H2 => IH H1 H2 (proj2 Hd)); apply proj1 in Hd.
  destruct H1 as [->|H1], H2 as [H2|H2]; [injection H2 as e; exact e|contradict Hd|subst; contradict Hd|exact (IH H1 H2)]; cbn.
  1: exact (in_map _ _ _ H2).
  1: exact (in_map _ _ _ H1).
Qed.

Definition translate_node (source: Source.node): Result.t Lustre.type Target.node_ordered.
Proof using.
  unshelve refine (
    match node_to_graph source with (graph, index_table) => fun Heqg =>
    let props := node_to_graph_prop source graph index_table Heqg in
    do ord_graph remember eqgraph <- topological_sort source.(Source.n_loc) graph _ index_table _;
    Result.Ok (
      let new_order := map_in ord_graph _ in
      let sorted_new_order := reorder_list source.(Source.n_body) new_order _ in
      check_order source sorted_new_order _ _
    )
    end eq_refl
  ).
  - intros k Hk; rewrite (proj1 props); exact (graph_prop_is_graph_wd props k Hk).
  - intros k Hk; rewrite (proj1 props), <-(proj1 (proj2 props)) in Hk; exact Hk.
  - intros v Hv; refine (Hashtable.find index_table v _).
    match type of eqgraph with topological_sort ?loc ?g ?Hg ?imap ?Himap = _ =>
      specialize (topological_sort_prop loc g Hg imap Himap) as tmp end.
    specialize (eq_ind _ (fun v => match v with Result.Ok s => _ | Result.Err e => _ end) tmp _ eqgraph) as Hgraph;
      cbn in Hgraph; clear tmp.
    rewrite (proj1 (proj2 props)), <-(proj1 props).
    exact (proj2 (proj2 Hgraph _) Hv).
  - intros i Hi.
    apply in_map_in_iff in Hi; destruct Hi as [v [Hv Hi]].
    refine (eq_ind _ (In _) (eq_ind _ (fun v => In v _) (proj1 (proj2 (proj2 (proj2 props))) _ _) _ Hi) _ _).
    clear; unfold Source.n_assigned_vars.
    exact (map_map _ _ _).
  - assert (nodup_body : NoDup (map fst (Source.n_body source))).
    1:{
      assert (Hvars := source.(Source.n_vars_unique)); rewrite <-(map_map Source.equation_dest fst);
        change (map Source.equation_dest source.(Source.n_body)) with source.(Source.n_assigned_vars); clear - Hvars.
      rewrite source.(Source.n_vars_all_assigned); unfold Source.n_vars in Hvars.
      rewrite map_app in Hvars; exact (NoDup_app_remove_l _ _ Hvars).
    }
    match type of eqgraph with topological_sort ?loc ?g ?Hg ?imap ?Himap = _ =>
      specialize (topological_sort_prop loc g Hg imap Himap) as tmp end.
    specialize (eq_ind _ (fun v => match v with Result.Ok s => _ | Result.Err e => _ end) tmp _ eqgraph) as Hgraph;
      cbn in Hgraph; clear tmp.
    refine (reorder_list_prop _ _ _ nodup_body _).
    clear sorted_new_order.
    refine (NoDup_Permutation nodup_body _ _).
    + assert (tmp : forall A B l (f: forall x : A, In x l -> B),
        NoDup l -> (forall x Hx y Hy, x <> y -> f x Hx <> f y Hy) -> NoDup (map_in l f)); [clear|refine (tmp _ _ _ _ _ _); clear tmp].
      * intros A B l; induction l as [|hd tl IH]; intros f Hl Hf.
        1: exact (NoDup_nil _).
        refine (NoDup_cons _ _ (IH _ (proj2 (proj1 (NoDup_cons_iff _ _) Hl)) (fun x Hx y Hy => Hf x (or_intror Hx) y (or_intror Hy)))).
        intros Hin.
        apply in_map_in_iff in Hin; destruct Hin as [y [Hy H]].
        refine (Hf _ _ _ _ _ H).
        intros ->; exact (proj1 (proj1 (NoDup_cons_iff _ _) Hl) Hy).
      * clear new_order.
        exact (proj2 (proj1 Hgraph)).
      * intros x Hx0 y Hy0 xney; match goal with |- Hashtable.find _ _ ?hx <> Hashtable.find _ _ ?hy =>
          assert (Hx := hx); assert (Hy := hy); rewrite (Hashtable.find_ext _ _ _ Hx), (Hashtable.find_ext _ _ _ Hy) end.
        clear nodup_body new_order eqgraph ord_graph Hx0 Hy0 Hgraph.
        intros Himg.
        exact (xney (proj1 (proj2 (proj2 props)) _ _ _ _ Himg)).
    + intros i; split; intros Hi.
      * apply in_map_iff in Hi; destruct Hi as [[i' [ty e]] [[=->] Hi]].
        specialize (proj1 (proj2 (proj2 (proj2 (proj2 props)))) (i, ty) (in_map Source.equation_dest _ _ Hi)) as [v Hv]; cbn in Hv.
        specialize (proj1 (proj1 (proj2 props) v)) as tmp; rewrite <-(proj1 props) in tmp.
        specialize (proj1 (proj2 Hgraph v) (tmp (Hashtable.find_opt_Some_In _ _ _ Hv))) as vin; clear tmp.
        apply in_map_in_iff; exists v, vin.
        refine (f_equal (fun o => match o with Some v => v | None => i end) (x := Some _) (y := Some i) _).
        exact (eq_trans (eq_sym (Hashtable.find_opt_In _ _ _)) Hv).
      * apply in_map_in_iff in Hi; destruct Hi as [v [Hv Hi]].
        match type of Hi with Hashtable.find _ _ ?h = _ =>
          specialize (proj1 (proj2 (proj2 (proj2 props))) v h) as tmp; rewrite Hi in tmp end; clear Hi.
        exact (eq_ind _ (In _) tmp _ (map_map _ _ _)).
  - cbn.
    assert (nodup_body : NoDup (map fst (Source.n_body source))).
    1:{
      assert (Hvars := source.(Source.n_vars_unique)); rewrite <-(map_map Source.equation_dest fst);
        change (map Source.equation_dest source.(Source.n_body)) with source.(Source.n_assigned_vars); clear - Hvars.
      rewrite source.(Source.n_vars_all_assigned); unfold Source.n_vars in Hvars.
      rewrite map_app in Hvars; exact (NoDup_app_remove_l _ _ Hvars).
    }
    match type of eqgraph with topological_sort ?loc ?g ?Hg ?imap ?Himap = _ =>
      specialize (topological_sort_prop loc g Hg imap Himap) as tmp end.
    specialize (eq_ind _ (fun v => match v with Result.Ok s => _ | Result.Err e => _ end) tmp _ eqgraph) as Hgraph;
      cbn in Hgraph; clear tmp.
    match type of (eq_refl : sorted_new_order = reorder_list _ _ _) with _ = reorder_list _ _ ?h =>
      assert (Hsrt := h); rewrite (reorder_list_ext _ _ _ Hsrt : sorted_new_order = _); clear sorted_new_order end.
    match type of (eq_refl : new_order = map_in _ _) with _ = map_in _ (fun v Hv => Hashtable.find _ _ ?p) =>
      pose (Hord := fun v (Hv : In v ord_graph) => p);
        change new_order with (map_in ord_graph (fun v Hv => Hashtable.find index_table v (Hord v Hv)));
        change new_order with (map_in ord_graph (fun v Hv => Hashtable.find index_table v (Hord v Hv))) in Hsrt;
        clear new_order; generalize dependent Hord; intros Hord Hsrt end.
    clear eqgraph.
    destruct Hgraph as [[Hg1 Hg2] _].
    induction ord_graph as [|hdv tl IH].
    1: cbn; clear; assert (Hd := source.(Source.n_vars_unique) : NoDup (map fst (_ ++ _))).
    1: rewrite map_app in Hd; apply NoDup_app_remove_r in Hd; remember source.(Source.n_in) as l; clear - Hd.
    1: induction l as [|[i ty] tl IH]; [exact Ordered.nil|cbn in Hd; apply NoDup_cons_iff in Hd].
    1: refine (Ordered.append _ _ _ _ (IH (proj2 Hd)) _ (Forall_nil _)).
    1: rewrite map_map; exact (proj1 Hd).
    cbn in Hg1 |- *; destruct Hg1 as [Hhd Hg1].
    apply NoDup_cons_iff in Hg2.
    assert (tmp := Hsrt _ (or_introl eq_refl)); apply in_map_iff in tmp; destruct tmp as [[i [ty e]] [[=->] Hitye]].
    rewrite (find_in_prop _ _ _ _ nodup_body Hitye); cbn.
    refine (Ordered.append _ _ _ _ (IH Hg1 (proj2 Hg2) (fun v Hv => Hord v (or_intror Hv)) (fun v Hv => Hsrt v (or_intror Hv))) _ _).
    + rewrite map_app, map_map, in_app_iff; intros [H|H].
      2:{
        assert (tmp := source.(Source.n_vars_unique) : NoDup (map fst (_ ++ _))).
        apply (in_map fst) in Hitye; cbn in Hitye.
        remember (Hashtable.find _ _ (Hord _ (or_introl eq_refl))) as i; clear - Hitye tmp H.
        apply in_split in H; destruct H as [l1 [l2 H]].
        rewrite map_app, (H : map (fst : ident * Source.type -> _) _ = _), <-app_assoc in tmp.
        refine (NoDup_remove_2 l1 (l2 ++ map fst _) i tmp _); clear tmp.
        apply in_or_app, or_intror, in_or_app, or_intror; clear l1 l2 H.
        rewrite <-(Permutation_map _ source.(Source.n_vars_all_assigned)),
          (map_map _ _ _ : map (A:=Source.binder) fst source.(Source.n_assigned_vars) = map fst source.(Source.n_body)).
        exact Hitye.
      }
      rewrite Target.equations_to_dag_is_map, map_map in H.
      apply in_map_iff in H; destruct H as [[j [tyj ej]] [eqj Hj]].
      apply (in_reorder_list_iff _ _ _ _ _ nodup_body) in Hj; destruct Hj as [Hjty Hj].
      apply in_map_in_iff in Hj; destruct Hj as [v [Hv Hj]].
      refine (proj1 Hg2 (eq_ind _ (fun v => In v tl) Hv _ _)).
      exact (proj1 (proj2 (proj2 props)) _ _ _ _ (eq_trans Hj eqj)).
    + apply Forall_forall; intros [j tyj] Hjty.
      specialize (proj1 (Forall_forall _ _) (proj2 (proj2 (proj2 (proj2 (proj2 props))))) _ Hitye _ (Hashtable.find_opt_In _ _ _))
        as [incl1 incl2].
      specialize (incl2 _ (in_map _ _ _ Hjty)); cbn in incl2.
      apply in_app_or in incl2; destruct incl2 as [Hj|Hj].
      * rewrite map_map, in_map_iff in Hj; destruct Hj as [[? ty2] [[=->] Hj]]; exists []; apply in_or_app, or_intror.
        refine (in_map _ _ (j, tyj) (eq_ind _ (fun v => In (_, v) _) Hj _ _)).
        assert (jinvars := proj1 (Forall_forall _ _) source.(Source.n_all_vars_exist) _ Hitye _ Hjty); clear - Hj jinvars.
        exact (eq_sym (ident_types_same _ _ _ _ jinvars (in_or_app _ _ _ (or_introl Hj)))).
      * apply in_map_iff in Hj; destruct Hj as [v [eqv Hv]].
        specialize (proj1 (proj2 (proj2 (proj2 props))) _ (Hashtable.find_opt_Some_In _ _ _ eqv)) as tmp;
          rewrite (Hashtable.find_opt_Some_eq _ _ _ eqv), (map_map _ _ _ : map fst source.(Source.n_assigned_vars) = _) in tmp.
        cbn in tmp; apply in_map_iff in tmp; destruct tmp as [[? [tyj' ej]] [[=->] Hej]].
        exists (Source.var_of_exp ej); apply in_or_app; left; rewrite Target.equations_to_dag_is_map.
        refine (eq_ind _ (fun t => In (_, t, _) _) (in_map _ _ (j, existT Source.exp tyj' ej) _) _ _).
        1: refine (proj2 (in_reorder_list_iff _ _ _ _ _ nodup_body) (conj Hej _)).
        1: apply in_map_in_iff; exists v, (proj1 (Forall_forall _ _) Hhd _ Hv).
        1: apply Hashtable.find_opt_Some in eqv; destruct eqv as [tmp eqv]; exact (eq_trans (Hashtable.find_ext _ _ _ _) eqv).
        assert (jinvars := proj1 (Forall_forall _ _) source.(Source.n_all_vars_exist) _ Hitye _ Hjty); clear - Hej jinvars.
        apply (in_map (B:=ident * Source.type) Source.equation_dest) in Hej;
          fold source.(Source.n_assigned_vars) in Hej; unfold Source.equation_dest in Hej; cbn in Hej.
        exact (eq_sym (ident_types_same _ _ _ _ jinvars (in_or_app _ _ _ (or_intror Hej)))).
Defined.
