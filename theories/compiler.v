From Coq Require Export List Nat.
From Coq Require Export BinNums FMapPositive PArith.

Import ListNotations.
Open Scope positive.


Definition ident := positive.


Module Stream.

  CoInductive t (A: Type) :=
    | Cons: A -> t A -> t A.

  Arguments Cons {_} _ _.


  CoFixpoint from {A: Type} (x: A) : t A := Cons x (from x).

  CoFixpoint merge {A B C: Type} (f: A -> B -> C) (x: t A) (y: t B): t C :=
    match x, y with
    | Cons x xs, Cons y ys => Cons (f x y) (merge f xs ys)
    end.

  CoFixpoint map {A B: Type} (f: A -> B) (x: t A): t B :=
    match x with
    | Cons x xs => Cons (f x) (map f xs)
    end.

  Definition hd {A: Type} (s: t A): A :=
    match s with
    | Cons x _ => x
    end.

End Stream.


Module source.

  Inductive type :=
    | TBool.

  Definition binder := prod ident type.


  Inductive const :=
    | CBool: bool -> const.

  Inductive exp :=
    | EConst : const -> exp
    | EVar : binder -> exp
    | EAnd : exp -> exp -> exp
    | EOr : exp -> exp -> exp
    | EXor : exp -> exp -> exp.

  Definition equation := prod ident exp.


  Record node := mk_node {
    n_name: ident;

    n_in: list binder;
    n_out: binder;
    n_locals: list binder;

    n_body: list equation;

    n_vars: list binder := n_in ++ n_out :: n_locals;
    n_ident_uniq: NoDup (map fst n_vars);
  }.

  Definition value := const.
  Definition history := PositiveMap.t (Stream.t value).

  Definition sem_const (c: const): value := c.

  Inductive sem_exp: history -> exp -> Stream.t const -> Prop :=
    | SeConst (h: history) (c: const):
        sem_exp h (EConst c) (Stream.from (sem_const c))

    | SeVar (h: history) (b: binder) (s: Stream.t const):
        PositiveMap.MapsTo (fst b) s h ->
        sem_exp h (EVar b) s

    | SeAnd (h: history) (e1 e2: exp) (s1 s2 s: Stream.t bool):
        sem_exp h e1 (Stream.map (fun x => CBool x) s1) ->
        sem_exp h e2 (Stream.map (fun x => CBool x) s2) ->
        sem_exp h (EAnd e1 e2) (Stream.map (fun x => CBool x) (Stream.merge (fun x y => andb x y) s1 s2))

    | SeOr (h: history) (e1 e2: exp) (s1 s2 s: Stream.t bool):
        sem_exp h e1 (Stream.map (fun x => CBool x) s1) ->
        sem_exp h e2 (Stream.map (fun x => CBool x) s2) ->
        sem_exp h (EOr e1 e2) (Stream.map (fun x => CBool x) (Stream.merge (fun x y => orb x y) s1 s2))

    | SeXor (h: history) (e1 e2: exp) (s1 s2 s: Stream.t bool):
        sem_exp h e1 (Stream.map (fun x => CBool x) s1) ->
        sem_exp h e2 (Stream.map (fun x => CBool x) s2) ->
        sem_exp h (EXor e1 e2) (Stream.map (fun x => CBool x) (Stream.merge (fun x y => xorb x y) s1 s2)).

End source.


Module target.

  Inductive type :=
    | TBool.

  Definition binder := prod ident type.


  Inductive const :=
    | CBool: bool -> const.

  Inductive exp :=
    | EConst : const -> exp
    | EVar : binder -> exp
    | EAnd : exp -> exp -> exp
    | EOr : exp -> exp -> exp
    | EXor : exp -> exp -> exp.

  Inductive stmt :=
    | SAssign: ident -> exp -> stmt
    | SSeq : stmt -> stmt -> stmt
    | SReturn : exp -> stmt
    | SNop : stmt.


  Record method := mk_method {
    m_name: ident;

    m_in: list binder;
    m_out: type;
    m_vars: list binder;

    m_body: stmt;
  }.


  Definition stack := PositiveMap.t const.

  Inductive sem_exp: stack -> exp -> const -> Prop :=
    | SeConst (s: stack) (c: const):
        sem_exp s (EConst c) c

    | SeVar (s: stack) (b: binder) (v: const):
        PositiveMap.MapsTo (fst b) v s ->
        sem_exp s (EVar b) v

    | SeAnd (s: stack) (e1 e2: exp) (v1 v2: bool):
        sem_exp s e1 (CBool v1) ->
        sem_exp s e2 (CBool v2) ->
        sem_exp s (EAnd e1 e2) (CBool (andb v1 v2))

    | SeOr (s: stack) (e1 e2: exp) (v1 v2: bool):
        sem_exp s e1 (CBool v1) ->
        sem_exp s e2 (CBool v2) ->
        sem_exp s (EOr e1 e2) (CBool (orb v1 v2))

    | SeXor (s: stack) (e1 e2: exp) (v1 v2: bool):
        sem_exp s e1 (CBool v1) ->
        sem_exp s e2 (CBool v2) ->
        sem_exp s (EXor e1 e2) (CBool (xorb v1 v2)).

  Inductive sem_stmt: stack -> stmt -> stack -> Prop :=
    | SeAssign (s: stack) (b: binder) (e: exp) (v: const):
        sem_exp s e v ->
        sem_stmt s (SAssign (fst b) e) (PositiveMap.add (fst b) v s)

    | SeSeq (s1 s2 s3: stack) (st1 st2: stmt):
        sem_stmt s1 st1 s2 ->
        sem_stmt s2 st2 s3 ->
        sem_stmt s1 (SSeq st1 st2) s3

    | SeReturn (s: stack) (e: exp) (v: const):
        sem_exp s e v ->
        sem_stmt s (SReturn e) (PositiveMap.add 1 v s)

    | SeNop (s: stack):
        sem_stmt s SNop s.

End target.


Section translation.

  Definition translate_const (c: source.const): target.const :=
    match c with
    | source.CBool b => target.CBool b
    end.

  Definition translate_type (t: source.type): target.type :=
    match t with
    | source.TBool => target.TBool
    end.

  Definition translate_binder (b: source.binder): target.binder :=
    (fst b, translate_type (snd b)).

  Fixpoint translate_exp (e: source.exp): target.exp :=
    match e with
    | source.EConst c => target.EConst (translate_const c)
    | source.EVar b => target.EVar (translate_binder b)
    | source.EAnd e1 e2 => target.EAnd (translate_exp e1) (translate_exp e2)
    | source.EOr e1 e2 => target.EOr (translate_exp e1) (translate_exp e2)
    | source.EXor e1 e2 => target.EXor (translate_exp e1) (translate_exp e2)
    end.

  Fixpoint translate_equation (eq: source.equation): target.stmt :=
    match fst eq with
    | 1 => target.SReturn (translate_exp (snd eq))
    | _ => target.SAssign (fst eq) (translate_exp (snd eq))
    end.

  Definition translate_history (h: source.history): target.stack :=
    PositiveMap.map (fun x => translate_const (Stream.hd x)) h.

  Definition translate_node (n: source.node): option target.method :=
    let return_eq := List.find (fun eq => (fst eq) =? 1) (source.n_body n) in
    let remaining_eqs := List.filter (fun eq => negb ((fst eq) =? 1)) (source.n_body n) in

    match return_eq with
    | None => None
    | Some return_eq => Some {|
        target.m_name := source.n_name n;

        target.m_in := map translate_binder (source.n_in n);
        target.m_out := translate_type (snd (source.n_out n));
        target.m_vars := map translate_binder (source.n_vars n);

        target.m_body := fold_left
                           (fun acc x => target.SSeq acc x)
                           (map translate_equation remaining_eqs)
                           (translate_equation return_eq)
      |}
    end.

  Lemma correctness_exp (e: source.exp) (h: source.history) (out: Stream.t source.const):
    source.sem_exp h e out ->
      target.sem_exp (translate_history h) (translate_exp e) (translate_const (Stream.hd out)).
  Proof.
    induction 1.

    - (* EConst *)
      apply target.SeConst.

    - (* EVar *)
      apply target.SeVar; simpl.

      set (f := fun e => translate_const (Stream.hd e)).
      now apply PositiveMap.map_1 with (f := f).

    - (* EAnd *)
      replace (Stream.hd _) with (source.CBool (Stream.hd s1 && Stream.hd s2)); simpl.
      2: { now destruct s1, s2. }

      apply target.SeAnd.
      + replace (target.CBool (Stream.hd s1)) with
          (translate_const (Stream.hd (Stream.map (fun x : bool => source.CBool x) s1))).
        2: { now destruct s1. }
        apply IHsem_exp1.

      + replace (target.CBool (Stream.hd s2)) with
          (translate_const (Stream.hd (Stream.map (fun x : bool => source.CBool x) s2))).
        2: { now destruct s2. }
        apply IHsem_exp2.

    - (* EOr *)
      replace (Stream.hd _) with (source.CBool (Stream.hd s1 || Stream.hd s2)); simpl.
      2: { now destruct s1, s2. }

      apply target.SeOr.
      + replace (target.CBool (Stream.hd s1)) with
          (translate_const (Stream.hd (Stream.map (fun x : bool => source.CBool x) s1))).
        2: { now destruct s1. }
        apply IHsem_exp1.

      + replace (target.CBool (Stream.hd s2)) with
          (translate_const (Stream.hd (Stream.map (fun x : bool => source.CBool x) s2))).
        2: { now destruct s2. }
        apply IHsem_exp2.

    - (* EXor *)
      replace (Stream.hd _) with (source.CBool (xorb (Stream.hd s1) (Stream.hd s2))); simpl.
      2: { now destruct s1, s2. }

      apply target.SeXor.
      + replace (target.CBool (Stream.hd s1)) with
          (translate_const (Stream.hd (Stream.map (fun x : bool => source.CBool x) s1))).
        2: { now destruct s1. }
        apply IHsem_exp1.

      + replace (target.CBool (Stream.hd s2)) with
          (translate_const (Stream.hd (Stream.map (fun x : bool => source.CBool x) s2))).
        2: { now destruct s2. }
        apply IHsem_exp2.
  Qed.

  Lemma correctness_node (n: source.node) (h: source.history) (ret: PositiveMap.t source.const):
    forall (m: target.method), translate_node n = Some m ->
      forall (ret': PositiveMap.t source.const),
        (forall (k: positive) (v: source.const),
           PositiveMap.MapsTo k v ret ->
           PositiveMap.MapsTo k v ret'
        )
    ->
      (forall (s: Stream.t source.const) (e: source.equation),
           In e (source.n_body n) ->
           PositiveMap.MapsTo (fst e) (Stream.hd s) ret ->
           source.sem_exp h (snd e) s
      ) -> (
        target.sem_stmt (@PositiveMap.empty target.const) (target.m_body m)
          (PositiveMap.map translate_const ret')
      ).
  Proof.
    intros m Hsuccess ret' Hweak Hsource.
    destruct n.

    induction (n_body).
    { discriminate. }

    simpl in IHl.
    unfold translate_node in Hsuccess. simpl in Hsuccess.
  Admitted.

End translation.


Section example.

  Section source.

    Import source.
    Notation "a ⊕ b" := (source.EXor a b) (at level 40).
    Notation "a ∧ b" := (source.EAnd a b) (at level 40).
    Notation "a ∨ b" := (source.EOr a b) (at level 40).
    Notation "( x ~ T )" := (source.EVar (x, T)) (at level 0).

    Program Definition full_add: node := {|
      n_name := 1;

      n_in := [(2, TBool); (3, TBool); (4, TBool)];
      n_out := (1, TBool);
      n_locals := [(5, TBool)];

      n_body := [
        (1, (((2 ~ TBool) ⊕ (3 ~ TBool)) ⊕ (4 ~ TBool)));
        (5, (((2 ~ TBool) ∧ (3 ~ TBool)) ∨ ((2 ~ TBool) ∧ (4 ~ TBool))) ∨ ((3 ~ TBool) ∧ (4 ~ TBool)))
      ];
    |}.
    Next Obligation.
    Admitted.

  End source.

  Section target.

    Notation "a ⊕ b" := (target.EXor a b) (at level 40).
    Notation "a ∧ b" := (target.EAnd a b) (at level 40).
    Notation "a ∨ b" := (target.EOr a b) (at level 40).
    Notation "( x ~ T )" := (target.EVar (x, T)) (at level 0).

    Notation "a <- b" := (target.SAssign a b) (at level 40).
    Notation "'return' a" := (target.SReturn a) (at level 40).
    Notation "a ; b" := (target.SSeq a b) (at level 40).

    Eval compute in (translate_node full_add).

  End target.

End example.
