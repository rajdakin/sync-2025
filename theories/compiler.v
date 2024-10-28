From Coq Require Export List.
From Coq Require Export BinNums FMapPositive PArith.

Import ListNotations.
Open Scope positive.


Definition ident := positive.

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

  Definition equation := prod (list ident) (list exp).


  Record node := mk_node {
    n_name: ident;

    n_in: list binder;
    n_out: list binder;
    n_vars: list binder;

    n_body: list equation;
  }.

  CoInductive Stream (A: Type) :=
    | Cons: A -> Stream A -> Stream A.

  Arguments Cons {_} _ _.


  CoFixpoint from {A: Type} (x: A) : Stream A := Cons x (from x).

  CoFixpoint merge {A B C: Type} (f: A -> B -> C) (x: Stream A) (y: Stream B): Stream C :=
    match x, y with
    | Cons x xs, Cons y ys => Cons (f x y) (merge f xs ys)
    end.

  CoFixpoint map {A B: Type} (f: A -> B) (x: Stream A): Stream B :=
    match x with
    | Cons x xs => Cons (f x) (map f xs)
    end.


  Definition value := const.
  Definition history := PositiveMap.t (Stream value).

  Definition sem_const (c: const): value := c.

  Inductive sem_exp: history -> exp -> Stream const -> Prop :=
    | SeConst (h: history) (c: const) (s: Stream const):
        sem_exp h (EConst c) (from (sem_const c))

    | SeVar (h: history) (b: binder) (s: Stream const):
        PositiveMap.MapsTo (fst b) s h ->
        sem_exp h (EVar b) s

    | SeAnd (h: history) (e1 e2: exp) (s1 s2 s: Stream bool):
        sem_exp h e1 (map (fun x => CBool x) s1) ->
        sem_exp h e2 (map (fun x => CBool x) s2) ->
        sem_exp h (EAnd e1 e2) (map (fun x => CBool x) (merge (fun x y => andb x y) s1 s2))

    | SeOr (h: history) (e1 e2: exp) (s1 s2 s: Stream bool):
        sem_exp h e1 (map (fun x => CBool x) s1) ->
        sem_exp h e2 (map (fun x => CBool x) s2) ->
        sem_exp h (EOr e1 e2) (map (fun x => CBool x) (merge (fun x y => orb x y) s1 s2))

    | SeXor (h: history) (e1 e2: exp) (s1 s2 s: Stream bool):
        sem_exp h e1 (map (fun x => CBool x) s1) ->
        sem_exp h e2 (map (fun x => CBool x) s2) ->
        sem_exp h (EXor e1 e2) (map (fun x => CBool x) (merge (fun x y => xorb x y) s1 s2)).

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
    | SAssign: binder -> exp -> stmt
    | SSeq : stmt -> stmt -> stmt
    | SReturn : exp -> stmt
    | SNop : stmt.


  Record method := mk_method {
    m_name: ident;

    m_in: list binder;
    m_out: list binder;
    m_vars: list binder;

    m_body: list stmt;
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
        sem_stmt s (SAssign b e) (PositiveMap.add (fst b) v s)

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


Section source_example.

  Import source.

  Notation "a ⊕ b" := (EXor a b) (at level 0).
  Notation "a ∧ b" := (EAnd a b) (at level 0).
  Notation "a ∨ b" := (EOr a b) (at level 0).

  Notation "( x ~ T )" := (EVar (x, T)) (at level 0).

  Program Definition full_add: node := {|
    n_name := 1;

    n_in := [(1, TBool); (2, TBool); (3, TBool)];
    n_out := [(4, TBool); (5, TBool)];
    n_vars := [];

    n_body := [
      ([5], [((1 ~ TBool) ⊕ (2 ~ TBool)) ⊕ (3 ~ TBool)]);
      ([4], [(((1 ~ TBool) ∧ (2 ~ TBool)) ∨ ((1 ~ TBool) ∧ (3 ~ TBool))) ∨ ((2 ~ TBool) ∧ (3 ~ TBool))])
    ];
  |}.

End source_example.
