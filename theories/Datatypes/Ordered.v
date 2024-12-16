From Reactive Require Import Base.

Inductive t {A: Type}: list (A * list A) -> Prop :=
  | nil : t []
  | alone (x: A) (l: list (A * list A)):
      t l ->
      ~ In x (map fst l) ->
      t ((x, []) :: l)
  | append (x: A) (lx: list A) (l: list (A * list A)):
      t l ->
      ~ In x (map fst l) ->
      (Forall (fun y => exists ly: list A, In (y, ly) l) lx) ->
      t ((x, lx) :: l).
