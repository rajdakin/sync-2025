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
