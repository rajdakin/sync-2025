From Reactive Require Export Base.

From Stdlib Require Export String.


Inductive t (A: Type): Type :=
  | Ok: A -> t A
  | Err: string -> t A.

Arguments Ok {_}.
Arguments Err {_}.


Definition bind {A B} (x: t A) (f: A -> t B): t B :=
  match x with
  | Err msg => Err msg
  | Ok x => f x
  end.


Module notations.

  Notation "e1 >>= e2" := (bind e1 e2) (at level 60, right associativity).
  Notation "'do' x <- e1 ; e2" := (bind e1 (fun x => e2)) (at level 60, right associativity).

End notations.
