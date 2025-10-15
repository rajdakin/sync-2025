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

Definition strong_bind {A B} (x: t A) (f: forall a: A, x = Ok a -> t B): t B :=
  match x as y return x = y -> _ with
  | Err msg => fun _ => Err msg
  | Ok x => f x
  end eq_refl.


Module notations.

  Notation "e1 >>= e2" := (bind e1 e2) (at level 60, right associativity).
  Notation "'do' x <- e1 ; e2" := (bind e1 (fun x => e2)) (at level 60, x binder, right associativity).
  Notation "'do' x 'remember' e <- e1 ; e2" := (strong_bind e1 (fun x e => e2)) (at level 60, x binder, e binder, right associativity).

End notations.
