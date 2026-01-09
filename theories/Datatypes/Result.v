Set Default Goal Selector "!".

From Stdlib Require Import List.
From Stdlib Require Export String.

From Reactive.Props Require Import Identifier.

Import ListNotations.

Record location : Set := {
  loc_start_line: nat;
  loc_start_col: nat;
  loc_end_line: nat;
  loc_end_col: nat;
}.

Inductive declaration_location: Set :=
  | DeclInput
  | DeclOutput
  | DeclLocal
.

Inductive r {type: Set} | : Set :=
  | BadType (expected: list type) (got: type): r
  | IncompatibleTypeAssignment (vname: string) (vid: ident) (vtype: type) (etype: type): r
  | UndeclaredVariable (vname: string): r
  | MultipleDeclaration (vname: string) (vid: ident) (loc1 loc2: declaration_location): r
  | MissingAssignment (vname: string) (vid: ident) (vtype: type): r
  | MultipleAssignment (vname: string) (vid: ident) (vtype: type): r
  | AssignToInput (vname: string) (vid: ident) (vtype: type): r
  | InvalidTiming (vname: string) (vid: ident) (vtype: type): r
  | CyclicDependency (loop: list ident): r
  | InternalError (msg: string): r
.
Arguments r _ : clear implicits.

Inductive t type (A: Type) | : Type :=
  | Ok: A -> t
  | Err: list (location * r type) -> t.

Arguments Ok [_] {_}.
Arguments Err {_ _}.


Definition combine_prop {type} {A B : Prop} (x: t type A) (y: t type B): t type (A /\ B) := match x, y with
  | Ok x, Ok y => Ok (conj x y)
  | Err x, Ok _ => Err x
  | Ok _, Err y => Err y
  | Err x, Err y => Err (x ++ y)
end.

Definition combine {type A B} (x: t type A) (y: t type B): t type (A * B) := match x, y with
  | Ok x, Ok y => Ok (x, y)
  | Err x, Ok _ => Err x
  | Ok _, Err y => Err y
  | Err x, Err y => Err (x ++ y)
end.

Definition bind {type A B} (x: t type A) (f: A -> t type B): t type B :=
  match x with
  | Err msg => Err msg
  | Ok x => f x
  end.

Definition strong_bind {type A B} (x: t type A) (f: forall a: A, x = Ok a -> t type B): t type B :=
  match x as y return x = y -> _ with
  | Err msg => fun _ => Err msg
  | Ok x => f x
  end eq_refl.

Definition list_map {type A} {P : A -> Prop} (dec : forall x, t type (P x)): forall l, t type (Forall P l) :=
  fix inner l := match l with
  | [] => Ok (Forall_nil _)
  | hd :: tl => match dec hd with
      | Ok H => bind (inner tl) (fun IH => Ok (Forall_cons _ H IH))
      | Err es => Err (match inner tl with Ok _ => es | Err es' => es ++ es' end)
      end
  end.


Module notations.

  Infix ">>=" := bind (at level 60, right associativity).
  Notation "'do' x <- e1 ; e2" := (bind e1 (fun x => e2)) (at level 60, x binder, right associativity).
  Notation "'do' x 'remember' e <- e1 ; e2" := (strong_bind e1 (fun x e => e2)) (at level 60, x binder, e binder, right associativity).
  Infix ">+<" := combine (at level 60, right associativity).

End notations.

Lemma ok_eq {A E} (a b: A): @Ok E A a = Ok b -> a = b.
Proof.
  inversion 1.
  reflexivity.
Qed.
