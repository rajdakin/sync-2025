#[export] Set Default Goal Selector "!".

From Coq Require Export List Nat String.
From Coq Require Export Lia.

Export ListNotations.
Open Scope nat_scope.


Axiom ProofIrrelevance: forall (P: Prop) (p q: P), p = q.

Definition ident := nat.
