Parameter t : Type -> Type.
Parameter make : forall {A}, nat -> A -> t A.
Parameter length : forall {A}, t A -> nat.
Parameter set : forall {A} (a : t A) (n : nat), A -> t A.
Parameter get : forall {A} (a : t A) (n : nat), A.

Axiom length_make : forall {A} n (x : A), length (make n x) = n.
Axiom length_set : forall {A} (a : t A) n x, length (set a n x) = length a.
Axiom get_make : forall {A} n (x : A) k, k < n -> get (make n x) k = x.
Axiom get_set_same : forall {A} (a : t A) n x, n < length a -> get (set a n x) n = x.
Axiom get_set_other : forall {A} (a : t A) n1 x n2, n1 < length a -> n1 <> n2 -> get (set a n1 x) n2 = get a n2.
