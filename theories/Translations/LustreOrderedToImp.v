From Reactive Require Import Base.
From Reactive.Datatypes Require Ordered.
From Reactive.Languages Require LustreOrdered Imp.

Module Source := LustreOrdered.Lustre.
Module Target := Imp.


Definition translate_const (c: Source.const): Target.const :=
  match c with
  | Source.CBool b => Target.CBool (Stream.hd b)
  end.

Definition translate_type (t: Source.type): Target.type :=
  match t with
  | Source.TBool => Target.TBool
  end.

Definition translate_binder (b: Source.binder): Target.binder :=
  (fst b, translate_type (snd b)).

Definition translate_binop (op: Source.binop): Target.binop :=
  match op with
  | Source.Bop_and => Target.Bop_and
  | Source.Bop_or => Target.Bop_or
  | Source.Bop_xor => Target.Bop_xor
  end.

Fixpoint translate_value (v: Source.value): Target.value :=
  match v with
  | Source.VConst c => Target.VConst (translate_const c)
  | Source.VInput b => Target.VInput (translate_binder b)
  | Source.VBinop op v1 v2 => Target.VBinop (translate_binop op) (translate_value v1) (translate_value v2)
  end.

Fixpoint translate_exp (e: Source.exp): Target.exp :=
  match e with
  | Source.EConst c => Target.EConst (translate_const c)
  | Source.EInput b => Target.EInput (translate_binder b)
  | Source.EVar b => Target.EVar (translate_binder b)
  | Source.EBinop op e1 e2 => Target.EBinop (translate_binop op) (translate_exp e1) (translate_exp e2)
  end.

Definition translate_equation (eq: Source.equation): Target.stmt :=
  Target.SAssign (fst eq) (translate_exp (snd eq)).

Definition translate_history (h: Source.history): Target.stack :=
  Dict.map (fun x => translate_value x) h.

Definition translate_node_body (body: list Source.equation): Target.stmt :=
  fold_right (fun acc x => Target.SSeq x acc) Target.SNop (List.map translate_equation body).

Definition tranlsate_lustre_node (n: Source.node): Target.method := {|
    Target.m_name := Source.n_name n;

    Target.m_in := map translate_binder (Source.n_in n);
    Target.m_out := translate_type (snd (Source.n_out n));
    Target.m_vars := map translate_binder (Source.n_vars n);

    Target.m_body := translate_node_body n.(Source.n_body)
|}.

Definition translate_node (n: LustreOrdered.node_ordered): Target.method :=
  tranlsate_lustre_node (LustreOrdered.node_ordered_is_node n).
