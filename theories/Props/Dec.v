Set Default Goal Selector "!".

From Stdlib Require Import List.
From Stdlib Require ListDec.

Import ListNotations.

Definition incl_dec {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) : forall l l' : list A, {incl l l'} + {~ incl l l'} :=
  fun l1 l2 =>
  list_rec (fun l1 => {incl l1 l2} + {~ incl l1 l2})
    (left (fun (x : A) (H : In x []) => match H return In x l2 with end))
    (fun (hd: A) (tl: list A) (IH: {incl tl l2} + {~ incl tl l2}) => match ListDec.In_dec dec hd l2 with
      | right hdnin => right (fun Hincl => hdnin (Hincl hd (or_introl _ eq_refl)))
      | left hdin => match IH with
        | right nincl => right (fun Hincl => nincl (fun (x: A) (H: In x tl) => Hincl x (or_intror _ H)))
        | left incl =>
          left
            (fun (x: A) (H: In x (hd :: tl)) => match H with
            | or_introl _ xeq => eq_ind_r (fun y => In y _ -> In x _) (fun p => p) xeq hdin
            | or_intror _ xintl => incl x xintl
            end)
        end
      end)
    l1.

Definition dec_not {P : Prop} : {P} + {~P} -> {~P} + {~ ~P} :=
  fun dec => match dec with left h => right (fun nP => nP h) | right h => left h end.

Definition prod_dec {A B : Type} : (forall x y : A, {x = y} + {x <> y}) -> (forall x y : B, {x = y} + {x <> y}) ->
  (forall x y : A * B, {x = y} + {x <> y}) := fun decA decB '(xa, xb) '(ya, yb) =>
  match decA xa ya with
  | right n => right (fun (f : (_, _) = (_, _)) => n (f_equal fst f))
  | left ea =>
    match decB xb yb with
    | right n => right (fun (f : (_, _) = (_, _)) => n (f_equal snd f))
    | left eb => left (f_equal2 pair ea eb)
    end
  end.
