Require Import HoTT.Basics Types.Unit.
Require Import Colimits.Pushout.
Require Import Truncations.Core.

(** * Cones of HSets *)

Section SetCone.
  Context {A B : HSet} (f : A -> B).

  Definition setcone := Trunc 0 (Pushout@{_ _ Set _} f (const_tt A)).

  #[export] Instance istrunc_setcone : IsHSet setcone := _.

  Definition setcone_point : setcone := tr (push (inr tt)).
End SetCone.
