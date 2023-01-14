(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import Colimits.Pushout.
Require Import Truncations.Core.

(** * Cones of HSets *)

Section SetCone.
  Context {A B : HSet} (f : A -> B).

  Definition setcone := Trunc 0 (Pushout f (const tt)).

  Global Instance istrunc_setcone : IsHSet setcone := _.

  Definition setcone_point : setcone := tr (push (inr tt)).
End SetCone.
