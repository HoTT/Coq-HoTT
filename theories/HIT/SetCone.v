(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import HoTT.Types.
Require Import HSet TruncType.
Require Import Colimits.Pushout.
Require Import HoTT.Truncations.

(** * Cones of hsets *)

Section SetCone.
  Context {A B : hSet} (f : A -> B).

  Definition setcone := Trunc 0 (Pushout f (const tt)).

  Global Instance istrunc_setcone : IsHSet setcone := _.

  Definition setcone_point : setcone := tr (push (inr tt)).
End SetCone.
