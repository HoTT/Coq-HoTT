From HoTT Require Import Basics.Overture Pointed.Core.

(** Test pelim tactic. *)

Open Scope pointed_scope.

(** Check that it works for types with explicit base points. *)
Definition test1 {X Y : Type} {x : X} {y : Y} (f : [X,x] ->* [Y,y]) : (f x = y) * (point_eq f = point_eq f).
Proof.
  pelim f.
  split; reflexivity.
Defined.

(** Check that it works for pointed equivalences. *)
Definition test2 {X Y : pType} (f : X <~>* Y) : (f pt = pt) * (point_eq f = point_eq f).
Proof.
  pelim f.
  split; reflexivity.
Defined.
