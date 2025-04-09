From HoTT Require Import Basics Types Truncations.Core Pointed.Core Homotopy.Cover.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.

(** * Evaluation fibrations and self-maps *)

(** The type of unpointed self maps of A, pointed at the identity map. *)
Definition selfmaps (A : Type) : pType := [A -> A, idmap].

(** The unrestricted evaluation map. *)
Definition ev (A : pType) : selfmaps A ->* A
  := Build_pMap (fun f : selfmaps A => f pt) idpath.

(** The evaluation fibration of an unpointed map [X -> A]. *)
Definition evfib {X : pType} {A : Type} (f : X -> A) : comp (X -> A) (tr f) -> A
  := fun g => g.1 pt.

(** If [f] is pointed, then the evaluation fibration of [f] is too. *)
Definition pevfib {A X : pType} (f : X ->* A) : pcomp (X -> A) f ->* A
  := Build_pMap (fun g : pcomp (X -> A) f => g.1 pt) (point_eq f).

(** The evaluation map of the identity. *)
Definition ev1 (A : pType) := pevfib (A:=A) pmap_idmap.
