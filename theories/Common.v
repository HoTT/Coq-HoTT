(* -*- mode: coq; mode: visual-line -*- *)
(** * General definitions that are used throughout the library. *)

(** We make the identity map a notation so we do not have to unfold it,
    or complicate matters with its type. *)
Notation "'idmap'" := (fun x => x).

(** We define notation for dependent pairs because it is too annoying to write and see [existT P x y] all the time.  However, we put it in its own scope, because sometimes it is necessary to give the particular dependent type, so we'd like to be able to turn off this notation selectively. *)
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.

Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Notation "x .2" := (projT2 x) (at level 3) : fibration_scope.

(** Composition of functions. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

(** These funny looking types are used to trigger the canonical structures
   mechanism. *)
Inductive batman T (p : T) := Batman. (* Known as [phantom] in ssreflect. *)
Inductive robin (p : Type) := Robin. (* Known as [phant] in ssreflect. *)
