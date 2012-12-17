(** * General definitions that are used throughout the library. *)

(** We make the identity map a notation so we do not have to unfold it,
    or complicate matters with its type. *)
Notation "'idmap'" := (fun x => x).

(** Notation for dependent pairs. *)
Notation "( x ; y )" := (existT _ x y).

(** Composition of functions. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

(** These funny looking types are used to trigger the canonical structures
   mechanism. *)
Inductive batman T (p : T) := Batman. (* Known as [phantom] in ssreflect. *)
Inductive robin (p : Type) := Robin. (* Known as [phant] in ssreflect. *)
