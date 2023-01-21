From HoTT Require Import Basics Types Truncations.Core HFiber
  Pointed Pointed.pModality Modalities.ReflectiveSubuniverse.

Local Open Scope pointed_scope.

(** * [O]-connected covers *)

(** Given a reflective subuniverse [O], for any type [X] and [x : O X], the [O]-connected cover of [X] at [x] is the fibre of [to O X] at [x]. *)

Definition O_cover@{u} `{O : ReflectiveSubuniverse@{u}}
  (X : Type@{u}) (x : O X) : Type@{u}
  := hfiber (to O _) x.

(** Characterization of paths in [O_cover] is given by [equiv_path_hfiber]. *)

(** Path components are given by specializing to [O] being set-truncation. *)
Definition comp := O_cover (O:=Tr 0).

(* If [x] is an actual point of [X], then the connected cover is pointed. *)
Definition O_pcover@{u v} (O : ReflectiveSubuniverse@{u})
  (X : Type@{u}) (x : X) : pType@{u}
  := pfiber@{u v u u} (pto O [X,x]).

Definition pcomp := O_pcover (Tr 0).
