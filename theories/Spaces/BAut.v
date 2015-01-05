(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import Modalities.Modality hit.Truncations hit.Connectedness.
Import TrM.

Open Scope path_scope.
Open Scope equiv_scope.

(** * BAut(X) *)

(** [BAut X] is the type of types that are merely equivalent to [X]. *)
Definition BAut (X : Type) := { Z : Type & merely (Z = X) }.

(** It is canonically pointed by [X] itself. *)
Global Instance ispointed_baut X : IsPointed (BAut X)
  := (X ; tr 1).

Definition BAut_pr1 X : BAut X -> Type := pr1.
Coercion BAut_pr1 : BAut >-> Sortclass.

Definition path_baut `{Univalence} {X} (Z Z' : BAut X)
: (Z <~> Z') <~> (Z = Z' :> BAut X).
Proof.
  eapply equiv_compose'.
  - apply equiv_path_sigma_hprop.
  - apply equiv_path_universe.
Defined.
