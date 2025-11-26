From HoTT Require Import Basics Types.
Require Import Pointed WildCat.
Require Import Modalities.ReflectiveSubuniverse Truncations.Core.
Require Import Algebra.AbGroups.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.PinSn.
Require Import Spaces.Int Spaces.Circle.

Require Import Spaces.Torus.Torus.
Require Import Spaces.Torus.TorusEquivCircles.

Local Open Scope trunc_scope.
Local Open Scope pointed_scope.

(** ** Fundamental group of the torus .*)

(** The torus is 1-truncated *)

Instance is1type_torus `{Univalence} : IsTrunc 1 Torus.
Proof.
  exact (istrunc_equiv_istrunc _ equiv_torus_prod_Circle^-1).
Qed.

(** The torus is 0-connected *)

Instance isconnected_torus `{Univalence} : IsConnected 0 Torus.
Proof.
  srapply (isconnected_equiv' _ _ equiv_torus_prod_Circle^-1).
  srapply (isconnected_equiv' _ _ (equiv_sigma_prod0 _ _)).
Qed.

(** We give these notations for the pointed versions. *)
Local Notation T := ([Torus, _]).
Local Notation S1 := ([Circle, _]).

(** A pointed version of the equivalence from TorusEquivCircles.v. *)
(** TODO: If [Funext] is removed from there, remove it from here as well. *)
Lemma pequiv_torus_prod_circles `{Funext} : T  <~>* S1 * S1.
Proof.
  srapply Build_pEquiv'.
  1: exact equiv_torus_prod_Circle.
  reflexivity.
Defined.

(** Fundamental group of torus *)
Theorem pi1_torus `{Univalence}
  : GroupIsomorphism (Pi 1 T) (grp_prod abgroup_Z abgroup_Z).
Proof.
  etransitivity.
  1: exact (emap (Pi 1) pequiv_torus_prod_circles).
  etransitivity.
  1: apply grp_iso_pi_prod.
  apply grp_iso_prod.
  1,2: exact pi1_circle.
Defined.

(** Loop space of torus *)
Theorem loops_torus `{Univalence} : loops T <~>* Int * Int.
Proof.
  (* Since [T] is 1-truncated, [loops T] is 0-truncated, and is therefore equivalent to its 0-truncation. *)
  refine (_ o*E pequiv_ptr (n:=0)).
  exact pi1_torus.
Defined.
