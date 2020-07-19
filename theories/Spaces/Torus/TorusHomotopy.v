Require Import Basics Types Pointed.
Require Import Algebra.AbGroups.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.Pi1S1.
Require Import Spaces.Int Spaces.Circle.
Require Import Truncations.

Require Import Spaces.Torus.Torus.
Require Import Spaces.Torus.TorusEquivCircles.

Local Open Scope trunc_scope.
Local Open Scope pointed_scope.

(** ** Fundamental group of the torus .*)

(** The torus is 1-truncated *)

Global Instance is1type_Torus `{Univalence} : IsTrunc 1 Torus.
Proof.
  refine (trunc_equiv _ equiv_torus_prod_Circle^-1).
Qed.

(** The torus is 0-connected *)

Global Instance isconnected_Torus `{Univalence} : IsConnected 0 Torus.
Proof.
  srapply (isconnected_equiv' _ _ equiv_torus_prod_Circle^-1).
  srapply (isconnected_equiv' _ _ (equiv_sigma_prod0 _ _)).
Qed.

(** We give these notations for the pointed versions. *)
Local Notation T := (Build_pType Torus _).
Local Notation S1 := (Build_pType Circle _).

(** Loop space of Torus *)
Theorem loops_torus `{Univalence} : loops T <~>* Int * Int.
Proof.
  srefine (_ o*E _).
  1: exact (loops (S1 * S1)).
  1: apply pequiv_loops_functor.
  { srapply Build_pEquiv.
    1: srapply Build_pMap.
    1: exact equiv_torus_prod_Circle.
    1: reflexivity.
    exact _. }
  srefine (_ o*E _).
  1: exact (loops S1 * loops S1).
  1: apply loops_prod.
  snrapply Build_pEquiv.
  1: srapply Build_pMap.
  { apply functor_prod.
    1,2: apply equiv_loopCircle_int. }
  1: reflexivity.
  exact _.
Defined.

Lemma pequiv_torus_prod_circles `{Funext} : T  <~>* S1 * S1.
Proof.
  srapply Build_pEquiv'.
  1: apply equiv_torus_prod_Circle.
  reflexivity.
Defined.

(** Fundamental group of Torus *)
Theorem Pi1Torus `{Univalence}
  : GroupIsomorphism (Pi 1 T) (grp_prod abgroup_Z abgroup_Z).
Proof.
  etransitivity.
  { apply groupiso_pi_functor.
    apply pequiv_torus_prod_circles. }
  etransitivity.
  1: apply pi_prod.
  apply grp_iso_prod.
  1,2: apply Pi1Circle.
Defined.
