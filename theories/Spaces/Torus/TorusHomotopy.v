Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Spaces.Int.
Require Import HIT.Circle.
Require Import HIT.Truncations.
Require Import HIT.Connectedness.
Require Import Homotopy.HomotopyGroup.
Import TrM.

Require Import Torus.
Require Import TorusEquivCircles.

(* The torus is 1-truncated *)

Global Instance is1type_Torus `{Univalence} : IsTrunc 1 Torus.
Proof.
  serapply (inO_equiv_inO (O:=1) _ equiv_torus_prod_S1^-1).
Qed.

(* The torus is 0-connected *)

Global Instance isconnected_Torus `{Univalence} : IsConnected 0 Torus.
Proof.
  serapply (isconnected_equiv' _ _ equiv_torus_prod_S1^-1).
  serapply (isconnected_equiv' _ _ (equiv_sigma_prod0 _ _)).
Qed.

(* Loop space of Torus *)

Global Instance ispointed_torus : IsPointed Torus := tbase.

Local Open Scope pointed_scope.

Notation T := (Build_pType Torus _).
Notation S1 := (Build_pType S1 _).

Theorem loops_torus `{Univalence} : loops T <~>* Int * Int.
Proof.
  srefine (_ o*E _).
  1: exact (loops (S1 * S1)).
  1: apply pequiv_loops_functor.
  { serapply Build_pEquiv.
    1: serapply Build_pMap.
    1: exact equiv_torus_prod_S1.
    1: reflexivity.
    exact _. }
  srefine (_ o*E _).
  1: exact (loops S1 * loops S1).
  1: apply loops_prod.
  serapply Build_pEquiv.
  1: serapply Build_pMap.
  { apply functor_prod.
    1,2: apply equiv_loopS1_int. }
  1: reflexivity.
  exact _.
Defined.

(* Fundamental group of Torus *)

Theorem Pi1Torus `{Univalence} : Pi 1 T <~> Int * Int.
Proof.
  unfold Pi.
  refine ((equiv_tr 0 (Int * Int))^-1 oE _).
  refine (Trunc_functor_equiv 0 _).
  serapply loops_torus.
Defined.
