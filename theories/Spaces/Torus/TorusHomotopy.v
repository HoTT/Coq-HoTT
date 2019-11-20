Require Import Basics.
Require Import Types.
Require Algebra.Group.
Require Algebra.AbelianGroup.
Require Import Homotopy.Pi1S1.
Require Import Algebra.Z.
Require Import Pointed.
Require Import Spaces.Int.
Require Import HIT.Circle.
Require Import Truncations.
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

Lemma pequiv_torus_prod_circles `{Funext} : T  <~>* S1 * S1.
Proof.
  serapply Build_pEquiv'.
  1: apply equiv_torus_prod_S1.
  reflexivity.
Defined.

(* Fundamental group of Torus *)

Import Algebra.Group.
Import Algebra.AbelianGroup.

Local Notation "( A , a )" := (Build_pType A a).
Local Infix "≅" := GroupIsomorphism (at level 20).
Local Notation "'π'" := HomotopyGroup (at level 0).
Local Infix "×" := group_prod (at level 5).

Theorem Pi1Torus `{Univalence} : π 1 T ≅ Z × Z.
Proof.
  etransitivity.
  { apply groupiso_homotopygroup_functor.
    apply pequiv_torus_prod_circles. }
  etransitivity.
  1: apply homotopygroup_prod.
  apply groupiso_prod.
  1,2: apply Pi1Circle.
Defined.
