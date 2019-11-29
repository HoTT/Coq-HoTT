Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Spaces.Int.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Homotopy.HomotopyGroup.
Require Import HIT.Circle.
Require Import HIT.Spheres.
Require Import Truncations.
Require Import Algebra.Z.
Require Import Truncations.
Import TrM.

(* Calculation of Pi 1 S1 *)

Section Pi1S1.
  Context `{Univalence}.

  Local Notation "( A , a )" := (Build_pType A a).

(*   Local Infix "≅" := GroupIsomorphism (at level 20).
  Local Notation "'π'" := HomotopyGroup (at level 0).
  Local Infix "×" := group_prod (at level 5).
 *)
  Local Open Scope int_scope.
  Local Open Scope pointed_scope.

  Theorem Pi1Circle : GroupIsomorphism (Pi 1 (S1, base)) Z.
  Proof.
    (** We give the isomorphism backwards, so we check the operation is preserved coming from the integer side. *)
    symmetry.
    serapply Build_GroupIsomorphism'.
    { equiv_via (base = base).
      2: exact (equiv_tr 0 (loops (S1, base))).
      symmetry.
      exact equiv_loopS1_int. }
    intros a b.
    cbn; apply ap.
    apply loopexp_add.
  Defined.

  Theorem Pi1S1 : GroupIsomorphism (Pi 1 (psphere 1)) Z.
  Proof.
    etransitivity.
    2: apply Pi1Circle.
    apply groupiso_pi_functor.
    apply pequiv_pSph1_to_S1.
  Defined.

End Pi1S1.