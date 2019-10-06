Require Import HoTT.Basics.
Require Import HoTT.Pointed.
Require Import HoTT.Spaces.Int.
Require Import HoTT.Homotopy.HomotopyGroup.
Require Import HoTT.Homotopy.Suspension.
Require Import HoTT.HIT.Circle.
Require Import HoTT.HIT.Truncations.
Require Import HoTT.HIT.Spheres.
Require Import HoTT.UnivalenceAxiom.

(* Calculation of Pi 1 S1 *)

Section Pi1S1.
  Local Notation "( A , a )" := (Build_pType A a).

  Theorem Pi1S1 : Pi 1 (S1, base) <~> Int.
  Proof.
    unfold Pi; cbn.
    equiv_via (base = base).
    1: symmetry; exact (equiv_tr 0 (loops (S1, base))).
    exact equiv_loopS1_int.
  Defined.

  Theorem Pi1S1' : Pi 1 (psphere 1) <~> Int.
  Proof.
    unfold psphere.
    refine (transport (fun x => Pi _ x <~> _) _ _).
    2: apply Pi1S1.
    apply path_ptype.
    symmetry.
    apply pequiv_pSph1_to_S1.
  Defined.

End Pi1S1.