Require Import Basics.
Require Import Pointed.
Require Import Spaces.Int.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.Suspension.
Require Import HIT.Circle.
Require Import HIT.Truncations.
Require Import HIT.Spheres.
Require Import UnivalenceAxiom.

(*
  Calculation of Pi 1 S1
*)

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
    assert (X : (Sphere 1, North) = (S1, base)).
    { serapply path_ptype.
      serapply Build_pEquiv.
      1: serapply Build_pMap.
      1: serapply Sph1_to_S1.
      1: reflexivity.
      exact _. }
    refine (transport (fun x => Pi _ x <~> _) X^ _).
    apply Pi1S1.
  Defined.

End Pi1S1.