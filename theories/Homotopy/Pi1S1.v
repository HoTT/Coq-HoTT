Require Import
  HoTT.Basics
  HoTT.Pointed
  HoTT.Spaces.Int
  HoTT.Homotopy.HomotopyGroup
  HoTT.HIT.Circle
  HoTT.HIT.Truncations
  HoTT.HIT.Spheres
  HoTT.HIT.Suspension
  HoTT.UnivalenceAxiom.

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
    refine (transport (fun x => Pi _ x <~> _) _ _).
    2: apply Pi1S1.
    apply path_ptype.
    symmetry.
    apply pequiv_pSph1_to_S1.
  Defined.

End Pi1S1.