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