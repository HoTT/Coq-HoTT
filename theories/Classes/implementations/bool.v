Require Import
  HoTT.Classes.interfaces.abstract_algebra.

Global Instance join_bool : Join Bool := orb.
Global Instance meet_bool : Meet Bool := andb.
Global Instance bottom_bool : Bottom Bool := false.
Global Instance top_bool : Top Bool := true.

Section contents.
  Local Ltac solve_bool :=
    repeat (intros [|]); compute; (contradiction || auto).

  Global Instance lattice_bool : IsBoundedLattice Bool.
  Proof. repeat split; (apply _ || solve_bool). Defined.

End contents.
