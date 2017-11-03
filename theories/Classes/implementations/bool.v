Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Types.Bool.

Instance join_bool : Join Bool := orb.
Instance meet_bool : Meet Bool := andb.
Instance bottom_bool : Bottom Bool := false.
Instance top_bool : Top Bool := true.

Section contents.
  Local Ltac solve_bool :=
    repeat (intros [|]); compute; (contradiction || auto).

  Global Instance boundedjoinsemilattice_bool :
    BoundedJoinSemiLattice Bool.
  Proof. repeat split; (apply _ || solve_bool). Defined.

  Global Instance boundedmeetsemilattice_bool :
    @BoundedSemiLattice Bool (⊓) true.
  Proof. repeat split; (apply _ || solve_bool). Defined.

  Global Instance lattice_bool : Lattice Bool.
  Proof. repeat split; (apply _ || solve_bool). Defined.

End contents.
