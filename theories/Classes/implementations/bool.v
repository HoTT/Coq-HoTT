Require Import
  HoTT.Classes.interfaces.abstract_algebra.

Instance join_bool : Join Bool := orb.
Instance meet_bool : Meet Bool := andb.
Instance bottom_bool : Bottom Bool := false.
Instance top_bool : Top Bool := true.

Section contents.
  Local Ltac solve_bool :=
    repeat (intros [|]); compute; (contradiction || auto).

  #[export] Instance lattice_bool : IsBoundedLattice Bool.
  Proof. repeat split; (apply _ || solve_bool). Defined.

End contents.
