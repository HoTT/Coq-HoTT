Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.rationals
  HoTTClasses.theory.dec_fields.

Section contents.
Context `{Rationals Q} `{!TrivialApart Q}.

Global Instance rational_1_neq_0 : PropHolds (@apart Q _ 1 0).
Proof.
red. apply trivial_apart. solve_propholds.
Qed.

End contents.
