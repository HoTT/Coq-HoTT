Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.tactics.ring_tac.

Lemma test1 `{SemiRing R}
  : forall x y : R, x + (y * x) = x * (y + 1).
Proof.
intros.
ring_with_nat.
Qed.

Require Import
  HoTTClasses.interfaces.naturals.

Lemma test2 `{SemiRing R}
  : forall x y : R, x + (y * x) = x * (y + 1).
Proof.
intros.
apply (by_quoting (naturals_to_semiring nat R)).
compute. reflexivity.
Qed.
