Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.tactics.ring_tac.

Lemma test1 `{SemiRing R}
  : forall x y : R, x + (y * x) = x * (y + 1).
Proof.
intros.
ring_with_nat.
Qed.

Require Import
  HoTT.Classes.interfaces.naturals.

Lemma test2 `{SemiRing R}
  : forall x y : R, x + (y * x) = x * (y + 1).
Proof.
intros.
apply (by_quoting (naturals_to_semiring nat R)).
compute. reflexivity.
Qed.

Lemma test3 `{SemiRing R}
  (pa pb pc : R) :
  pa * (pb * pc)
= pa * pb * pc.
Proof.
intros.
apply (by_quoting (naturals_to_semiring nat R)). compute.
reflexivity.
Qed.

Lemma test4 `{SemiRing R}
  (a b : R)
  : a * b = b * a.
Proof.
apply (ring_quote.Quoting.eval_eqquote R).
apply (prove_prequoted (naturals_to_semiring nat R)).
reflexivity.
Qed.

Lemma test5 : forall x y : nat, x + (y * x) = x * (y + 1).
Proof.
intros;ring_with_nat.
Qed.

