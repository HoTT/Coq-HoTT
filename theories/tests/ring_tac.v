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

Import ring_pol. Import ring_quote.Quoting.

Lemma test3 `{SemiRing R}
  (pa pb pc na nb nc : R) : ( pa * (pb * pc + nb * nc) + na * (pb * nc + nb * pc) +
((pa * pb + na * nb) * nc + (pa * nb + na * pb) * pc)
≡ (pa * pb + na * nb) * pc + (pa * nb + na * pb) * nc +
  (pa * (pb * nc + nb * pc) + na * (pb * pc + nb * nc))).
Proof.
intros.
apply (normalize_eq (naturals_to_semiring nat R)).
compute.
change Aplus with (@plus R Aplus);change Amult with (@mult R Amult);
change Azero with (@zero R Azero);change Aone with (@one R Aone).
Abort.