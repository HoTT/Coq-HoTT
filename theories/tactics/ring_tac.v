Require Import HoTT.Basics HoTT.Types.Bool.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.theory.additional_operations
  HoTTClasses.tactics.ring_quote
  HoTTClasses.tactics.ring_pol
  HoTTClasses.theory.rings
  HoTTClasses.orders.sum
  HoTTClasses.misc.decision
  HoTTClasses.implementations.peano_naturals
  HoTTClasses.interfaces.naturals.

Section content.

Context `{DecidablePaths C}.

Context `(phi : C -> R) `{SemiRing_Morphism C R phi}.

Notation Vars V := (V -> R).

Lemma normalize_eq `{Q : @Quoting.EqQuote R _ _ _ _ V l n m V' l'}
  `{Trichotomy V Vlt} `{Trichotomy V' Vlt'}
  : eval phi (Quoting.merge R l l')
  (toPol (Quoting.expr_map inl (Quoting.eqquote_l R)))
  ≡ eval phi (Quoting.merge R l l') (toPol (Quoting.eqquote_r R))
  -> n = m.
Proof.
pose proof semiringmor_a.
pose proof semiringmor_b.
intros E.
eapply Quoting.eval_eqquote.
etransitivity;[symmetry;apply (eval_toPol _)|].
etransitivity;[|apply (eval_toPol _)].
exact E.
Qed.

Lemma by_quoting `{Q : @Quoting.EqQuote R _ _ _ _ V l n m V' l'}
  `{Trichotomy V Vlt} `{Trichotomy V' Vlt'}
  : toPol (Quoting.expr_map inl (@Quoting.eqquote_l R _ _ _ _ _ _ _ _ _ _ Q))
  =? toPol (@Quoting.eqquote_r R  _ _ _ _ _ _ _ _ _ _ Q) = true
  -> n = m.
Proof.
intros E.
apply normalize_eq.
apply eval_eqb,E.
Qed.

End content.

Arguments normalize_eq {C _ R} phi {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments by_quoting {C _ R} phi {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.

Ltac ring_with_nat :=
  match goal with
  |- @paths ?R _ _ =>
    apply (by_quoting (naturals_to_semiring nat R));
    compute;reflexivity
  end.