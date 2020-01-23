Require Import HoTT.Basics HoTT.Types.Bool.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.theory.additional_operations
  HoTT.Classes.tactics.ring_quote
  HoTT.Classes.tactics.ring_pol
  HoTT.Classes.theory.rings
  HoTT.Classes.orders.sum
  HoTT.Classes.implementations.peano_naturals
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.integers.

Generalizable Variables A B C R V f l n m Vlt.

Import Quoting.Instances.

Section content.
Context `{DecidablePaths C}.

Context `(phi : C -> R) `{AlmostRingPreserving C R phi}
  `{!AlmostRing C} `{!AlmostRing R}.

Lemma normalize_eq `{Q : @Quoting.EqQuote R _ _ _ _ _ V l n m V' l'}
  `{Trichotomy V Vlt} `{Trichotomy V' Vlt'}
  : eval phi (Quoting.merge R l l')
  (toPol (Quoting.expr_map inl (Quoting.eqquote_l R)))
  = eval phi (Quoting.merge R l l') (toPol (Quoting.eqquote_r R))
  -> n = m.
Proof.
intros E.
eapply Quoting.eval_eqquote.
etransitivity;[symmetry;apply (eval_toPol _)|].
etransitivity;[|apply (eval_toPol _)].
exact E.
Qed.

Lemma by_quoting `{Q : @Quoting.EqQuote R _ _ _ _ _ V l n m V' l'}
  `{Trichotomy V Vlt} `{Trichotomy V' Vlt'}
  : toPol (Quoting.expr_map inl (@Quoting.eqquote_l R _ _ _ _ _ _ _ _ _ _ _ Q))
  =? toPol (@Quoting.eqquote_r R  _ _ _ _ _ _ _ _ _ _ _ Q) = true
  -> n = m.
Proof.
intros E.
apply normalize_eq.
apply eval_eqb,E.
Qed.

Lemma normalize_prequoted `{Trichotomy V Vlt} (a b : Quoting.Expr V) vs
  : eval phi vs (toPol a) = eval phi vs (toPol b) ->
  Quoting.eval _ vs a = Quoting.eval _ vs b.
Proof.
rewrite !(eval_toPol _).
trivial.
Qed.

Lemma prove_prequoted `{Trichotomy V Vlt} (a b : Quoting.Expr V) vs
  : toPol a =? toPol b = true -> Quoting.eval _ vs a = Quoting.eval _ vs b.
Proof.
intros.
apply normalize_prequoted.
apply eval_eqb;trivial.
Qed.

End content.

Instance default_almostneg `{Zero A} : AlmostNegate A | 20
  := fun _ => 0.
Arguments default_almostneg _ _ _ /.

Instance negate_almostneg `{Aneg : Negate A} : AlmostNegate A
  := (-).
Arguments negate_almostneg _ _ _ /.

Instance semiring_almostring `{IsSemiRing A} : AlmostRing A | 10.
Proof.
split;try apply _.
intros. unfold almost_negate;simpl.
symmetry;apply mult_0_l.
Qed.

Instance ring_almostring `{IsRing A} : AlmostRing A.
Proof.
split;try apply _.
intros. unfold almost_negate;simpl.
apply negate_mult.
Qed.

Instance sr_mor_almostring_mor `{IsSemiRingPreserving A B f}
  : AlmostRingPreserving f | 10.
Proof.
split;try apply _.
unfold almost_negate;simpl. intros _. apply preserves_0.
Qed.

Section VarSec.
Context `{IsRing A} `{IsRing B} {f : A -> B} `{!IsSemiRingPreserving f}.

Global Instance ring_mor_almostring_mor : AlmostRingPreserving f.
Proof.
split;try apply _.
unfold almost_negate;simpl. apply preserves_negate.
Qed.

End VarSec.

Arguments normalize_eq {C _ R} phi
  {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments by_quoting {C _ R} phi
  {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.

Ltac ring_with_nat :=
  match goal with
  |- @paths ?R _ _ =>
    ((pose proof (_ : IsSemiRing R)) || fail "target equality not on a semiring");
    apply (by_quoting (naturals_to_semiring nat R));
    compute;reflexivity
  end.

Ltac ring_with_integers Z :=
  match goal with
  |- @paths ?R _ _ =>
    ((pose proof (_ : IsRing R)) || fail "target equality not on a ring");
    apply (by_quoting (integers_to_ring Z R));
    compute;reflexivity
  end.

Ltac ring_with_self :=
  match goal with
  |- @paths ?R _ _ =>
    ((pose proof (_ : IsSemiRing R)) || fail "target equality not on a ring");
    apply (by_quoting (@id R));
    compute;reflexivity
  end.

Ltac ring_repl a b :=
  let Hrw := fresh "Hrw" in
  assert (Hrw : a = b);[ring_with_nat|rewrite Hrw;clear Hrw].

Tactic Notation "ring_replace" constr(x) "with" constr(y) := ring_repl x y.
