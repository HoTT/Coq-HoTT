Require Import HoTT.Types.Universe.
Require Import
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.orders.nat_int
  HoTT.Classes.theory.integers
  HoTT.Classes.theory.rings
  HoTT.Classes.orders.rings.

Section contents.
Context `{Funext} `{Univalence}.
Context `{Integers Z} `{Apart Z} `{!TrivialApart Z}
  `{!FullPseudoSemiRingOrder Zle Zlt} `{Naturals N}.

(* Add Ring Z : (rings.stdlib_ring_theory Z). *)

Lemma int_abs_unique (a b : IntAbs Z N) (z : Z) :
  int_abs Z N (ia:=a) z = int_abs Z N (ia:=b) z.
Proof.
unfold int_abs.
destruct (int_abs_sig Z N (IntAbs:=a) z) as [[n1 E1]|[n1 E1]];
destruct (int_abs_sig Z N (IntAbs:=b) z) as [[n2 E2]|[n2 E2]].
- apply (injective (naturals_to_semiring N Z)). path_via z.
- assert (E : n1 + n2 = 0);[|path_via 0;[|symmetry];
  apply (naturals.zero_sum _ _ E)].
  apply (injective (naturals_to_semiring N Z)).
  rewrite preserves_0,preserves_plus.
  rewrite E1,E2.
  apply plus_negate_r.
- assert (E : n1 + n2 = 0);[|path_via 0;[|symmetry];
  apply (naturals.zero_sum _ _ E)].
  apply (injective (naturals_to_semiring N Z)).
  rewrite preserves_0,preserves_plus.
  rewrite E1,E2.
  apply plus_negate_l.
- apply (injective (naturals_to_semiring N Z)). path_via (- z).
Qed.

Context `{!IntAbs Z N}.

Context `{!SemiRingPreserving (f : N -> Z)}.

Lemma int_abs_spec x :
  (0 ≤ x /\ f (int_abs Z N x) = x) |_| (x ≤ 0 /\ f (int_abs Z N x) = -x).
Proof.
unfold int_abs. destruct (int_abs_sig Z N x) as [[n E]|[n E]].
- left. rewrite <-E. split.
  + eapply @to_semiring_nonneg;apply _.
  + apply (naturals.to_semiring_unique_alt _ _).
- right. split.
  + apply flip_nonpos_negate. rewrite <-E. eapply @to_semiring_nonneg;apply _.
  + rewrite <-E. apply (naturals.to_semiring_unique_alt _ _).
Qed.

Lemma int_abs_sig_alt x :
  (sig (fun n : N => f n = x)) |_| (sig (fun n : N => f n = - x)).
Proof. destruct (int_abs_spec x) as [[??]|[??]]; eauto. Qed.

Lemma int_abs_nat n :
  int_abs Z N (f n) = n.
Proof.
apply (injective f).
destruct (int_abs_spec (f n)) as [[? E]|[? E]];trivial.
apply naturals.negate_to_ring. rewrite E, involutive. trivial.
Qed.

Lemma int_abs_negate_nat n :
  int_abs Z N (-f n) = n.
Proof.
apply (injective f). destruct (int_abs_spec (-f n)) as [[? E]|[? E]].
- symmetry. apply naturals.negate_to_ring. apply symmetry; trivial.
- rewrite involutive in E. trivial.
Qed.

Lemma int_abs_negate x :
  int_abs Z N (-x) = int_abs Z N x.
Proof.
destruct (int_abs_spec x) as [[_ E]|[_ E]].
- path_via (int_abs Z N (- f (int_abs Z N x))).
  apply int_abs_negate_nat.
- rewrite <-E. apply int_abs_nat.
Qed.

Lemma int_abs_0_alt x : int_abs Z N x = 0 <-> x = 0.
Proof.
split; intros E1.
- destruct (int_abs_spec x) as [[_ E2]|[_ E2]];[|apply flip_negate_0];
  rewrite <-E2, E1, (preserves_0 (f:=f)); trivial.
- rewrite E1, <-(preserves_0 (f:=f)). apply int_abs_nat.
Qed.

Lemma int_abs_ne_0 x : int_abs Z N x <> 0 <-> x <> 0.
Proof.
destruct (int_abs_0_alt x).
split;intros E1 E2;auto.
Qed.

Lemma int_abs_0 : int_abs Z N 0 = 0.
Proof. apply int_abs_0_alt;trivial. Qed.

Lemma int_abs_nonneg x :
  0 ≤ x -> f (int_abs Z N x) = x.
Proof.
intros E1. destruct (int_abs_spec x) as [[n E2]|[n E2]];trivial.
assert (Hrw : x = 0).
- apply (antisymmetry (<=));trivial.
- rewrite Hrw,int_abs_0, (preserves_0 (f:=f)). trivial.
Qed.

Lemma int_abs_nonpos x :
  x ≤ 0 -> f (int_abs Z N x) = -x.
Proof.
intros E. rewrite <-int_abs_negate, int_abs_nonneg; auto.
apply flip_nonpos_negate. trivial.
Qed.

Lemma int_abs_1 : int_abs Z N 1 = 1.
Proof.
apply (injective f). rewrite (preserves_1 (f:=f)).
apply int_abs_nonneg; solve_propholds.
Qed.

Lemma int_abs_nonneg_plus x y :
  0 ≤ x -> 0 ≤ y -> int_abs Z N (x + y) = int_abs Z N x + int_abs Z N y.
Proof.
intros. apply (injective f).
rewrite (preserves_plus (f:=f)), !int_abs_nonneg;auto.
apply nonneg_plus_compat;trivial.
Qed.

Lemma int_abs_mult x y :
  int_abs Z N (x * y) = int_abs Z N x * int_abs Z N y.
Proof.
apply (injective f). rewrite (preserves_mult (f:=f)).
destruct (int_abs_spec x) as [[? Ex]|[? Ex]],
   (int_abs_spec y) as [[? Ey]|[? Ey]]; rewrite Ex, Ey.
- rewrite int_abs_nonneg;trivial. apply nonneg_mult_compat;trivial.
- rewrite int_abs_nonpos.
  + apply negate_mult_distr_r.
  + apply nonneg_nonpos_mult;trivial.
- rewrite int_abs_nonpos.
  + apply negate_mult_distr_l.
  + apply nonpos_nonneg_mult;trivial.
- rewrite int_abs_nonneg.
  + symmetry;apply negate_mult_negate.
  + apply nonpos_mult;trivial.
Qed.
End contents.
