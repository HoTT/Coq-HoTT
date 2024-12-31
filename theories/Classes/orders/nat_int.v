Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.naturals
  HoTT.Classes.theory.rings.
Require Export
  HoTT.Classes.orders.semirings.

Generalizable Variables N R f.

Section Univ.
Context `{Funext} `{Univalence}.

(*
We axiomatize the order on the naturals and the integers as a non trivial
pseudo semiring order that satisfies the biinduction principle. We prove
some results that hold for the order on the naturals and the integers.
In particular, we show that given another non trivial pseudo semiring order
(that not necessarily has to satisfy the biinduction principle, for example
the rationals or the reals), any morphism to it is an order embedding.
*)
Lemma to_semiring_nonneg `{FullPseudoSemiRingOrder N}
  `{!NaturalsToSemiRing N} `{!Naturals N} `{FullPseudoSemiRingOrder R}
  `{!IsSemiCRing R}
  `{!IsSemiRingPreserving (f : N -> R)} n : 0 ≤ f n.
Proof.
revert n. apply naturals.induction.
- rewrite (preserves_0 (f:=f)).
  reflexivity.
- intros n E.
  rewrite (preserves_plus (f:=f)), (preserves_1 (f:=f)).
  apply nonneg_plus_compat.
  + solve_propholds.
  + trivial.
Qed.

Section nat_int_order.
Context `{Naturals N} `{Apart N} `{Le N} `{Lt N} `{!FullPseudoSemiRingOrder le lt}
  `{FullPseudoSemiRingOrder R} `{!IsSemiCRing R}
  `{!Biinduction R} `{PropHolds (1 ≶ 0)}.

(* Add Ring R : (stdlib_semiring_theory R). *)

Lemma nat_int_to_semiring : forall x : R, exists z,
  x = naturals_to_semiring N R z |_| x + naturals_to_semiring N R z = 0.
Proof.
apply biinduction.
- exists 0.
  left. symmetry. apply preserves_0.
- intros. split;intros E.
  + destruct E as [z [E|E]].
    * exists (1+z).
      left. rewrite E.
      rewrite (preserves_plus (f:=naturals_to_semiring N R)),
      (preserves_1 (f:=naturals_to_semiring N R)). reflexivity.
    * destruct (naturals.case z) as [Ez|[z' Ez]].
      ** rewrite Ez in *.
         rewrite (preserves_0 (A:=N)),plus_0_r in E.
         rewrite E. exists 1. left.
         rewrite (preserves_1 (A:=N)),plus_0_r. reflexivity.
      ** rewrite Ez in *;clear z Ez.
         exists z';right.
         path_via (n + naturals_to_semiring N R (1 + z')).
         clear E. rewrite (preserves_plus (A:=N)),(preserves_1 (A:=N)).
         rewrite plus_assoc,(plus_comm n);reflexivity.
  + destruct E as [z [E|E]].
    * destruct (naturals.case z) as [Ez|[z' Ez]];rewrite Ez in *;clear z Ez.
      ** exists 1;right.
         rewrite (preserves_1 (A:=N)),plus_comm,E.
         apply preserves_0.
      ** exists z';left.
         rewrite (preserves_plus (A:=N)),(preserves_1 (A:=N)) in E.
         apply (left_cancellation plus 1). trivial.
    * exists (1+z).
      right. rewrite (preserves_plus (A:=N)), (preserves_1 (A:=N)),<-E.
      rewrite plus_assoc,(plus_comm n);reflexivity.
Qed.

Lemma nat_int_nonneg_decompose x : 0 ≤ x -> exists z, x = naturals_to_semiring N R z.
Proof.
destruct (nat_int_to_semiring x) as [z [Ez1 | Ez2]].
- exists z. trivial.
- intros E. exists 0. rewrite (preserves_0 (A:=N)).
  apply (antisymmetry (≤)); trivial.
  rewrite <-Ez2. apply nonneg_plus_le_compat_r.
  apply to_semiring_nonneg.
Qed.

Lemma nat_int_le_plus x y : x ≤ y <-> exists z, y = x + naturals_to_semiring N R z.
Proof.
split.
- intros E. destruct (decompose_le E) as [z [Ez1 Ez2]].
  destruct (nat_int_nonneg_decompose _ Ez1) as [u Eu].
  exists u. rewrite <-Eu. trivial.
- intros [z Ez]. rewrite Ez.
  apply nonneg_plus_le_compat_r, to_semiring_nonneg.
Qed.

Lemma nat_int_lt_plus x y : x < y <-> exists z, y = x + 1 + naturals_to_semiring N R z.
Proof.
split.
- intros E.
  destruct ((fst (nat_int_le_plus x y) (lt_le _ _ E))) as [z0 Ez].
  destruct (naturals.case z0) as [E1|[z E1]];rewrite E1 in *;clear z0 E1.
  + rewrite preserves_0, plus_0_r in Ez.
    destruct (lt_ne_flip x y);trivial.
  + exists z.
    rewrite (preserves_plus (A:=N)), preserves_1, plus_assoc in Ez.
    trivial.
- intros [z Ez]. rewrite Ez.
  apply nonneg_plus_lt_compat_r.
  + apply to_semiring_nonneg.
  + apply pos_plus_lt_compat_r; solve_propholds.
Qed.

Lemma lt_iff_plus_1_le x y : x < y <-> x + 1 ≤ y.
Proof.
etransitivity.
- apply nat_int_lt_plus.
- apply symmetry,nat_int_le_plus.
Qed.

Lemma lt_iff_S_le x y : x < y <-> 1 + x ≤ y.
Proof.
rewrite plus_comm. apply lt_iff_plus_1_le.
Qed.

Lemma pos_ge_1 x : 0 < x <-> 1 ≤ x.
Proof.
split; intros E.
- rewrite <-(plus_0_l 1). apply lt_iff_plus_1_le. trivial.
- apply lt_le_trans with 1; [solve_propholds | trivial].
Qed.

Lemma le_iff_lt_plus_1 x y : x ≤ y <-> x < y + 1.
Proof.
split; intros E.
- apply lt_iff_plus_1_le. apply (order_preserving (+1)). trivial.
- apply (order_reflecting (+1)), lt_iff_plus_1_le. trivial.
Qed.

Lemma le_iff_lt_S x y : x ≤ y <-> x < 1 + y.
Proof. rewrite plus_comm. apply le_iff_lt_plus_1. Qed.

Section another_semiring.
  Context `{FullPseudoSemiRingOrder R2} `{!IsSemiCRing R2}
    `{PropHolds ((1 : R2) ≶ 0)}
    `{!IsSemiRingPreserving (f : R -> R2)}.

  Instance: OrderPreserving f.
  Proof.
  repeat (split; try apply _).
  intros x y E. apply nat_int_le_plus in E. destruct E as [z E].
  rewrite E, (preserves_plus (f:=f)), (naturals.to_semiring_twice f _ _).
  apply nonneg_plus_le_compat_r. apply to_semiring_nonneg.
  Qed.

  Global Instance: StrictlyOrderPreserving f | 50.
  Proof.
  repeat (split; try apply _).
  intros x y E. apply nat_int_lt_plus in E. destruct E as [z E].
  rewrite E, !(preserves_plus (f:=f)), preserves_1,
  (naturals.to_semiring_twice f _ _).
  apply nonneg_plus_lt_compat_r.
  - apply to_semiring_nonneg.
  - apply pos_plus_lt_compat_r; solve_propholds.
  Qed.

  Global Instance nat_morphism_order_embedding : OrderEmbedding f | 50.
  Proof. split; try apply _. apply full_pseudo_order_reflecting. Qed.
End another_semiring.
End nat_int_order.
End Univ.
