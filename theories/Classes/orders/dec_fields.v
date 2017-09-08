Require Import HoTT.Basics.Decidable.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.dec_fields.
Require Export
  HoTT.Classes.orders.rings.
Require Import HoTT.Classes.tactics.ring_tac.

Section contents.
Context `{DecField F} `{Apart F} `{!TrivialApart F}
  `{!FullPseudoSemiRingOrder Fle Flt} `{DecidablePaths F}.
(* Add Ring F : (stdlib_ring_theory F). *)

Instance pos_dec_recip_compat x : PropHolds (0 < x) -> PropHolds (0 < /x).
Proof.
intros E.
apply (strictly_order_reflecting (x *.)).
rewrite dec_recip_inverse by (apply orders.lt_ne_flip;trivial).
rewrite mult_0_r. solve_propholds.
Qed.

Instance nonneg_dec_recip_compat x : PropHolds (0 ≤ x) -> PropHolds (0 ≤ /x).
Proof.
intros E. red.
destruct (dec (x = 0)) as [E2 | E2].
- rewrite E2, dec_recip_0. rewrite E2 in E;trivial.
- apply lt_le. apply pos_dec_recip_compat.
  apply lt_iff_le_ne. split;trivial.
  apply symmetric_neq;trivial.
Qed.

Lemma neg_dec_recip_compat x : x < 0 -> /x < 0.
Proof.
intros. apply flip_neg_negate.
rewrite dec_recip_negate.
apply pos_dec_recip_compat.
apply flip_neg_negate. trivial.
Qed.

Lemma nonpos_dec_recip_compat x : x ≤ 0 -> /x ≤ 0.
Proof.
intros. apply flip_nonpos_negate.
rewrite dec_recip_negate.
apply nonneg_dec_recip_compat.
apply flip_nonpos_negate;trivial.
Qed.

Lemma flip_le_dec_recip x y : 0 < y -> y ≤ x  -> /x ≤ /y.
Proof.
intros E1 E2.
apply (order_reflecting_pos (.*.) x).
- apply lt_le_trans with y;trivial.
- rewrite dec_recip_inverse.
  + apply (order_reflecting_pos (.*.) y);trivial.
    rewrite (commutativity x), simple_associativity, dec_recip_inverse.
    * rewrite mult_1_l,mult_1_r. trivial.
    * apply lt_ne_flip;trivial.
  + apply lt_ne_flip.
    apply lt_le_trans with y;trivial.
Qed.

Lemma flip_le_dec_recip_l x y : 0 < y -> /y ≤ x  -> /x ≤ y.
Proof.
intros E1 E2.
rewrite <-(dec_recip_involutive y).
apply flip_le_dec_recip;trivial.
apply pos_dec_recip_compat;trivial.
Qed.

Lemma flip_le_dec_recip_r x y : 0 < y -> y ≤ /x  -> x ≤ /y.
Proof.
intros E1 E2.
rewrite <-(dec_recip_involutive x).
apply flip_le_dec_recip;trivial.
Qed.

Lemma flip_lt_dec_recip x y : 0 < y -> y < x  -> /x < /y.
Proof.
intros E1 E2.
assert (0 < x) by (transitivity y;trivial).
apply (strictly_order_reflecting (x *.)).
rewrite dec_recip_inverse.
- apply (strictly_order_reflecting (y *.)).
  rewrite (commutativity x), simple_associativity, dec_recip_inverse.
  + rewrite mult_1_l,mult_1_r. trivial.
  + apply lt_ne_flip. trivial.
- apply lt_ne_flip;trivial.
Qed.

Lemma flip_lt_dec_recip_l x y : 0 < y -> /y < x  -> /x < y.
Proof.
intros E1 E2.
rewrite <-(dec_recip_involutive y).
apply flip_lt_dec_recip; trivial.
apply pos_dec_recip_compat. trivial.
Qed.

Lemma flip_lt_dec_recip_r x y : 0 < y -> y < /x  -> x < /y.
Proof.
intros E1 E2.
rewrite <-(dec_recip_involutive x).
apply flip_lt_dec_recip;trivial.
Qed.
End contents.

(* Due to bug #2528 *)
Hint Extern 12 (PropHolds (0 ≤ _)) =>
  eapply @nonneg_dec_recip_compat : typeclass_instances.
Hint Extern 12 (PropHolds (0 < _)) =>
  eapply @pos_dec_recip_compat : typeclass_instances.
