Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations
  HoTTClasses.theory.premetric
  HoTTClasses.IR.cauchy_completion.

Require Export
  HoTTClasses.IR.cauchy_reals.base.

Local Set Universe Minimization ToSet.

Section real_initial.

Context `{Field F} `{!FullPseudoSemiRingOrder (A:=F) Fle Flt}.

Variable F_archimedean : forall x y : F, x < y ->
  merely (exists q, x < rationals_to_field Q F q < y).

Instance Fclose : Closeness F := fun e x y =>
  x - y < rationals_to_field Q F (' e) /\ y - x < rationals_to_field Q F (' e).

Instance rat_to_field_strict_order_embedding
  : StrictOrderEmbedding (rationals_to_field Q F).
Proof.
Admitted.

Lemma F_separated : Separated F.
Proof.
intros x y E.
apply (right_cancellation (+) (-y)). rewrite plus_negate_r.
apply tight_apart. intros E'. apply apart_iff_total_lt in E'.
destruct E' as [E'|E'];apply F_archimedean in E';revert E';apply (Trunc_ind _);
intros [q [E1 E2]].
- assert (Eq : 0 < - q).
  { rewrite <-(preserves_0 (f:=rationals_to_field Q F)) in E2.
    apply (strictly_order_reflecting _) in E2.
    apply flip_neg_negate. trivial.
  }
  pose proof (E (mkQpos _ Eq)) as [E3 E4];unfold cast in E3,E4;simpl in E3, E4.
  rewrite (preserves_negate (f:=rationals_to_field Q F)) in E4.
  apply flip_lt_negate in E4;rewrite involutive,<-negate_swap_r in E4.
  apply (irreflexivity lt (x - y)). transitivity (rationals_to_field Q F q);trivial.
- assert (Eq : 0 < q).
  { apply (strictly_order_reflecting _). rewrite preserves_0. trivial. }
  pose proof (E (mkQpos _ Eq)) as [E3 E4];unfold cast in E3,E4;simpl in E3, E4.
  apply (irreflexivity lt (x - y)). transitivity (rationals_to_field Q F q);trivial.
Qed.

Instance F_premetric : PreMetric F.
Proof.
split.
- apply _.
- intros e x. hnf. rewrite plus_negate_r.
  split;rewrite <-(preserves_0 (f:=rationals_to_field Q F));
  apply (strictly_order_preserving _);solve_propholds.
- intros e x y E. hnf. apply prod_symm,E.
- apply F_separated.
- intros x y z e d E1 E2.
  hnf. rewrite (preserves_plus (f:=_:Q -> F)).
  split.
  + assert (Hrw : x - z = (x - y) + (y - z))
      by ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw;clear Hrw. apply plus_lt_compat.
    * apply E1.
    * apply E2.
  + assert (Hrw : z - x = (y - x) + (z - y))
      by ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw;clear Hrw. apply plus_lt_compat.
    * apply E1.
    * apply E2.
- hnf. intros e x y. split.
  + intros [E1 E2].
    apply F_archimedean in E1;apply F_archimedean in E2.
    revert E1;apply (Trunc_ind _);intros [q1 [E1 E1']];
    revert E2;apply (Trunc_ind _);intros [q2 [E2 E2']].
    apply (strictly_order_reflecting _) in E1';
    apply (strictly_order_reflecting _) in E2'.
    assert (E3 : exists d d', q1 < ' d /\ q2 < ' d /\ e = d + d').
    { apply pos_gt_both;trivial. }
    destruct E3 as [d [d' [E3 [E4 E5]]]].
    apply tr;exists d,d';split;trivial.
    hnf. split;etransitivity;eauto;apply (strictly_order_preserving _);trivial.
  + apply (Trunc_ind _);intros [d [d' [E1 [E2 E3]]]].
    assert (rationals_to_field Q F (' d) < rationals_to_field Q F (' e))
      by (apply (strictly_order_preserving _); rewrite E1;
          apply pos_plus_lt_compat_r; solve_propholds).
    split;etransitivity;eauto.
Qed.

Context `{!Lim F} `{!CauchyComplete F}.

Definition real_embed : real -> F.
Proof.
simple refine (lipschitz_extend Q (rationals_to_field Q F) 1);try apply _.
apply nonexpanding_lipschitz.
hnf. intros e q r [E1 E2].
hnf. rewrite <-!preserves_negate,<-!preserves_plus.
apply flip_lt_negate in E1. rewrite involutive,<-negate_swap_r in E1.
split;apply (strictly_order_preserving _);trivial.
Defined.

Definition real_embed_rat q : real_embed (rat q) = rationals_to_field Q F q
  := idpath.

(* To show that real_embed preserves plus/mult
   we need to know that they're continuous on F. *)

End real_initial.
