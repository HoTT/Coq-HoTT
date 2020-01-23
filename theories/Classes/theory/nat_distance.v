Require Import HoTT.Types.Universe.
Require Import
  HoTT.Classes.orders.naturals
  HoTT.Classes.implementations.peano_naturals.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.naturals
  HoTT.Classes.theory.additional_operations.


Generalizable Variables N.

Section contents.
Context `{Funext} `{Univalence}.
Context `{Naturals N}.
(* Add Ring N : (rings.stdlib_semiring_theory N). *)

(* NatDistance instances are all equivalent, because their behavior is fully
 determined by the specification. *)
Lemma nat_distance_unique {a b : NatDistance N}
  : forall x y, @nat_distance _ _ a x y = @nat_distance _ _ b x y.
Proof.
intros. unfold nat_distance.
destruct (@nat_distance_sig _ _ a x y) as [[z1 E1]|[z1 E1]],
(@nat_distance_sig _ _ b x y) as [[z2 E2]|[z2 E2]];simpl.
- apply (left_cancellation plus x). path_via y.
- rewrite <-(rings.plus_0_r y),<-E2,<-rings.plus_assoc in E1.
  apply (left_cancellation plus y) in E1. apply naturals.zero_sum in E1.
  destruct E1;path_via 0.
- rewrite <-(rings.plus_0_r x),<-E2,<-rings.plus_assoc in E1.
  apply (left_cancellation plus x) in E1. apply naturals.zero_sum in E1.
  destruct E1;path_via 0.
- apply (left_cancellation plus y);path_via x.
Qed.

End contents.

(* An existing instance of [CutMinus]
   allows to create an instance of [NatDistance] *)
Instance natdistance_cut_minus `{Naturals N} `{!TrivialApart N}
   {cm} `{!CutMinusSpec N cm} `{forall x y, Decidable (x ≤ y)} : NatDistance N.
Proof.
red. intros. destruct (decide_rel (<=) x y) as [E|E].
- left. exists (y ∸ x).
  rewrite rings.plus_comm;apply cut_minus_le;trivial.
- right. exists (x ∸ y).
  rewrite rings.plus_comm;apply cut_minus_le, orders.le_flip;trivial.
Defined.

(* Using the preceding instance we can make an instance
   for arbitrary models of the naturals
   by translation into [nat] on which we already have a [CutMinus] instance. *)
Global Instance natdistance_default `{Naturals N} : NatDistance N | 10.
Proof.
intros x y.
destruct (nat_distance_sig (naturals_to_semiring N nat x)
  (naturals_to_semiring N nat y)) as [[n E]|[n E]].
- left. exists (naturals_to_semiring nat N n).
  rewrite <-(naturals.to_semiring_involutive N nat y), <-E.
  rewrite (rings.preserves_plus (A:=nat)), (naturals.to_semiring_involutive _ _).
  split.
- right. exists (naturals_to_semiring nat N n).
  rewrite <-(naturals.to_semiring_involutive N nat x), <-E.
  rewrite (rings.preserves_plus (A:=nat)), (naturals.to_semiring_involutive _ _).
  split.
Defined.
