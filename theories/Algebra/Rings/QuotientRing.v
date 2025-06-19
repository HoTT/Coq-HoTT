Require Import WildCat.Core WildCat.Equiv.
Require Import Algebra.Congruence.
Require Import Algebra.AbGroups.
Require Import Classes.interfaces.abstract_algebra.
Require Import Algebra.Rings.Ring.
Require Import Algebra.Rings.Ideal.

(** * Quotient Rings *)

(** In this file we define the quotient of a ring by an ideal. *)

Import Ideal.Notation.
Local Open Scope predicate_scope.
Local Open Scope ring_scope.
Local Open Scope wc_iso_scope.

Section QuotientRing.

  Context (R : Ring) (I : Ideal R).

  Instance plus_quotient_group : Plus (QuotientAbGroup R I) := group_sgop.

  Instance iscong_mult_incosetL
    : @IsCongruence R ring_mult (in_cosetL I).
  Proof.
    snapply Build_IsCongruence.
    intros x x' y y' p q.
    change (I ( - (x * y) + (x' * y'))).
    rewrite <- (rng_plus_zero_l (x' * y')).
    rewrite <- (rng_plus_negate_r (x' * y)).
    rewrite 2 rng_plus_assoc.
    rewrite <- rng_mult_negate_l.
    rewrite <- rng_dist_r.
    rewrite <- rng_plus_assoc.
    rewrite <- rng_mult_negate_r.
    rewrite <- rng_dist_l.
    rapply subgroup_in_op.
    - by rapply isrightideal.
    - by rapply isleftideal.
  Defined.

  Instance mult_quotient_group : Mult (QuotientAbGroup R I).
  Proof.
    srapply Quotient_rec2.
    - exact (fun x y => class_of _ (x * y)).
    - intros x x' y p. apply qglue. by apply iscong.
    - intros x y y' q. apply qglue. by apply iscong.
  Defined.

  Instance one_quotient_abgroup : One (QuotientAbGroup R I) := class_of _ one.

  Instance isring_quotient_abgroup : IsRing (QuotientAbGroup R I).
  Proof.
    split.
    1: exact _.
    1: repeat split.
    1: exact _.
    (** Associativity follows from the underlying operation *)
    { srapply Quotient_ind3_hprop; intros x y z.
      unfold mult, sg_op; simpl.
      apply ap.
      apply associativity. }
    (* Left and right identity follow from the underlying structure *)
    1,2: snapply Quotient_ind_hprop; [exact _ | intro x].
    1,2: unfold mult, sg_op; simpl.
    1-2: apply ap.
    1: apply left_identity.
    1: apply right_identity.
    (** Finally distributivity also follows *)
    { srapply Quotient_ind3_hprop; intros x y z.
      unfold sg_op, mult_is_sg_op, mult_quotient_group,
        plus, mult, plus_quotient_group; simpl.
      napply ap.
      apply simple_distribute_l. }
    { srapply Quotient_ind3_hprop; intros x y z.
      unfold sg_op, mult_is_sg_op, mult_quotient_group,
        plus, mult, plus_quotient_group; simpl.
      napply ap.
      apply simple_distribute_r. }
  Defined.

  Definition QuotientRing : Ring
    := Build_Ring (QuotientAbGroup R I) _ _ _ _ _ _ _.

End QuotientRing.

Infix "/" := QuotientRing : ring_scope.

(** Quotient map *)
Definition rng_quotient_map {R : Ring} (I : Ideal R)
  : RingHomomorphism R (R / I).
Proof.
  snapply Build_RingHomomorphism'.
  1: exact grp_quotient_map.
  repeat split.
Defined.

Instance issurj_rng_quotient_map {R : Ring} (I : Ideal R)
  : IsSurjection (rng_quotient_map I).
Proof.
  exact _.
Defined.

(** *** Specialized induction principles *)

(** We provide some specialized induction principles for [QuotientRing] that require cleaner hypotheses than the ones given by [Quotient_ind]. *)
Definition QuotientRing_ind {R : Ring} {I : Ideal R} (P : R / I -> Type)
  `{forall x, IsHSet (P x)}
  (c : forall (x : R), P (rng_quotient_map I x))
  (g : forall (x y : R) (h : I (- x + y)), qglue h # c x = c y)
  : forall (r : R / I), P r
  := Quotient_ind _ P c g.

(** And a version eliminating into hprops. This one is especially useful. *)
Definition QuotientRing_ind_hprop {R : Ring} {I : Ideal R} (P : R / I -> Type)
  `{forall x, IsHProp (P x)} (c : forall (x : R), P (rng_quotient_map I x))
  : forall (r : R / I), P r
  := Quotient_ind_hprop _ P c.

Definition QuotientRing_ind2_hprop {R : Ring} {I : Ideal R} (P : R / I -> R / I -> Type)
  `{forall x y, IsHProp (P x y)}
  (c : forall (x y : R), P (rng_quotient_map I x) (rng_quotient_map I y))
  : forall (r s : R / I), P r s
  := Quotient_ind2_hprop _ P c.

Definition QuotientRing_rec {R : Ring} {I : Ideal R} (S : Ring)
  (f : R $-> S) (H : forall x, I x -> f x = 0) 
  : R / I $-> S.
Proof.
  snapply Build_RingHomomorphism'.
  - snapply (grp_quotient_rec _ _ f).
    exact H.
  - split.
    + srapply QuotientRing_ind2_hprop.
      napply rng_homo_mult.
    + napply rng_homo_one.
Defined.

(** ** Quotient theory *)

(** First isomorphism theorem for commutative rings *)
Definition rng_first_iso `{Funext} {A B : Ring} (f : A $-> B)
  : A / ideal_kernel f ≅ rng_image f.
Proof.
  snapply Build_RingIsomorphism''.
  1: rapply abgroup_first_iso.
  split.
  { srapply QuotientRing_ind2_hprop; intros x y.
    srapply path_sigma_hprop.
    exact (rng_homo_mult _ _ _). }
  srapply path_sigma_hprop.
  exact (rng_homo_one _).
Defined.

(** Invariance of equal ideals *)
Lemma rng_quotient_invar {R : Ring} {I J : Ideal R} (p : (I ↔ J)%ideal)
  : R / I ≅ R / J.
Proof.
  snapply Build_RingIsomorphism'.
  { srapply equiv_quotient_functor'.
    1: exact equiv_idmap.
    intros x y; cbn.
    apply p. }
  repeat split.
  1,2: srapply Quotient_ind2_hprop; intros x y; rapply qglue.
  1: change (J ( - (x + y) + (x + y))).
  2: change (J (- ( x * y) + (x * y))).
  1,2: rewrite rng_plus_negate_l.
  1,2: apply ideal_in_zero.
Defined.

(** We phrase the first ring isomorphism theorem in a slightly different way so that it is easier to use. This form specifically asks for a surjective map *)
Definition rng_first_iso' `{Funext} {A B : Ring} (f : A $-> B)
  (issurj_f : IsSurjection f)
  (I : Ideal A) (p : (I ↔ ideal_kernel f)%ideal)
  : A / I ≅ B.
Proof.
  etransitivity.
  1: exact (rng_quotient_invar p).
  etransitivity.
  2: exact (rng_image_issurj f).
  apply rng_first_iso.
Defined.

