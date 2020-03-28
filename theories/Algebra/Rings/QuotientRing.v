Require Import Basics Types WildCat.
Require Import Algebra.Congruence.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.CRing.
Require Import Algebra.Rings.Ideal.

(** In this file we define the quotient of a commuative ring by an ideal *)

Section QuotientRing.

  Context (R : CRing) (I : Ideal R).

  Instance plus_quotient_abgroup : Plus (QuotientAbGroup R I) := abgroup_sgop.

  Instance iscong_mult_incosetL
    : @IsCongruence R cring_mult (@in_cosetL R I _).
  Proof.
    snrapply Build_IsCongruence.
    intros x x' y y' [i p] [j q].
    change (issubgroup_incl (H:=R) i = (- x) + x') in p.
    change (issubgroup_incl (H:=R) j = (- y) + y') in q.
    unfold in_cosetL, hfiber.
    change {m : I & issubgroup_incl (H:=R) m = - (x * y) + (x' * y')}.
    rewrite <- (left_identity (op:=(+)) (x' * y') : 0 + (x' * y') = x' * y').
    rewrite <- (right_inverse (op:=(+)) (x' * y) : (x' * y) - (x' * y) = 0).
    rewrite 2 simple_associativity.
    rewrite negate_mult_distr_l.
    rewrite <- simple_distribute_r.
    rewrite <- simple_associativity.
    rewrite negate_mult_distr_r.
    rewrite <- simple_distribute_l.
    rewrite <- p, <- q.
    pose (isideal x' j) as s; destruct s as [s s'].
    pose (isideal y i) as t; destruct t as [t t'].
    rewrite (commutativity _ y).
    rewrite <- s', <- t'.
    exists (sg_op t s).
    rapply grp_homo_op.
  Defined.

  Instance mult_quotient_abgroup : Mult (QuotientAbGroup R I).
  Proof.
    intro x.
    srapply Quotient_rec.
    { intro y; revert x.
      srapply Quotient_rec.
      { intro x.
        apply class_of.
        exact (x * y). }
      intros x x' p.
      apply qglue.
      by rapply iscong. }
    intros y y' q.
    revert x.
    srapply Quotient_ind_hprop.
    intro x.
    simpl.
    apply qglue.
    by rapply iscong.
  Defined.

  Instance zero_quotient_abgroup : Zero (QuotientAbGroup R I) := class_of _ zero.
  Instance one_quotient_abgroup : One (QuotientAbGroup R I) := class_of _ one.

  Instance isring_quotient_abgroup : IsRing (QuotientAbGroup R I).
  Proof.
    split.
    1: exact _.
    1: repeat split.
    1: exact _.
    (** Associativity follows from the underlying operation *)
    { intros x y.
      snrapply Quotient_ind_hprop; [exact _ | intro z; revert y].
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x ].
      unfold sg_op, mult_is_sg_op, mult_quotient_abgroup; simpl.
      apply ap.
      apply associativity. }
    (* Left and right identity follow from the underlying structure *)
    1,2: snrapply Quotient_ind_hprop; [exact _ | intro x].
    1-2: unfold sg_op, mult_is_sg_op, mult_quotient_abgroup; simpl.
    1-2: apply ap.
    1: apply left_identity.
    1: apply right_identity.
    (** Commutativity also follows *)
    { intros x.
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x].
      unfold sg_op, mult_is_sg_op, mult_quotient_abgroup; simpl.
      apply ap.
      apply commutativity. }
    (** Finally distributivity also follows *)
    { intros x y.
      snrapply Quotient_ind_hprop; [exact _ | intro z; revert y].
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x ].
      unfold sg_op, mult_is_sg_op, mult_quotient_abgroup,
        plus, mult, plus_quotient_abgroup; simpl.
      apply ap.
      apply simple_distribute_l. }
  Defined.

  Definition QuotientRing : CRing 
    := Build_CRing (QuotientAbGroup R I) _ _ _ _ _ _.

End QuotientRing.

(** TODO; move *)
(** Here is an alternative way to build a commutative ring using the underlying abelian group. *)
Definition Build_CRing' (R : AbGroup)
  `(Mult R, One R, LeftDistribute R mult abgroup_sgop)
  (iscomm : @IsCommutativeMonoid R mult one)
  : CRing
  := Build_CRing R abgroup_sgop _ abgroup_unit _
      abgroup_inverse (Build_IsRing _ _ _ _).

(** TODO: move *)
Definition rng_image {R S : CRing} (f : CRingHomomorphism R S) : CRing.
Proof.
  snrapply (Build_CRing' (abgroup_image f)).
  { simpl.
    intros [x p] [y q].
    exists (x * y).
    strip_truncations; apply tr.
    destruct p as [p p'], q as [q q'].
    exists (p * q).
    refine (rng_homo_mult _ _ _ @ _).
    f_ap. }
  { exists 1.
    apply tr.
    exists 1.
    exact (rng_homo_one f). }
  (** Much of this proof is doing the same thing over, so we use some compact tactics. *)
  2: repeat split.
  2: exact _.
  all: intros [].
  1,2,5: intros [].
  1,2: intros [].
  all: apply path_sigma_hprop; cbn.
  1: apply distribute_l.
  1: apply associativity.
  1: apply commutativity.
  1: apply left_identity.
  apply right_identity.
Defined.

(** First isomorphism theorem for rings *)
Section FirstIso.

  Context `{Funext} {A B : CRing} (phi : A $-> B).

  (** First we define a map from the quotient by the kernel of phi into the image of phi *)
  Definition rng_image_quotient
    : CRingHomomorphism (QuotientRing A (ideal_kernel phi)) (rng_image phi).
  Proof.
  Admitted.

  (** The underlying map of this homomorphism is an equivalence *)
  Global Instance isequiv_grp_image_quotient : IsEquiv rng_image_quotient.
  Proof.
(*     snrapply isequiv_surj_emb.
    1: srapply cancelR_conn_map.
    srapply isembedding_isinj_hset.
    refine (Quotient_ind_hprop _ _ _); intro x.
    refine (Quotient_ind_hprop _ _ _); intro y.
    intros h; simpl in h.
    apply qglue.
    srefine (_;_).
    { exists (-x * y).
      apply (equiv_path_sigma_hprop _ _)^-1%equiv in h; cbn in h.
      rewrite grp_homo_op, grp_homo_inv, h.
      srapply negate_l. }
    reflexivity. *)
  Admitted.

  (** First isomorphism theorem for commutative rings *)
  Theorem rng_first_iso
    : CRingIsomorphism (QuotientRing A (ideal_kernel phi)) (rng_image phi).
  Proof.
    exact (Build_CRingIsomorphism _ _ rng_image_quotient _).
  Defined.

End FirstIso.
