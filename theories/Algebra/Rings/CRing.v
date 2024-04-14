Require Import WildCat.
Require Import Spaces.Nat.Core.
(* Some of the material in abstract_algebra and canonical names could be selectively exported to the user, as is done in Groups/Group.v. *)
Require Import Classes.interfaces.abstract_algebra.
Require Import Algebra.AbGroups.
Require Export Algebra.Rings.Ring Algebra.Rings.Ideal.

(** * Commutative Rings *)

Local Open Scope ring_scope.
Local Open Scope wc_iso_scope.

(** A commutative ring consists of the following data: *)
Record CRing := {
  (** An underlying abelian group. *)
  cring_abgroup :> AbGroup;
  (** A multiplication operation. *)
  cring_mult :: Mult cring_abgroup;
  (** A multiplicative identity. *)
  cring_one :: One cring_abgroup;
  (** Such that they satisfy the axioms of a ring. *)
  cring_iscring :: IsCRing cring_abgroup;
}.

Arguments cring_mult {_}.
Arguments cring_one {_}.
Arguments cring_iscring {_}.

Definition issig_CRing : _ <~> CRing := ltac:(issig).

Global Instance cring_plus {R : CRing} : Plus R := plus_abgroup (cring_abgroup R).
Global Instance cring_zero {R : CRing} : Zero R := zero_abgroup (cring_abgroup R).
Global Instance cring_negate {R : CRing} : Negate R := negate_abgroup (cring_abgroup R).

Definition ring_cring : CRing -> Ring
  := fun R => Build_Ring (cring_abgroup R) (cring_mult) (cring_one) _.
Coercion ring_cring : CRing >-> Ring.

Definition Build_CRing' (R : Ring) (H : Commutative (@ring_mult R)) : CRing.
Proof.
  rapply (Build_CRing R).
  split; try exact _.
  split; exact _.
Defined.

(** ** Properties of commutative rings *)

Definition rng_mult_comm {R : CRing} (x y : R) : x * y = y * x := commutativity x y.

(** Powers commute with multiplication *)
Lemma rng_power_mult {R : CRing} (x y : R) (n : nat)
  : rng_power (R:=R) (x * y) n = rng_power (R:=R) x n * rng_power (R:=R) y n.
Proof.
  induction n.
  1: symmetry; rapply rng_mult_one_l.
  simpl.
  rewrite (rng_mult_assoc (A:=R)).
  rewrite <- (rng_mult_assoc (A:=R) x _ y).
  rewrite (rng_mult_comm (rng_power (R:=R) x n) y).
  rewrite rng_mult_assoc.
  rewrite <- (rng_mult_assoc _ (rng_power (R:=R) x n)).
  f_ap.
Defined.

(** ** Ideals in commutative rings *)
  
Section IdealCRing.
  Context {R : CRing}.
  
  (** The section is meant to complement the IdealLemmas section in Algebra.Rings.Ideal. Since the results here only hold in commutative rings, they have to be kept here. *)
  
  (** We import ideal notations as used in Algebra.Rings.Ideal but only for this section. Important to note is that [↔] corresponds to equality of ideals. *)
  Import Ideal.Notation.
  Local Open Scope ideal_scope.

  (** In a commutative ring, the product of two ideals is a subset of the reversed product. *)
  Lemma ideal_product_subset_product_commutative (I J : Ideal R)
    : I ⋅ J ⊆ J ⋅ I.
  Proof.
    intros r p.
    strip_truncations.
    induction p as [r p | |].
    2: apply ideal_in_zero.
    2: by apply ideal_in_plus_negate.
    destruct p as [s t p q].
    rewrite rng_mult_comm.
    apply tr.
    apply sgt_in.
    by rapply ipn_in.
  Defined.

  (** Ideal products are commutative in commutative rings. Note that we are using ideal notations here and [↔] corresponds to equality of ideals. Essentially a subset in each direction. *)
  Lemma ideal_product_comm (I J : Ideal R) : I ⋅ J ↔ J ⋅ I.
  Proof.
    apply ideal_subset_antisymm;
    apply ideal_product_subset_product_commutative.
  Defined.
  
  (** Product of intersection and sum is a subset of product. Note that this is a generalization of lcm * gcd = product *)
  Lemma ideal_product_intersection_sum_subset' (I J : Ideal R)
    : (I ∩ J) ⋅ (I + J) ⊆ I ⋅ J.
  Proof.
    etransitivity.
    2: rapply ideal_sum_self.
    etransitivity.
    2: rapply ideal_sum_subset_pres_r.
    2: rapply ideal_product_comm.
    apply ideal_product_intersection_sum_subset.
  Defined.
 
  (** If the sum of ideals is the whole ring then their intersection is a subset of their product. *)
  Lemma ideal_intersection_subset_product (I J : Ideal R)
    : ideal_unit R ⊆ (I + J) -> I ∩ J ⊆ I ⋅ J.
  Proof.
    intros p.
    etransitivity.
    { apply ideal_eq_subset.
      symmetry.
      apply ideal_product_unit_r. }
    etransitivity.
    1: rapply (ideal_product_subset_pres_r _ _ _ p).
    rapply ideal_product_intersection_sum_subset'.
  Defined.

  (** This can be combined into a sufficient (but not necessary) condition for equality of intersections and products. *)
  Lemma ideal_intersection_is_product (I J : Ideal R)
    : Coprime I J -> I ∩ J ↔ I ⋅ J.
  Proof.
    intros p.
    apply ideal_subset_antisymm.
    - apply ideal_intersection_subset_product.
      unfold Coprime in p.
      apply symmetry in p.
      rapply p.
    - apply ideal_product_subset_intersection.
  Defined.

  Lemma ideal_quotient_product (I J K : Ideal R)
    : (I :: J) :: K ↔ (I :: (J ⋅ K)).
  Proof.
    apply ideal_subset_antisymm.
    - intros x p; simpl in p.
      strip_truncations; apply tr.
      intros y q.
      strip_truncations.
      induction q as [y i | | ? ? ? [] ? [] ].
      + destruct i as [ y z s t ].
        destruct (p z t) as [p' p''].
        strip_truncations.
        destruct (p' y s) as [q q'], (p'' y s) as [q'' q'''].
        rewrite <- rng_mult_assoc.
        rewrite (rng_mult_comm y).
        rewrite rng_mult_assoc.
        by split.
      + rewrite rng_mult_zero_l, rng_mult_zero_r.
        split; apply ideal_in_zero.
      + rewrite rng_dist_l, rng_dist_r.
        rewrite rng_mult_negate_l, rng_mult_negate_r.
        split; by apply ideal_in_plus_negate.
    - intros x p; strip_truncations; apply tr; intros y k.
      split; apply tr; intros z j.
      + rewrite <- rng_mult_assoc.
        rewrite (rng_mult_comm x y).
        rewrite 2 rng_mult_assoc, <- rng_mult_assoc.
        rewrite (rng_mult_comm y).
        simpl in p; by apply p, tr, sgt_in, ipn_in.
      + rewrite rng_mult_assoc.
        rewrite (rng_mult_comm y x).
        rewrite <- rng_mult_assoc.
        rewrite (rng_mult_comm y).
        simpl in p; by apply p, tr, sgt_in, ipn_in.
  Defined.
  
  (** The ideal quotient is a right adjoint to the product in the monoidal lattice of ideals. *)
  Lemma ideal_quotient_subset_prod (I J K : Ideal R)
    : I ⋅ J ⊆ K <-> I ⊆ (K :: J).
  Proof.
    split.
    - intros p r i; apply tr; intros s j; rewrite (rng_mult_comm s r); split;
        by apply p, tr, sgt_in; rapply ipn_in.
    - intros p x.
      apply Trunc_rec.
      intros q.
      induction q as [r x | | ].
      { destruct x.
        specialize (p x s); simpl in p.
        revert p; apply Trunc_rec; intros p.
        by apply p. }
      1: apply ideal_in_zero.
      by apply ideal_in_plus_negate.
  Defined.

  (** Ideal quotients partially cancel *)
  Lemma ideal_quotient_product_left (I J : Ideal R)
    : (I :: J) ⋅ J ⊆ I.
  Proof.
    by apply ideal_quotient_subset_prod.
  Defined.

End IdealCRing.

(** ** Category of commutative rings. *)

Global Instance isgraph_CRing : IsGraph CRing := isgraph_induced ring_cring.
Global Instance is01cat_CRing : Is01Cat CRing := is01cat_induced ring_cring.
Global Instance is2graph_CRing : Is2Graph CRing := is2graph_induced ring_cring.
Global Instance is1cat_CRing : Is1Cat CRing := is1cat_induced ring_cring.
