Require Import WildCat.
(* Some of the material in abstract_algebra and canonical names could be selectively exported to the user, as is done in Groups/Group.v. *)
Require Import Classes.interfaces.abstract_algebra.
Require Import Algebra.AbGroups.
Require Export Algebra.Rings.Ring Algebra.Rings.Ideal Algebra.Rings.QuotientRing.

(** * Commutative Rings *)

Local Open Scope predicate_scope.
Local Open Scope ring_scope.
Local Open Scope wc_iso_scope.

(** A commutative ring consists of the following data: *)
Record CRing := {
  (** An underlying ring. *)
  cring_ring :> Ring;
  (** Such that they satisfy the axioms of a commutative ring. *)
  cring_commutative :: Commutative (A:=cring_ring) (.*.);
}.

Definition issig_CRing : _ <~> CRing := ltac:(issig).

Instance cring_plus {R : CRing} : Plus R := plus_abgroup R.
Instance cring_zero {R : CRing} : Zero R := zero_abgroup R.
Instance cring_negate {R : CRing} : Negate R := negate_abgroup R.

Definition Build_CRing' (R : AbGroup) `(!One R, !Mult R)
  (comm : Commutative (.*.)) (assoc : Associative (.*.))
  (dist_l : LeftDistribute (.*.) (+)) (unit_l : LeftIdentity (.*.) 1)
  : CRing.
Proof.
  snapply Build_CRing.
  - rapply (Build_Ring R); only 1,2,4: exact _.
    + intros x y z.
      lhs napply comm.
      lhs rapply dist_l.
      f_ap.
    + intros x.
      lhs rapply comm.
      apply unit_l.
  - exact _.
Defined.

(** ** Properties of commutative rings *)

Definition rng_mult_comm {R : CRing} (x y : R) : x * y = y * x := commutativity x y.

(** Powers commute with multiplication *)
Lemma rng_power_mult {R : CRing} (x y : R) (n : nat)
  : rng_power (R:=R) (x * y) n = rng_power (R:=R) x n * rng_power (R:=R) y n.
Proof.
  simple_induction' n.
  1: symmetry; rapply rng_mult_one_l.
  simpl.
  lhs_V napply rng_mult_assoc.
  rhs_V napply rng_mult_assoc.
  napply (ap (x *.)).
  lhs napply (ap (y *.) IH).
  lhs napply rng_mult_assoc.
  rhs napply rng_mult_assoc.
  exact (ap (.* _) (rng_mult_comm _ _)).
Defined.

Definition rng_mult_permute_2_3 {R : CRing} (x y z : R)
  : x * y * z = x * z * y.
Proof.
  lhs_V napply rng_mult_assoc.
  rhs_V napply rng_mult_assoc.
  apply ap, rng_mult_comm.
Defined.

Definition rng_mult_move_left_assoc {R : CRing} (x y z : R)
  : x * y * z = y * x * z.
Proof.
  f_ap; apply rng_mult_comm.
Defined.

Definition rng_mult_move_right_assoc {R : CRing} (x y z : R)
  : x * (y * z) = y * (x * z).
Proof.
  refine (rng_mult_assoc _ _ _ @ _ @ (rng_mult_assoc _ _ _)^).
  apply rng_mult_move_left_assoc.
Defined.

Definition isinvertible_cring (R : CRing) (x : R)
  (inv : R) (inv_l : inv * x = 1)
  : IsInvertible R x.
Proof.
  snapply Build_IsInvertible.
  - exact inv.
  - exact inv_l.
  - lhs napply rng_mult_comm.
    exact inv_l.
Defined.

(** ** Ideals in commutative rings *)
  
Section IdealCRing.
  Context {R : CRing}.
  
  (** The section is meant to complement the [IdealLemmas] section in Algebra.Rings.Ideal. Since the results here only hold in commutative rings, they have to be kept here. *)
  
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
    apply pred_subset_antisymm;
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
    { apply pred_subset_pred_eq.
      symmetry.
      apply ideal_product_unit_r. }
    etransitivity.
    1: exact (ideal_product_subset_pres_r _ _ _ p).
    rapply ideal_product_intersection_sum_subset'.
  Defined.

  (** This can be combined into a sufficient (but not necessary) condition for equality of intersections and products. *)
  Lemma ideal_intersection_is_product (I J : Ideal R)
    : Coprime I J -> I ∩ J ↔ I ⋅ J.
  Proof.
    intros p.
    apply pred_subset_antisymm.
    - apply ideal_intersection_subset_product.
      unfold Coprime in p.
      apply symmetry in p.
      exact p.
    - apply ideal_product_subset_intersection.
  Defined.

  Lemma ideal_quotient_product (I J K : Ideal R)
    : (I :: J) :: K ↔ (I :: (J ⋅ K)).
  Proof.
    apply pred_subset_antisymm.
    - intros x [p q]; strip_truncations; split; apply tr;
      intros r; rapply Trunc_rec; intros jk.
      + induction jk as [y [z z' j k] | | ? ? ? ? ? ? ].
        * rewrite (rng_mult_comm z z').
          simpl.
          rewrite rng_mult_assoc.
          destruct (p z' k) as [p' ?].
          revert p'; apply Trunc_rec; intros p'.
          exact (p' z j).
        * change (I (x * 0)).
          rewrite rng_mult_zero_r.
          apply ideal_in_zero.
        * change (I (x * (g - h))).
          rewrite rng_dist_l.
          rewrite rng_mult_negate_r.
          by apply ideal_in_plus_negate.
      + induction jk as [y [z z' j k] | | ? ? ? ? ? ? ].
        * change (I (z * z' * x)).
          rewrite <- rng_mult_assoc.
          rewrite (rng_mult_comm z).
          destruct (q z' k) as [q' ?].
          revert q'; apply Trunc_rec; intros q'.
          exact (q' z j).
        * change (I (0 * x)).
          rewrite rng_mult_zero_l.
          apply ideal_in_zero.
        * change (I ((g - h) * x)).
          rewrite rng_dist_r.
          rewrite rng_mult_negate_l.
          by apply ideal_in_plus_negate.
    - intros x [p q]; strip_truncations; split; apply tr;
      intros r k; split; apply tr; intros z j.
      + simpl.
        rewrite <- rng_mult_assoc.
        rewrite (rng_mult_comm r z).
        by apply p, tr, sgt_in, ipn_in.
      + cbn in z.
        change (I (z * (x * r))).
        rewrite (rng_mult_comm x).
        rewrite rng_mult_assoc.
        by apply q, tr, sgt_in, ipn_in.
      + cbn in r.
        change (I (r * x * z)).
        rewrite <- rng_mult_assoc.
        rewrite (rng_mult_comm r).
        rewrite <- rng_mult_assoc.
        by apply p, tr, sgt_in, ipn_in.
      + cbn in r, z.
        change (I (z * (r * x))).
        rewrite rng_mult_assoc.
        rewrite rng_mult_comm.
        by apply p, tr, sgt_in, ipn_in.
  Defined.
  
  (** The ideal quotient is a right adjoint to the product in the monoidal lattice of ideals. *)
  Lemma ideal_quotient_subset_prod (I J K : Ideal R)
    : I ⋅ J ⊆ K <-> I ⊆ (K :: J).
  Proof.
    split.
    - intros p r i; split; apply tr; intros s j; cbn in s, r.
      + by apply p, tr, sgt_in, ipn_in.
      + change (K (s * r)).
        rewrite (rng_mult_comm s r).
        by apply p, tr, sgt_in; rapply ipn_in.
    - intros p x.
      apply Trunc_rec.
      intros q.
      induction q as [r x | | ].
      { destruct x.
        specialize (p x s); destruct p as [p q].
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

Instance isgraph_CRing : IsGraph CRing := isgraph_induced cring_ring.
Instance is01cat_CRing : Is01Cat CRing := is01cat_induced cring_ring.
Instance is2graph_CRing : Is2Graph CRing := is2graph_induced cring_ring.
Instance is1cat_CRing : Is1Cat CRing := is1cat_induced cring_ring.
Instance hasequiv_CRing : HasEquivs CRing := hasequivs_induced cring_ring.

(** ** Quotient rings *)

Instance commutative_quotientring_mult (R : CRing) (I : Ideal R)
  : Commutative (A:=QuotientRing R I) (.*.).
Proof.
  intros x; srapply QuotientRing_ind_hprop; intros y; revert x.
  srapply QuotientRing_ind_hprop; intros x; hnf.
  lhs_V napply rng_homo_mult.
  rhs_V napply rng_homo_mult.
  snapply ap.
  apply commutativity.
Defined.

Definition cring_quotient (R : CRing) (I : Ideal R) : CRing
  := Build_CRing (QuotientRing R I) _.

Definition cring_quotient_map {R : CRing} (I : Ideal R)
  : R $-> cring_quotient R I
  := rng_quotient_map I.
