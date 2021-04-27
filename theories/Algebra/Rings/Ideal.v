Require Import Basics Types.
Require Import Spaces.Nat Spaces.Finite.
Require Import Algebra.Rings.CRing.
Require Import Algebra.AbGroups.

Local Open Scope mc_scope.

Declare Scope ideal_scope.
Delimit Scope ideal_scope with ideal.

(** In this file we define Ideals *)

(** An additive subgroup I of a ring R is an ideal when: *)
Class IsIdeal {R : CRing} (I : Subgroup R) :=
  isideal (r x : R) : I x -> I (r * x).

Global Instance ishprop_isideal `{Funext} {R : CRing} (I : Subgroup R)
  : IsHProp (IsIdeal I) := ltac:(unfold IsIdeal; exact _).

(** An ideal of a ring [R] is a subgroup of R which is closed under left multiplication. *)
Record Ideal (R : CRing) := {
  ideal_subgroup : Subgroup R;
  ideal_isideal : IsIdeal ideal_subgroup;
}.

Coercion ideal_subgroup : Ideal >-> Subgroup.
Global Existing Instances ideal_isideal.

Definition issig_Ideal (R : CRing) : _ <~> Ideal R := ltac:(issig).

Global Instance ishset_ideal `{Univalence} {R : CRing} : IsHSet (Ideal R).
Proof.
  nrapply istrunc_equiv_istrunc.
  1: apply issig_Ideal.
  rapply istrunc_sigma.
Defined.

(** Here are some lemmas for proving certain elements are in an ideal. *)
Section IdealElements.

  Context {R : CRing} (I : Ideal R).

  Definition ideal_in_zero : I cring_zero := subgroup_unit I.
  Definition ideal_in_plus a b : I a -> I b -> I (a + b) := subgroup_op I a b.
  Definition ideal_in_negate a : I a -> I (- a) := subgroup_inverse I a.
  Definition ideal_in_plus_negate a b : I a -> I b -> I (a - b)
    := subgroup_op_inverse I a b.

  Lemma ideal_in_negate' a : I (- a) -> I a.
  Proof.
    intros p; rewrite <- (negate_involutive a); revert p.
    apply ideal_in_negate.
  Defined.

  Lemma ideal_in_plus_l a b : I (a + b) -> I b -> I a.
  Proof.
    intros p q; rewrite <- (rng_plus_zero_r a); revert p q.
    rewrite <- (rng_plus_negate_r b).
    rewrite rng_plus_assoc.
    apply ideal_in_plus_negate.
  Defined.

End IdealElements.

(** The zero ideal is an ideal *)
Global Instance isideal_trivial_subgroup (R : CRing)
  : IsIdeal (R:=R) trivial_subgroup.
Proof.
  hnf; cbn. intros r x p.
  refine (_ @ rng_mult_zero_r r).
  f_ap.
Defined.

(** Zero ideal *)
Definition ideal_zero (R : CRing) : Ideal R
  := Build_Ideal R _ (isideal_trivial_subgroup R).

(** The unit ideal is an ideal *)
Global Instance isideal_maximal_subgroup (R : CRing)
  : IsIdeal (R:=R) maximal_subgroup.
Proof.
  split.
Defined.

(** Unit ideal *)
Definition ideal_unit (R : CRing) : Ideal R
  := Build_Ideal R _ (isideal_maximal_subgroup R).

(** Intersections of underlying subgroups of ideals are again ideals *)
Global Instance isideal_subgroup_intersection (R : CRing) (I J : Ideal R)
  : IsIdeal (subgroup_intersection I J).
Proof.
  intros r x [a b]; split; by apply isideal.
Defined.

(** Intersection of ideals *)
Definition ideal_intersection {R : CRing} : Ideal R -> Ideal R -> Ideal R
  := fun I J => Build_Ideal R _ (isideal_subgroup_intersection R I J).

(** The subgroup product of ideals is again an ideal. *)
Global Instance isideal_subgroup_product (R : CRing) (I J : Ideal R)
  : IsIdeal (subgroup_product I J).
Proof.
  intros r.
  refine (subgroup_product_ind I J _  _ _ _ _).
  + intros x p.
    apply tr, sgt_in.
    left; by apply isideal.
  + intros x p.
    apply tr, sgt_in.
    right; by apply isideal.
  + apply tr, sgt_in.
    left; apply isideal.
    apply subgroup_unit.
  + intros x y p q IHp IHq.
    rewrite rng_dist_l.
    rewrite rng_mult_negate_r.
    by rapply subgroup_op_inverse.
Defined.

(** Sum of ideals *)
Definition ideal_sum {R : CRing} : Ideal R -> Ideal R -> Ideal R
  := fun I J => Build_Ideal R _ (isideal_subgroup_product R I J).

Definition ideal_sum_ind {R : CRing} (I J : Ideal R)
  (P : forall x, ideal_sum I J x -> Type)
  (P_I_in : forall x y, P x (tr (sgt_in (inl y))))
  (P_J_in : forall x y, P x (tr (sgt_in (inr y))))
  (P_unit : P mon_unit (tr sgt_unit))
  (P_op : forall x y h k, P x (tr h) -> P y (tr k) -> P (x - y) (tr (sgt_op h k)))
  `{forall x y, IsHProp (P x y)}
  : forall x (p : ideal_sum I J x), P x p
  := subgroup_product_ind I J P P_I_in P_J_in P_unit P_op.

(** *** Product of ideals *)

(** First we form the "naive" product of ideals { a * b | a ∈ I /\ b ∈ J } *)
(** Note that this is not an ideal, but we can fix this later. *)
Inductive ideal_product_naive_type {R : CRing} (I J : Ideal R) : R -> Type :=
| ipn_in : forall x y, I x -> J y -> ideal_product_naive_type I J (x * y)
.

(** Now we can close this under addition to get the product ideal. *)

(** Product of ideals *)
Definition ideal_product {R : CRing} : Ideal R -> Ideal R -> Ideal R.
Proof.
  intros I J.
  snrapply Build_Ideal.
  1: exact (subgroup_generated (G := R) (ideal_product_naive_type I J)).
  intros r s.
  apply Trunc_functor.
  intros p.
  induction p as [s i | | g h p1 IHp1 p2 IHp2].
  + destruct i.
    apply sgt_in.
    rewrite simple_associativity.
    apply ipn_in.
    1: apply isideal.
    1,2: assumption.
  + rewrite rng_mult_zero_r.
    rapply sgt_unit.
  + rewrite rng_dist_l.
    rewrite rng_mult_negate_r.
    by rapply sgt_op.
Defined.

(** The kernel of a ring homomorphism is an ideal. *)
Definition ideal_kernel {R S : CRing} (f : CRingHomomorphism R S) : Ideal R.
Proof.
  snrapply Build_Ideal.
  1: exact (grp_kernel f).
  intros r x p; cbn in p.
  simpl.
  refine (rng_homo_mult _ _ _ @ _).
  refine (_ @ rng_mult_zero_r (f r)).
  f_ap.
Defined.

(** *** Ideal generated by a subset *)

(** It seems tempting to define ideals generated by a subset in terms of subgroups generated by a subset but this does not work. Ideals also have to be closed under left multiplciation by ring elements so they end up having more elements than the subgroup that gets generated. *)

(** Therefore we will do an analagous construction to the one done in Subgroup.v *)

(** Underlying type family of an ideal generated by subset *)
Inductive ideal_generated_type (R : CRing) (X : R -> Type) : R -> Type :=
(** The iddeal should contain all elements of the original family. *)
| igt_in (r : R) : X r -> ideal_generated_type R X r
(** It should contain zero. *)
| igt_zero : ideal_generated_type R X cring_zero
(** It should be closed under negation and addition. *)
| igt_add_neg (r s : R)
  : ideal_generated_type R X r
  -> ideal_generated_type R X s
  -> ideal_generated_type R X (r - s)
(** And finally, it should be closed under left multiplication. *)
| igt_mul (r s : R)
  : ideal_generated_type R X s
  -> ideal_generated_type R X (r * s)
.

Arguments ideal_generated_type {R} X r.
Arguments igt_in {R X r}.
Arguments igt_zero {R X}.
Arguments igt_add_neg {R X r s}.
Arguments igt_mul {R X r s}.

(** Again, as with subgroups we need to truncate this to make it a predicate. *)

(** Ideal generated by a subset *)
Definition ideal_generated {R : CRing} (X : R -> Type) : Ideal R.
Proof.
  snrapply Build_Ideal.
  { snrapply Build_Subgroup'.
    1: exact (fun x => merely (ideal_generated_type X x)).
    1: exact _.
    1: apply tr, igt_zero.
    intros x y p q; strip_truncations.
    by apply tr, igt_add_neg. }
  intros r x; apply Trunc_functor.
  apply igt_mul.
Defined.

(** Finitely generated ideal *)
Definition ideal_generated_finite {R : CRing} {n : nat} (X : Fin n -> R) : Ideal R.
Proof.
  apply ideal_generated.
  intros r.
  exact {x : Fin n & X x = r}.
Defined.

(** Principal ideal *)
Definition ideal_principal {R : CRing} (x : R) : Ideal R
  := ideal_generated (fun r => x = r).

(** *** Ideal equality *)

(** Classically, set based equality suffices for ideals. Since we are talking about predicates, we use pointwise iffs. This can of course be shown to be equivalent to the identity type. *)
Definition ideal_eq {R : CRing} (I J : Ideal R) := forall x, I x <-> J x.

(** With univalence we can characterize paths of ideals *)
Lemma equiv_path_ideal `{Univalence} {R : CRing} {I J : Ideal R} : ideal_eq I J <~> I = J.
Proof.
  refine ((equiv_ap' (issig_Ideal R)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  rapply equiv_path_subgroup'.
Defined.

Global Instance reflexive_ideal_eq {R : CRing} : Reflexive (@ideal_eq R).
Proof.
  intros I x; by split.
Defined.

Global Instance symmetric_ideal_eq {R : CRing} : Symmetric (@ideal_eq R).
Proof.
  intros I J p x; specialize (p x); by symmetry.
Defined.

Global Instance transitive_ideal_eq {R : CRing} : Transitive (@ideal_eq R).
Proof.
  intros I J K p q x; specialize (p x); specialize (q x); by transitivity (J x).
Defined.

(** We define the subset relation on ideals in the usual way: *)
Definition ideal_subset {R : CRing} (I J : Ideal R) := (forall x, I x -> J x).

Global Instance reflexive_ideal_subset {R : CRing} : Reflexive (@ideal_subset R)
  := fun _ _ => idmap.

Global Instance transitive_ideal_subset {R : CRing} : Transitive (@ideal_subset R).
Proof.
  intros x y z p q a.
  specialize (p a); specialize (q a).
  exact (q o p).
Defined.

Coercion ideal_eq_subset {R : CRing} {I J : Ideal R} : ideal_eq I J -> ideal_subset I J.
Proof.
  intros f x; apply f.
Defined.

(** Quotient (a.k.a colon) ideal *)
(** Unfortunately, due to truncatedness constraints, we need to assume funext. *)
Definition ideal_quotient `{Funext} {R : CRing} (I J : Ideal R) : Ideal R.
Proof.
  snrapply Build_Ideal.
  { snrapply Build_Subgroup'.
    1: exact (fun r => forall x, J x -> I (r * x)).
    1: exact _.
    { intros r p.
      rewrite rng_mult_zero_l.
      apply ideal_in_zero. }
    hnf; intros x y p q r s.
    rewrite rng_dist_r.
    rewrite rng_mult_negate_l.
    apply ideal_in_plus_negate.
    1: by apply p.
    by apply q. }
  hnf; cbn.
  intros r x p q s.
  rewrite <- rng_mult_assoc.
  by apply isideal, p.
Defined.

(** The annihilator of an ideal. *)
Definition ideal_annihilator `{Funext} {R : CRing} (I : Ideal R) : Ideal R
  := ideal_quotient (ideal_zero R) I.

(** *** Ideal notations *)

(** We declare a module for various (unicode) ideal notations. These exist in their own special case, and can be imported and used when needing to reason about ideals. *)

(** TODO: reserve these properly *)
Module Notation.
  Infix "⊆" := ideal_subset : ideal_scope.
  Infix "↔" := ideal_eq : ideal_scope.
  Infix "+" := ideal_sum : ideal_scope.
  Infix "⋅" := ideal_product (at level 20) : ideal_scope.
  Infix "∩" := ideal_intersection (at level 20)  : ideal_scope.
  Infix "::" := ideal_quotient : ideal_scope.
  Notation "〈 X 〉" := (ideal_generated X)  : ideal_scope.
  Notation Ann := ideal_annihilator.
End Notation.

(** ** Properties of ideals *)

(** *** Coprime ideals *)

(** Two ideals are coprime if their sum is the unit ideal. *)
Definition Coprime {R : CRing} (I J : Ideal R) : Type
  := ideal_eq (ideal_sum I J) (ideal_unit R).
Existing Class Coprime.

(* Lemma coprime_property {R : CRing} {I J : Ideal R} (p : Coprime I J)
  : merely {x : R & I x /\ {y : R & J y /\ x + y = 1}}.
Proof.
  pose (q := p); clearbody q.
  specialize (p cring_one).
  destruct p as [_ p].
  specialize (p tt).
  revert p; apply Trunc_functor; intros p.
  destruct p as [x [s | t] | | ].
  - 
  
  
  
  rapply (subgroup_generated_type_rec _ _ (fun _ _ => _) _ _ _ _ p).
  { intros x t.
    destruct t as [s | t].
    + apply tr.
      exists x.
      exists (1 - x).
      rewrite rng_plus_comm, <- rng_plus_assoc, rng_plus_negate_l.
      apply rng_plus_zero_r.
    + apply tr.
      exists x.
      exists (1 - x).
      rewrite rng_plus_comm, <- rng_plus_assoc, rng_plus_negate_l.
      apply rng_plus_zero_r. }
  { apply tr.
      
      reflexivity.
      rewrite 
      rewrite (rng_plus_assoc x (-x) 1). *)

(** *** Ideal lemmas *)

(** We use these notations in the rest of this file *)
Import Notation.
Local Open Scope ideal_scope.

Section IdealLemmas.

  Context {R : CRing}.

  (** Subset relation is antisymmetric *)
  Lemma ideal_subset_antisymm (I J : Ideal R) : I ⊆ J -> J ⊆ I -> I ↔ J.
  Proof.
    intros p q x; split; by revert x.
  Defined.

  (** The zero ideal is contained by all ideals *)
  Lemma ideal_zero_subset I : ideal_zero R ⊆ I.
  Proof.
    intros x p; rewrite p; apply ideal_in_zero.
  Defined.

  (** The unit ideal contains all ideals *)
  Lemma ideal_unit_subset I : I ⊆ ideal_unit R.
  Proof.
    hnf; cbn; trivial.
  Defined.

  (** Intersection includes into the left *)
  Lemma ideal_intersection_subset_l (I J : Ideal R) : I ∩ J ⊆ I.
  Proof.
    intro; exact fst.
  Defined.

  (** Intersection includes into the right *)
  Lemma ideal_intersection_subset_r (I J : Ideal R) : I ∩ J ⊆ J.
  Proof.
    intro; exact snd.
  Defined.

  (** Subsets of intersections *)
  Lemma ideal_intersection_subset (I J K : Ideal R)
    : K ⊆ I -> K ⊆ J -> K ⊆ I ∩ J.
  Proof.
    intros p q x r; specialize (p x r); specialize (q x r); by split.
  Defined.

  (** Ideals include into their sum on the left *)
  Lemma ideal_sum_subset_l (I J : Ideal R) : I ⊆ (I + J).
  Proof.
    intros x p.
    apply tr, sgt_in.
    left; exact p.
  Defined.

  (** Ideals include into their sum on the right *)
  Lemma ideal_sum_subset_r (I J : Ideal R) : J ⊆ (I + J).
  Proof.
    intros x p.
    apply tr, sgt_in.
    right; exact p.
  Defined.

  (** Products of ideals are included in their left factor *)
  Lemma ideal_product_subset_l (I J : Ideal R) : I ⋅ J ⊆ I.
  Proof.
    intros r p.
    strip_truncations.
    induction p as [r i | | r s p1 IHp1 p2 IHp2 ].
    + destruct i as [s t].
      rewrite commutativity.
      by apply isideal.
    + rapply ideal_in_zero.
    + by rapply ideal_in_plus_negate.
  Defined.

  (** Products of ideals are included in their right factor. *)
  Lemma ideal_product_subset_r (I J : Ideal R) : I ⋅ J ⊆ J.
  Proof.
    intros r p.
    strip_truncations.
    induction p as [r i | | r s p1 IHp1 p2 IHp2 ].
    + destruct i as [s t].
      by apply isideal.
    + rapply ideal_in_zero.
    + by rapply ideal_in_plus_negate.
  Defined.

  (** Products of ideals preserve subsets on the left *)
  Lemma ideal_product_subset_pres_l (I J K : Ideal R) : I ⊆ J -> I ⋅ K ⊆ J ⋅ K.
  Proof.
    intros p r q.
    strip_truncations.
    induction q as [r i | | r s ].
    + destruct i.
      apply tr, sgt_in, ipn_in.
      1: apply p.
      1,2: assumption.
    + apply ideal_in_zero.
    + by apply ideal_in_plus_negate.
  Defined.

  (** Products of ideals preserve subsets on the right *)
  Lemma ideal_product_subset_pres_r (I J K : Ideal R) : I ⊆ J -> K ⋅ I ⊆ K ⋅ J.
  Proof.
    intros p r q.
    strip_truncations.
    induction q as [r i | | r s ].
    + destruct i.
      apply tr, sgt_in, ipn_in.
      2: apply p.
      1,2: assumption.
    + apply ideal_in_zero.
    + by apply ideal_in_plus_negate.
  Defined.

  (** Products of ideals are subsets of their intersection. *)
  Lemma ideal_product_subset_intersection (I J : Ideal R) : I ⋅ J ⊆ I ∩ J.
  Proof.
    apply ideal_intersection_subset.
    + apply ideal_product_subset_l.
    + apply ideal_product_subset_r.
  Defined.

  (** Sums of ideals are the smallest ideal containing the summand. *)
  Lemma ideal_sum_smallest (I J K : Ideal R) : I ⊆ K -> J ⊆ K -> (I + J) ⊆ K.
  Proof.
    intros p q.
    refine (ideal_sum_ind I J (fun x _ => K x) p q _ _).
    1: apply subgroup_unit.
    intros y z s t.
    rapply subgroup_op_inverse.
  Defined.

  (** Ideals absorb themselves under sum. *)
  Lemma ideal_sum_self (I : Ideal R) : I + I ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: by rapply ideal_sum_smallest.
    rapply ideal_sum_subset_l.
  Defined.

  (** Sums preserve inclusions in left summand. *)
  Lemma ideal_sum_subset_pres_l (I J K : Ideal R) : I ⊆ J -> (I + K) ⊆ (J + K).
  Proof.
    intros p.
    apply ideal_sum_smallest.
    { transitivity J.
      1: exact p.
      apply ideal_sum_subset_l. }
    apply ideal_sum_subset_r.
  Defined.

  (** Sums preserve inclusions in right summand. *)
  Lemma ideal_sum_subset_pres_r (I J K : Ideal R) : I ⊆ J -> (K + I) ⊆ (K + J).
  Proof.
    intros p.
    apply ideal_sum_smallest.
    1: apply ideal_sum_subset_l.
    transitivity J.
    1: exact p.
    apply ideal_sum_subset_r.
  Defined.

  (** Products left distribute over sums *)
  Lemma ideal_dist_l (I J K : Ideal R) : I ⋅ (J + K) ↔ I ⋅ J + I ⋅ K.
  Proof.
    (** We split into two directions. *)
    apply ideal_subset_antisymm.
    (** We deal with the difficult inclusion first. The proof comes down to breaking down the definition and reassembling into the right. *)
    { intros r p.
      strip_truncations.
      induction p as [ r i | | r s p1 IHp1 p2 IHp2].
      - destruct i as [r s p q].
        strip_truncations.
        induction q as [ t k | | t k p1 IHp1 p2 IHp2 ].
        + apply tr, sgt_in.
          destruct k as [j | k].
          * left; by apply tr, sgt_in, ipn_in.
          * right; by apply tr, sgt_in, ipn_in.
        + apply tr, sgt_in; left.
          rewrite rng_mult_zero_r.
          apply ideal_in_zero.
        + rewrite rng_dist_l.
          rewrite rng_mult_negate_r.
          by apply ideal_in_plus_negate.
      - apply ideal_in_zero.
      - by apply ideal_in_plus_negate. }
    (** This is the easy direction which can use previous lemmas. *)
    apply ideal_sum_smallest.
    1,2: apply ideal_product_subset_pres_r.
    1: apply ideal_sum_subset_l.
    apply ideal_sum_subset_r.
  Defined.

  (** Products distribute over sums on the right. *)
  (** The proof is very similar to the left version *)
  Lemma ideal_dist_r (I J K : Ideal R) : (I + J) ⋅ K ↔ I ⋅ K + J ⋅ K.
  Proof.
    apply ideal_subset_antisymm.
    { intros r p.
      strip_truncations.
      induction p as [ r i | | r s p1 IHp1 p2 IHp2].
      - destruct i as [r s p q].
        strip_truncations.
        induction p as [ t k | | t k p1 IHp1 p2 IHp2 ].
        + apply tr, sgt_in.
          destruct k as [j | k].
          * left; by apply tr, sgt_in, ipn_in.
          * right; by apply tr, sgt_in, ipn_in.
        + apply tr, sgt_in; left.
          rewrite rng_mult_zero_l.
          apply ideal_in_zero.
        + rewrite rng_dist_r.
          rewrite rng_mult_negate_l.
          by apply ideal_in_plus_negate.
      - apply ideal_in_zero.
      - by apply ideal_in_plus_negate. }
    apply ideal_sum_smallest.
    1,2: apply ideal_product_subset_pres_l.
    1: apply ideal_sum_subset_l.
    apply ideal_sum_subset_r.
  Defined.

(*   Lemma ideal_dist_inter (I J K : Ideal R) : J ⊆ I -> I ∩ (J + K) ↔ J + (I ∩ K).
  Proof. 
    intros ji.
    apply ideal_subset_antisymm.
    { intros x [i jk].
      strip_truncations.
      apply tr, sgt_in.
      induction jk as [r [] | | k].
      1: by left.
      1: right; by split.
      1: left; apply ideal_in_zero.
      admit. }
    apply ideal_sum_smallest.
    - apply ideal_intersection_subset.
      1: exact p.
      apply ideal_sum_subset_l.
    - apply ideal_intersection_subset.
      1: apply ideal_intersection_subset_l.
      etransitivity.
      2: apply ideal_sum_subset_r.
      apply ideal_intersection_subset_r.
  Admitted. *)
  
  (** Ideal sums are commutative *)
  Lemma ideal_sum_comm (I J : Ideal R) : I + J ↔ J + I.
  Proof.
    apply ideal_subset_antisymm; apply ideal_sum_smallest.
    1,3: apply ideal_sum_subset_r.
    1,2: apply ideal_sum_subset_l.
  Defined.

  (** Zero ideal is left additive identity. *) 
  Lemma ideal_sum_zero_l I : ideal_zero R + I ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: apply ideal_sum_smallest.
    1: apply ideal_zero_subset.
    1: reflexivity.
    apply ideal_sum_subset_r.
  Defined.

  (** Zero ideal is right additive identity. *)
  Lemma ideal_sum_zero_r I : I + ideal_zero R ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: apply ideal_sum_smallest.
    1: reflexivity.
    1: apply ideal_zero_subset.
    apply ideal_sum_subset_l.
  Defined.

  (** Ideal products are commutative. *)
  (** This only holds because we are in a commutative ring. *)
  Lemma ideal_product_comm (I J : Ideal R) : I ⋅ J ↔ J ⋅ I.
  Proof.
    (** WLOG we show one direction *)
    assert (p : forall K L : Ideal R, K ⋅ L ⊆ L ⋅ K).
    { clear I J; intros I J.
      intros r p.
      strip_truncations.
      induction p as [r p | |].
      2: apply ideal_in_zero.
      2: by apply ideal_in_plus_negate.
      destruct p as [s t p q].
      rewrite rng_mult_comm.
      by apply tr, sgt_in, ipn_in. }
    apply ideal_subset_antisymm; apply p.
  Defined.

  (** Unit ideal is left multiplicative identity *)
  Lemma ideal_product_unit_l I : ideal_unit R ⋅ I ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: apply ideal_product_subset_r.
    intros r p.
    rewrite <- rng_mult_one_l.
    by apply tr, sgt_in, ipn_in.
  Defined.

  (** Unit ideal is right multiplicative ideal. *)
  Lemma ideal_product_unit_r I : I ⋅ ideal_unit R ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: apply ideal_product_subset_l.
    intros r p.
    rewrite <- rng_mult_one_r.
    by apply tr, sgt_in, ipn_in.
  Defined.

  (** Intersecting with unit ideal on the left does nothing. *)
  Lemma ideal_intresection_unit_l I : ideal_unit R ∩ I ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: apply ideal_intersection_subset_r.
    apply ideal_intersection_subset.
    1: apply ideal_unit_subset.
    reflexivity.
  Defined.

  (** Intersecting with unit ideal on right does nothing. *)
  Lemma ideal_intersection_unit_r I : I ∩ ideal_unit R ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: apply ideal_intersection_subset_l.
    apply ideal_intersection_subset.
    1: reflexivity.
    apply ideal_unit_subset.
  Defined.

  (** Product of intersection and sum is subset of sum of products *)
  (** This is stated a bit more generally, like we would for a general ring .*)
  Lemma ideal_product_intersection_sum_subset (I J : Ideal R)
    : (I ∩ J) ⋅ (I + J) ⊆ (I ⋅ J + J ⋅ I).
  Proof.
    etransitivity.
    1: rapply ideal_dist_l.
    etransitivity.
    1: rapply ideal_sum_subset_pres_r.
    1: rapply ideal_product_subset_pres_l.
    1: apply ideal_intersection_subset_l.
    etransitivity.
    1: rapply ideal_sum_subset_pres_l.
    1: rapply ideal_product_subset_pres_l.
    1: apply ideal_intersection_subset_r.
    rapply ideal_sum_comm.
  Defined.

  (** Product of intersection and sum is a subset of product *)
  (** Note that this is a generalization of lcm * gcd = product *)
  (** In a commutative ring we can simplify the right hand side of the previous lemma. *)
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

  (** If the sum of ideals is the whole ring then their product is a subset of their intersection. *)
  Lemma ideal_intersection_subset_product (I J : Ideal R)
    : ideal_unit R ⊆ (I + J) -> I ∩ J ⊆ I ⋅ J.
  Proof.
    intros p.
    etransitivity.
    { apply ideal_eq_subset.
      symmetry.
      apply ideal_product_unit_r. }
    etransitivity.
    { rapply ideal_product_subset_pres_r.
      exact p. }
    rapply ideal_product_intersection_sum_subset'.
  Defined.

  (** This can be combined into a sufficient (but not necessery) condition for equality of intersections and products. *)
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

  Section AssumeFunext.
    Context `{Funext}.

    (** Ideals are subsets of their ideal quotients *)
    Lemma ideal_quotient_subset (I J : Ideal R) : I ⊆ (I :: J).
    Proof.
      intros x i r j.
      rewrite rng_mult_comm.
      by apply isideal.
    Defined.

    (** Products are subsets iff the first factor is a subset of the ideal quotient *)
    Lemma ideal_quotient_subset_prod (I J K : Ideal R)
      : I ⋅ J ⊆ K <-> I ⊆ (K :: J).
    Proof.
      split.
      { intros p r i s j.
        by apply p, tr, sgt_in, ipn_in. }
      intros p x q.
      strip_truncations.
      induction q as [r x | | ].
      { destruct x.
        cbv in p.
        by apply p. }
      1: apply ideal_in_zero.
      by apply ideal_in_plus_negate.
    Defined.

    (** Ideal quotients partially cancel *)
    Lemma ideal_quotient_susbset_left_inverse (I J : Ideal R)
      : (I :: J) ⋅ J ⊆ I.
    Proof.
      by apply ideal_quotient_subset_prod.
    Defined.

    (** If J divides I then the ideal quotient of J by I is trivial. *)
    Lemma ideal_quotient_trivial (I J : Ideal R)
      : I ⊆ J -> J :: I ↔ ideal_unit R.
    Proof.
      intros p.
      apply ideal_subset_antisymm.
      1: cbv; trivial.
      intros r _ x q.
      by apply isideal, p.
    Defined.

    (** The ideal quotient of I by unit is I *)
    Lemma ideal_quotient_unit_bottom (I : Ideal R)
      : (I :: ideal_unit R) ↔ I.
    Proof.
      apply ideal_subset_antisymm.
      { intros r p.
        rewrite <- rng_mult_one_r.
        exact (p cring_one tt). }
      apply ideal_quotient_subset.
    Defined.

    (** The ideal quotient of unit by I is unit *)
    Lemma ideal_quotient_unit_top (I : Ideal R)
      : (ideal_unit R :: I) ↔ ideal_unit R.
    Proof.
      cbv; split; trivial.
    Defined.

    (** The ideal quotient by a sum is an intersecton of ideal quotients *)
    Lemma ideal_quotient_sum (I J K : Ideal R)
      : (I :: (J + K)) ↔ (I :: J) ∩ (I :: K).
    Proof.
      apply ideal_subset_antisymm.
      { intros r p; split.
        + intros x j.
          hnf in p; apply p.
          by apply ideal_sum_subset_l.
        + intros x k.
          hnf in p; apply p.
          by apply ideal_sum_subset_r. }
      intros r [p q] x jk.
      hnf in p, q.
      strip_truncations.
      induction jk as [s x | | ].
      - destruct x.
        1: by apply p.
        by apply q.
      - rewrite rng_mult_zero_r.
        apply ideal_in_zero.
      - rewrite rng_dist_l.
        rewrite rng_mult_negate_r.
        by apply ideal_in_plus_negate.
    Defined.

    Lemma ideal_quotient_product (I J K : Ideal R)
      : (I :: J) :: K ↔ (I :: (J ⋅ K)).
    Proof.
      apply ideal_subset_antisymm.
      { hnf. intros x p y q. cbv in p.
        strip_truncations.
        induction q as [y i | | ].
        - destruct i as [ y z s t ].
          rewrite (rng_mult_comm y).
          rewrite rng_mult_assoc.
          by apply p.
        - rewrite rng_mult_zero_r.
          apply ideal_in_zero.
        - rewrite rng_dist_l.
          rewrite rng_mult_negate_r.
          by apply ideal_in_plus_negate. }
      intros x p y k z j; hnf in p.
      rewrite <- rng_mult_assoc.
      rewrite (rng_mult_comm y).
      by apply p, tr, sgt_in, ipn_in.
    Defined.

    (** Ideal quotients distribute over intersections *)
    Lemma ideal_quotient_intersection (I J K : Ideal R)
      : (I ∩ J :: K) ↔ (I :: K) ∩ (J :: K).
    Proof.
      apply ideal_subset_antisymm.
      1: intros r p; hnf in p; split; hnf; intros; by apply p.
      intros r [p q]; hnf in p, q; intros x k; by split; [apply p | apply q].
    Defined.

    (** Annihilators reverse the order of inclusion. *)
    Lemma ideal_annihilator_subset (I J : Ideal R) : I ⊆ J -> Ann J ⊆ Ann I.
    Proof.
      intros p x q y i.
      hnf in q.
      by apply q, p.
    Defined.

  End AssumeFunext.

End IdealLemmas.


(** TODO: Maximal ideals *)
(** TODO: Principal ideal *)
(** TODO: Prime ideals *)
(** TODO: Radical ideals *)
(** TODO: Minimal ideals *)
(** TODO: Primary ideals *)

