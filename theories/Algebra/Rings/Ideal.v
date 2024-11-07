Require Import Basics Types.
Require Import Spaces.Finite.Fin.
Require Import Classes.interfaces.canonical_names.
Require Import Algebra.Rings.Ring.
Require Import Algebra.Groups.Subgroup.
Require Import Algebra.AbGroups.
Require Import WildCat.Core.

Local Open Scope mc_scope.

Declare Scope ideal_scope.
Delimit Scope ideal_scope with ideal.
Local Open Scope ideal_scope.

(** * Left, Right and Two-sided Ideals *)

(** ** Definition of Ideals *)

(** An additive subgroup [I] of a ring [R] is a left ideal when it is closed under multiplciation on the left. *)
Class IsLeftIdeal {R : Ring} (I : Subgroup R) :=
  isleftideal (r x : R) : I x -> I (r * x).

(** An additive subgroup [I] of a ring [R] is a right ideal when it is closed under multiplication on the right. We define this using the opposite ring allowing us to reduce redundancy between left and right ideals. *)
Class IsRightIdeal {R : Ring} (I : Subgroup R) :=
  isrightideal_isleftideal_op :: IsLeftIdeal (R := rng_op R) I.

Definition isrightideal {R : Ring} (I : Subgroup R) (x r : R)
  : IsRightIdeal I -> I x -> I (x * r)
  := fun _ => isleftideal (R := rng_op R) r x.

(** An additive subgroup [I] of a ring [R] is a two-sided ideal when it is both a left and right ideal. In this case we just call it an ideal. *)
Class IsIdeal {R : Ring} (I : Subgroup R) := {
  ideal_isleftideal :: IsLeftIdeal I;
  ideal_isrightideal :: IsRightIdeal I;
}.
Definition issig_IsIdeal {R : Ring} (I : Subgroup R) : _ <~> IsIdeal I := ltac:(issig).
Hint Immediate Build_IsIdeal : typeclass_instances.

(** Any two-sided ideal is also a two-sided ideal of the opposite ring. *)
Global Instance isideal_op {R : Ring} (I : Subgroup R)
  : IsIdeal I -> IsIdeal (R := rng_op R) I.
Proof.
  intros [? ?]; exact _.
Defined.

(** A left ideal of a ring [R] is a subgroup [I] of [R] which is closed under left multiplication. *)
Record LeftIdeal (R : Ring) := {
  leftideal_subgroup :> Subgroup R;
  leftideal_isleftideal :: IsLeftIdeal leftideal_subgroup;
}.
Definition issig_LeftIdeal (R : Ring) : _ <~> LeftIdeal R := ltac:(issig).

(** A right ideal of a ring [R] is a subgroup [I] of [R] which is closed under right multiplication. *)
Definition RightIdeal (R : Ring) := LeftIdeal (rng_op R).

Global Instance isrightdeal_rightideal {R} (I : RightIdeal R)
  : IsRightIdeal (R:=R) I
  := leftideal_isleftideal _ I.

Definition Build_RightIdeal (R : Ring) (I : Subgroup R) (H : IsRightIdeal I)
  : RightIdeal R
  := Build_LeftIdeal (rng_op R) I H.

Definition issig_RightIdeal (R : Ring)
  : {I : Subgroup R& IsRightIdeal (R:=R) I} <~> RightIdeal R
  := ltac:(issig).

(** A two-sided ideal of a ring [R], or just an ideal, is a subgroup [I] of [R] which is closed under both left and right multiplication. *)
Record Ideal (R : Ring) := {
  ideal_subgroup :> Subgroup R;
  ideal_isideal :: IsIdeal ideal_subgroup;
}.
Definition issig_Ideal (R : Ring) : _ <~> Ideal R := ltac:(issig).

Definition ideal_op (R : Ring) : Ideal R -> Ideal (rng_op R)
  := fun I => Build_Ideal (rng_op R) I _.
Coercion ideal_op : Ideal >-> Ideal.

(** *** Truncatedness properties *)

Section IdealTrunc.
  (** Assuming [Funext] we can show that the ideal predicates are propositions. *) 
  Context `{Funext}.

  (** Being a left ideal is a proposition. *)
  Global Instance ishprop_isleftideal {R : Ring} (I : Subgroup R)
    : IsHProp (IsLeftIdeal I) := ltac:(unfold IsLeftIdeal; exact _).

  (** Being a right ideal is a proposition. *)
  Global Instance ishprop_isrightideal `{Funext} {R : Ring} (I : Subgroup R)
    : IsHProp (IsRightIdeal I) :=  ishprop_isleftideal _.

  (** Being a two-sided ideal is a proposition. *)
  Global Instance ishprop_isideal {R : Ring} (I : Subgroup R)
    : IsHProp (IsIdeal I)
    := istrunc_equiv_istrunc _ (issig_IsIdeal I).

  (** Assuming [Univalence] we can show that the ideal types are sets. Note that univalence is only used to prove that the type of [Subgroup]s is a set. *)
  Context `{Univalence}.

  (** The type of left ideals is a set. *)
  Global Instance ishset_leftideal {R : Ring} : IsHSet (LeftIdeal R)
    := istrunc_equiv_istrunc _ (issig_LeftIdeal R).
  
  (** The type of right ideals is a set. *)
  Global Instance ishset_rightideal {R : Ring} : IsHSet (RightIdeal R)
    := _.

  (** The type of ideals is a set. *)
  Global Instance ishset_ideal {R : Ring} : IsHSet (Ideal R)
    := istrunc_equiv_istrunc _ (issig_Ideal R).

End IdealTrunc.

(** *** Conversion between Ideals *)

(** Every ideal is a left ideal. *)
Definition leftideal_of_ideal {R : Ring} : Ideal R -> LeftIdeal R
  := fun I => Build_LeftIdeal R I _.
Coercion leftideal_of_ideal : Ideal >-> LeftIdeal.

(** Every ideal is a right ideal. *)
Definition rightideal_of_ideal {R : Ring} : Ideal R -> RightIdeal R
  := fun I => Build_RightIdeal R I _.
Coercion rightideal_of_ideal : Ideal >-> RightIdeal.

(** *** Easy properties of ideals *)

(** Here are some lemmas for proving certain elements are in an ideal. They are just special cases of the underlying subgroup lemmas. We write them out for clarity. Note that [I] isn't actually assumed to be an ideal but only a subgroup. *)
Section IdealElements.
  Context {R : Ring} (I : Subgroup R) (a b : R).
  Definition ideal_in_zero : I ring_zero := subgroup_in_unit I.
  Definition ideal_in_plus : I a -> I b -> I (a + b) := subgroup_in_op I a b.
  Definition ideal_in_negate  : I a -> I (- a) := subgroup_in_inv  I a.
  Definition ideal_in_negate' : I (- a) -> I a := subgroup_in_inv' I a.
  Definition ideal_in_plus_negate : I a -> I b -> I (a - b) := subgroup_in_op_inv I a b.
  Definition ideal_in_negate_plus : I a -> I b -> I (-a + b) := subgroup_in_inv_op I a b.
  Definition ideal_in_plus_l : I (a + b) -> I b -> I a := subgroup_in_op_l I a b.
  Definition ideal_in_plus_r : I (a + b) -> I a -> I b := subgroup_in_op_r I a b.
End IdealElements.

(** ** Constructions of ideals *)

(** *** Zero Ideal *)

(** The trivial subgroup is a left ideal. *)
Global Instance isleftideal_trivial_subgroup (R : Ring)
  : IsLeftIdeal (R := R) trivial_subgroup.
Proof.
  intros r x p.
  rhs_V nrapply (rng_mult_zero_r).
  f_ap.
Defined.

(** The trivial subgroup is a right ideal. *)
Global Instance isrightideal_trivial_subgroup (R : Ring)
  : IsRightIdeal (R := R) trivial_subgroup
  := isleftideal_trivial_subgroup _.

(** The trivial subgroup is an ideal. *)
Global Instance isideal_trivial_subgroup (R : Ring)
  : IsIdeal (R := R) trivial_subgroup
  := {}.

(** We call the trivial subgroup the "zero ideal". *)
Definition ideal_zero (R : Ring) : Ideal R := Build_Ideal R _ _. 

(** *** The unit ideal *)

(** The maximal subgroup is a left ideal. *)
Global Instance isleftideal_maximal_subgroup (R : Ring)
  : IsLeftIdeal (R := R) maximal_subgroup
  := ltac:(done).

(** The maximal subgroup is a right ideal. *)
Global Instance isrightideal_maximal_subgroup (R : Ring)
  : IsRightIdeal (R := R) maximal_subgroup
  := isleftideal_maximal_subgroup _.

(** The maximal subgroup is an ideal.  *)
Global Instance isideal_maximal_subgroup (R : Ring)
  : IsIdeal (R:=R) maximal_subgroup
  := {}.

(** We call the maximal subgroup the "unit ideal". *)
Definition ideal_unit (R : Ring) : Ideal R
  := Build_Ideal R _ (isideal_maximal_subgroup R).

(** *** Intersection of ideals *)

(** Intersections of underlying subgroups of left ideals are again left ideals. *)
Global Instance isleftideal_subgroup_intersection (R : Ring) (I J : Subgroup R)
  `{IsLeftIdeal R I, IsLeftIdeal R J}
  : IsLeftIdeal (subgroup_intersection I J).
Proof.
  intros r x [a b]; split; by apply isleftideal.
Defined.

(** Intersections of underlying subgroups of right ideals are again right ideals. *)
Global Instance isrightideal_subgroup_intersection (R : Ring) (I J : Subgroup R)
  `{IsRightIdeal R I, IsRightIdeal R J}
  : IsRightIdeal (subgroup_intersection I J)
  := isleftideal_subgroup_intersection _ _ _.

(** Intersections of underlying subgroups of ideals are again ideals. *)
Global Instance isideal_subgroup_intersection (R : Ring) (I J : Subgroup R)
  `{IsIdeal R I, IsIdeal R J}
  : IsIdeal (subgroup_intersection I J)
  := {}.

(** Intersection of left ideals. *)
Definition leftideal_intersection {R : Ring}
  : LeftIdeal R -> LeftIdeal R -> LeftIdeal R
  := fun I J => Build_LeftIdeal R (subgroup_intersection I J) _.

(** Intersection of right ideals. *)
Definition rightideal_intersection {R : Ring}
  : RightIdeal R -> RightIdeal R -> RightIdeal R
  := leftideal_intersection.

(** Intersection of ideals. *)
Definition ideal_intersection {R : Ring}
  : Ideal R -> Ideal R -> Ideal R
  := fun I J => Build_Ideal R (subgroup_intersection I J) _.

(** *** Sum of ideals *)

(** The subgroup product of left ideals is again an ideal. *)
Global Instance isleftideal_subgroup_product (R : Ring) (I J : Subgroup R)
  `{IsLeftIdeal R I, IsLeftIdeal R J}
  : IsLeftIdeal (subgroup_product I J).
Proof.
  intros r.
  nrapply subgroup_product_ind.
  - intros x p.
    apply tr, sgt_in.
    left; by apply isleftideal.
  - intros x p.
    apply tr, sgt_in.
    right; by apply isleftideal.
  - apply tr, sgt_in.
    left; apply isleftideal.
    apply ideal_in_zero.
  - intros x y p q IHp IHq; cbn beta.
    rewrite rng_dist_l.
    rewrite rng_mult_negate_r.
    by apply subgroup_in_op_inv.
  - exact _.
Defined.

(** The subgroup product of right ideals is again an ideal. *)
Global Instance isrightideal_subgroup_product (R : Ring) (I J : Subgroup R)
  `{IsRightIdeal R I, IsRightIdeal R J}
  : IsRightIdeal (subgroup_product I J)
  := isleftideal_subgroup_product _ _ _.

(** The subgroup product of ideals is again an ideal. *)
Global Instance isideal_subgroup_product (R : Ring) (I J : Subgroup R)
  `{IsIdeal R I, IsIdeal R J}
  : IsIdeal (subgroup_product I J)
  := {}.

(** Sum of left ideals. *)
Definition leftideal_sum {R : Ring}
  : LeftIdeal R -> LeftIdeal R -> LeftIdeal R
  := fun I J => Build_LeftIdeal R (subgroup_product I J) _.

(** Sum of right ideals. *)
Definition rightideal_sum {R : Ring}
  : RightIdeal R -> RightIdeal R -> RightIdeal R
  := leftideal_sum.

(** Sum of ideals. *)
Definition ideal_sum {R : Ring}
  : Ideal R -> Ideal R -> Ideal R
  := fun I J => Build_Ideal R (subgroup_product I J) _.

Definition ideal_sum_ind {R : Ring} (I J : Ideal R)
  (P : forall x, ideal_sum I J x -> Type)
  (P_I_in : forall x y, P x (tr (sgt_in (inl y))))
  (P_J_in : forall x y, P x (tr (sgt_in (inr y))))
  (P_unit : P mon_unit (tr sgt_unit))
  (P_op : forall x y h k, P x (tr h) -> P y (tr k) -> P (x - y) (tr (sgt_op h k)))
  `{forall x y, IsHProp (P x y)}
  : forall x (p : ideal_sum I J x), P x p
  := subgroup_product_ind I J P P_I_in P_J_in P_unit P_op.

(** *** Product of ideals *)

(** First we form the "naive" product of ideals { a * b | a ∈ I /\ b ∈ J }. Note that this is not an ideal, but we can fix this. *)
Inductive ideal_product_naive_type {R : Ring} (I J : Subgroup R) : R -> Type :=
| ipn_in : forall x y, I x -> J y -> ideal_product_naive_type I J (x * y).

(** We instead consider the subgroup generated by this naive product and later prove it happens to be an ideal. Note that the subgroup generated by a set and the ideal generated by a set are not the same in general. *)
Definition ideal_product_type {R : Ring} (I J : Subgroup R) : Subgroup R
  := subgroup_generated (G := R) (ideal_product_naive_type I J). 

(** The product of left ideals is a left ideal. *)
Global Instance isleftideal_ideal_product_type {R : Ring} (I J : Subgroup R)
  `{IsLeftIdeal R I, IsLeftIdeal R J}
  : IsLeftIdeal (ideal_product_type I J).
Proof.
  intro r.
  nrapply (functor_subgroup_generated _ _ (grp_homo_rng_left_mult r)).
  intros s [s1 s2 p1 p2]; cbn.
  rewrite simple_associativity.
  nrefine (ipn_in I J (r * s1) s2 _ p2).
  by apply isleftideal.
Defined.

(** The product of right ideals is a right ideal. *)
Global Instance isrightideal_ideal_product_type {R : Ring} (I J : Subgroup R)
  `{IsRightIdeal R I, IsRightIdeal R J}
  : IsRightIdeal (ideal_product_type I J).
Proof.
  intro r.
  nrapply (functor_subgroup_generated _ _ (grp_homo_rng_right_mult (R:=R) r)).
  intros s [s1 s2 p1 p2]; cbn.
  rewrite <- simple_associativity.
  nrefine (ipn_in I J s1 (s2 * r) p1 _).
  by apply isrightideal.
Defined.

(** The product of ideals is an ideal. *)
Global Instance isideal_ideal_product_type {R : Ring} (I J : Subgroup R)
  `{IsIdeal R I, IsIdeal R J}
  : IsIdeal (ideal_product_type I J)
  := {}. 

(** Product of left ideals. *)
Definition leftideal_product {R : Ring}
  : LeftIdeal R -> LeftIdeal R -> LeftIdeal R
  := fun I J => Build_LeftIdeal R (ideal_product_type I J) _.

(** Product of right ideals. *)
Definition rightideal_product {R : Ring}
  : RightIdeal R -> RightIdeal R -> RightIdeal R
  := leftideal_product.

(** Product of ideals. *)
Definition ideal_product {R : Ring}
  : Ideal R -> Ideal R -> Ideal R
  := fun I J => Build_Ideal R (ideal_product_type I J) _.

(** *** The kernel of a ring homomorphism *)

(** The kernel of the underlying group homomorphism of a ring homomorphism is a left ideal. *)
Global Instance isleftideal_grp_kernel {R S : Ring} (f : RingHomomorphism R S)
  : IsLeftIdeal (grp_kernel f).
Proof.
  intros r x p.
  lhs nrapply rng_homo_mult.
  rhs_V nrapply (rng_mult_zero_r (f r)).
  by apply ap.
Defined.

(** The kernel of the underlying group homomorphism of a ring homomorphism is a right ideal. *)
Global Instance isrightideal_grp_kernel {R S : Ring} (f : RingHomomorphism R S)
  : IsRightIdeal (grp_kernel f)
  := isleftideal_grp_kernel (fmap rng_op f).

(** The kernel of the underlying group homomorphism of a ring homomorphism is an ideal. *)
Global Instance isideal_grp_kernel {R S : Ring} (f : RingHomomorphism R S)
  : IsIdeal (grp_kernel f)
  := {}.

(** The kernel of a ring homomorphism is an ideal. *)
Definition ideal_kernel {R S : Ring} (f : RingHomomorphism R S) : Ideal R
  := Build_Ideal R (grp_kernel f) _.

(** *** Ideal generated by a subset *)

(** It seems tempting to define ideals generated by a subset in terms of subgroups generated by a subset but this does not work. Left ideals also have to be closed under left multiplciation by ring elements, and similarly for right and two sided ideals. Therefore we will do an analagous construction to the one done in Subgroup.v. *)

(** Underlying type family of a left ideal generated by subset. *)
Inductive leftideal_generated_type (R : Ring) (X : R -> Type) : R -> Type :=
(** It should contain all elements of the original family. *)
| ligt_in (r : R) : X r -> leftideal_generated_type R X r
(** It should contain zero. *)
| ligt_zero : leftideal_generated_type R X ring_zero
(** It should be closed under negation and addition. *)
| ligt_add_neg (r s : R)
  : leftideal_generated_type R X r
  -> leftideal_generated_type R X s
  -> leftideal_generated_type R X (r - s)
(** And finally, it should be closed under left multiplication. *)
| ligt_mul (r s : R)
  : leftideal_generated_type R X s
  -> leftideal_generated_type R X (r * s)
.

Arguments leftideal_generated_type {R} X r.
Arguments ligt_in {R X r}.
Arguments ligt_zero {R X}.
Arguments ligt_add_neg {R X r s}.
Arguments ligt_mul {R X r s}.

(** Left ideal generated by a subset. *)
Definition leftideal_generated@{u v} {R : Ring@{u}} (X : R -> Type@{v}) : LeftIdeal@{u v} R.
Proof.
  snrapply Build_LeftIdeal.
  - snrapply Build_Subgroup'.
    + exact (fun x => merely (leftideal_generated_type X x)).
    + exact _.
    + apply tr, ligt_zero.
    + intros x y p q; strip_truncations.
      by apply tr, ligt_add_neg.
  - intros r x; apply Trunc_functor.
    apply ligt_mul.
Defined.

(** Right ideal generated by a subset. *)
Definition rightideal_generated@{u v} {R : Ring@{u}} (X : R -> Type@{v}) : RightIdeal@{u v} R
  := Build_RightIdeal R (leftideal_generated (R:=rng_op R) X) _.

(** Underlying type family of a two-sided ideal generated by subset. *)
Inductive ideal_generated_type (R : Ring) (X : R -> Type) : R -> Type :=
(** It should contain all elements of the original family. *)
| igt_in (r : R) : X r -> ideal_generated_type R X r
(** It should contain zero. *)
| igt_zero : ideal_generated_type R X ring_zero
(** It should be closed under negation and addition. *)
| igt_add_neg (r s : R)
  : ideal_generated_type R X r
  -> ideal_generated_type R X s
  -> ideal_generated_type R X (r - s)
(** And finally, it should be closed under left and right multiplication. *)
| igt_mul_l (r s : R)
  : ideal_generated_type R X s
  -> ideal_generated_type R X (r * s)
| igt_mul_r (r s : R)
  : ideal_generated_type R X r
  -> ideal_generated_type R X (r * s)
.

Arguments ideal_generated_type {R} X r.
Arguments igt_in {R X r}.
Arguments igt_zero {R X}.
Arguments igt_add_neg {R X r s}.
Arguments igt_mul_l {R X r s}.
Arguments igt_mul_r {R X r s}.

(** Two-sided ideal generated by a subset. *)
Definition ideal_generated {R : Ring} (X : R -> Type) : Ideal R.
Proof.
  snrapply Build_Ideal; [|split].
  - snrapply Build_Subgroup'.
    + exact (fun x => merely (ideal_generated_type X x)).
    + exact _.
    + apply tr, igt_zero.
    + intros x y p q; strip_truncations.
      by apply tr, igt_add_neg.
  - intros r x; apply Trunc_functor.
    nrapply igt_mul_l.
  - intros x r; apply Trunc_functor.
    nrapply igt_mul_r.
Defined. 

(** *** Finitely generated ideal *)

(** Finitely generated ideals *)
Definition ideal_generated_finite {R : Ring} {n : nat} (X : Fin n -> R) : Ideal R.
Proof.
  apply ideal_generated.
  exact (hfiber X).
Defined.

(** *** Principal ideals *)

(** A principal ideal is an ideal generated by a single element. *)
Definition ideal_principal {R : Ring} (x : R) : Ideal R
  := ideal_generated (fun r => x = r).

(** *** Ideal equality *)

(** Classically, set based equality suffices for ideals. Since we are talking about predicates, we use pointwise iffs. This can of course be shown to be equivalent to the identity type. *)
Definition ideal_eq {R : Ring} (I J : Subgroup R) := forall x, I x <-> J x.

(** With univalence we can characterize equality of ideals. *)
Lemma equiv_path_ideal `{Univalence} {R : Ring} {I J : Ideal R} : ideal_eq I J <~> I = J.
Proof.
  refine ((equiv_ap' (issig_Ideal R)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  rapply equiv_path_subgroup'.
Defined.

(** Under funext, ideal equiality is a proposition. *)
Global Instance ishprop_ideal_eq `{Funext} {R : Ring} (I J : Ideal R)
  : IsHProp (ideal_eq I J) := _.

(** Ideal equality is reflexive. *)
Global Instance reflexive_ideal_eq {R : Ring} : Reflexive (@ideal_eq R).
Proof.
  intros I x; by split.
Defined.

(** Ideal equality is symmetric. *)
Global Instance symmetric_ideal_eq {R : Ring} : Symmetric (@ideal_eq R).
Proof.
  intros I J p x; specialize (p x); by symmetry.
Defined.

(** Ideal equality is transitive. *)
Global Instance transitive_ideal_eq {R : Ring} : Transitive (@ideal_eq R).
Proof.
  intros I J K p q x; specialize (p x); specialize (q x); by transitivity (J x).
Defined.

(** *** Subset relation on ideals *)

(** We define the subset relation on ideals in the usual way: *)
Definition ideal_subset {R : Ring} (I J : Subgroup R) := (forall x, I x -> J x).

(** The subset relation is reflexive. *)
Global Instance reflexive_ideal_subset {R : Ring} : Reflexive (@ideal_subset R)
  := fun _ _ => idmap.

(** The subset relation is transitive. *)
Global Instance transitive_ideal_subset {R : Ring} : Transitive (@ideal_subset R).
Proof.
  intros x y z p q a.
  exact (q a o p a).
Defined.

(** We can coerce equality to the subset relation, since equality is defined to be the subset relation in each direction. *)
Coercion ideal_eq_subset {R : Ring} {I J : Subgroup R} : ideal_eq I J -> ideal_subset I J.
Proof.
  intros f x; apply f.
Defined.

(** *** Quotient (a.k.a colon) ideals *)

(** The definitions here are not entirely standard, but will become so when considering only commutative rings. For the non-commutative case there isn't a lot written about ideal quotients. *)

(** The subgroup corresponding to the left ideal quotient. *)
Definition subgroup_leftideal_quotient {R : Ring} (I J : Subgroup R)
  : Subgroup R.
Proof.
  snrapply Build_Subgroup'.
  - exact (fun r => merely (forall x, J x -> I (r * x))).
  - exact _.
  - apply tr.
    intros r p.
    rewrite rng_mult_zero_l.
    apply ideal_in_zero.
  - intros x y p q.
    strip_truncations; apply tr.
    hnf; intros s j.
    rewrite rng_dist_r.
    rewrite rng_mult_negate_l.
    apply ideal_in_plus_negate.
    + by apply p.
    + by apply q.
Defined.

(** The left ideal quotient of a left ideal is a left ideal. *)
Global Instance isleftideal_subgroup_leftideal_quotient {R : Ring}
  (I J : Subgroup R) `{IsLeftIdeal R I}
  : IsLeftIdeal (subgroup_leftideal_quotient I J).
Proof.
  intros r x p.
  strip_truncations; apply tr.
  intros s j.
  rewrite <- rng_mult_assoc.
  apply isleftideal.
  by nrapply p.
Defined.

(** The left ideal quotient of a right ideal by a left ideal is a right ideal. *)
Global Instance isrightideal_subgroup_leftideal_quotient {R : Ring}
  (I J : Subgroup R) `{IsRightIdeal R I, IsLeftIdeal R J}
  : IsRightIdeal (subgroup_leftideal_quotient (R:=R) I J).
Proof.
  intros r x p.
  strip_truncations; apply tr.
  intros s j.
  cbn in *.
  rewrite <- rng_mult_assoc.
  apply p.
  by rapply isleftideal.
Defined.

(** We define the left ideal quotient as a left ideal. *)
Definition leftideal_quotient {R : Ring}
  : LeftIdeal R -> Subgroup R -> LeftIdeal R
  := fun I J => Build_LeftIdeal R (subgroup_leftideal_quotient I J) _.
  
Definition subgroup_rightideal_quotient {R : Ring} (I J : Subgroup R) : Subgroup R
  := subgroup_leftideal_quotient (R:=rng_op R) I J. 

Global Instance isrightideal_subgroup_rightideal_quotient {R : Ring}
  (I J : Subgroup R) `{IsRightIdeal R I}
  : IsRightIdeal (subgroup_rightideal_quotient I J)
  := isleftideal_subgroup_leftideal_quotient (R:=rng_op R) I J.

Global Instance isleftideal_subgroup_rightideal_quotient {R : Ring}
  (I J : Subgroup R) `{H : IsLeftIdeal R I, IsRightIdeal R J}
  : IsLeftIdeal (subgroup_rightideal_quotient I J).
Proof.
  snrapply (isrightideal_subgroup_leftideal_quotient (R:=rng_op R) I J).
  - exact H.
  - exact _.
Defined.

(** We define the right ideal quotient as a right ideal. *)
Definition rightideal_quotient {R : Ring}
  : RightIdeal R -> Subgroup R -> RightIdeal R
  := fun I J => Build_RightIdeal R (subgroup_rightideal_quotient (R:=R) I J) _.

(** The ideal quotient is then the intersection of a left and right quotient of both two sided ideals. *)
Definition ideal_quotient {R : Ring}
  : Ideal R -> Ideal R -> Ideal R
  := fun I J =>
    Build_Ideal R
      (subgroup_intersection
        (leftideal_quotient I J)
        (rightideal_quotient I J))
      (Build_IsIdeal _ _ _ _).

(** *** Annihilator *)

(** The left annihilator of a subset is the set of elements that annihilate the subgroup with left multiplication. *)
Definition subgroup_ideal_left_annihilator {R : Ring} (S : R -> Type)
  : Subgroup R.
Proof.
  snrapply Build_Subgroup'.
  (** If we assume [Funext], then it isn't necessary to use [merely] here. *)
  - exact (fun r => merely (forall x, S x -> r * x = ring_zero)).
  - exact _.
  - apply tr. 
    intros r p.
    apply rng_mult_zero_l.
  - intros x y p q.
    strip_truncations; apply tr.
    intros r s.
    lhs rapply rng_dist_r.
    rewrite (p r s).
    rewrite rng_mult_negate_l.
    rewrite (q r s).
    rewrite <- rng_mult_negate.
    rewrite rng_mult_zero_r.
    apply left_identity.
Defined.

(** The left annihilator of a subgroup of a ring is a left ideal of the ring. *)
Global Instance isleftideal_ideal_left_annihilator {R : Ring} (I : R -> Type)
  : IsLeftIdeal (subgroup_ideal_left_annihilator I).
Proof.
  intros r x p.
  strip_truncations; apply tr.
  intros s i.
  rewrite <- rng_mult_assoc, (p s i).
  apply rng_mult_zero_r.
Defined.

(** The left annihilator of a left ideal also happens to be a right ideal. In fact, left ideal could be weakened to subset closed under multplication, however we don't need this generality currently. *)
Global Instance isrightideal_ideal_left_annihilator {R : Ring} (I : Subgroup R)
  `{IsLeftIdeal R I}
  : IsRightIdeal (subgroup_ideal_left_annihilator I).
Proof.
  intros r x p.
  strip_truncations; apply tr.
  intros s i; cbn.
  rewrite <- rng_mult_assoc.
  by apply p, isleftideal.
Defined.

(** Therefore the annihilator of a left ideal is an ideal. *)
Global Instance isideal_ideal_left_annihilator {R : Ring} (I : Subgroup R)
  `{IsLeftIdeal R I}
  : IsIdeal (subgroup_ideal_left_annihilator I)
  := {}.

(** The left annihilator of a left ideal. *)
Definition ideal_left_annihilator {R : Ring} (I : LeftIdeal R) : Ideal R
  := Build_Ideal R (subgroup_ideal_left_annihilator I) _.

(** The right annihilator of a subset of a ring is the set of elements that annihilate the elements of the subset with right multiplication. *)
Definition subgroup_ideal_right_annihilator {R : Ring} (I : R -> Type)
  : Subgroup R
  := subgroup_ideal_left_annihilator (R:=rng_op R) I.

(** When the subset is a right ideal the right annihilator is a left ideal of the ring. This can be strengthened. See the comment in the left ideal version of this lemma above. *)
Global Instance isleftideal_ideal_right_annihilator {R : Ring} (I : Subgroup R)
  `{IsRightIdeal R I}
  : IsLeftIdeal (subgroup_ideal_right_annihilator I)
  := isrightideal_ideal_left_annihilator (R:=rng_op R) I.

(** The right annihilator is a right ideal of the ring. *)
Global Instance isrightideal_ideal_right_annihilator {R : Ring} (I : R -> Type)
  : IsRightIdeal (subgroup_ideal_right_annihilator (R:=R) I)
  := isleftideal_ideal_left_annihilator (R:=rng_op R) I.

(** Therefore the annihilator of a right ideal is an ideal. *)
Global Instance isideal_ideal_right_annihilator {R : Ring} (I : Subgroup R)
  `{IsRightIdeal R I}
  : IsIdeal (subgroup_ideal_right_annihilator (R:=R) I)
  := {}.

(** The right annihilator of a right ideal. *)
Definition ideal_right_annihilator {R : Ring} (I : RightIdeal R) : Ideal R
  := Build_Ideal R (subgroup_ideal_right_annihilator (R:=R) I)
     (isideal_ideal_right_annihilator (R:=R) I).

(** The annihilator of an ideal is the intersection of the left and right annihilators. *)
Definition ideal_annihilator {R : Ring} (I : Ideal R) : Ideal R
  := ideal_intersection (ideal_left_annihilator I) (ideal_right_annihilator I).

(** ** Properties of ideals *)

(** *** Coprime ideals *)

(** Two ideals are coprime if their sum is the unit ideal. *)
Definition Coprime {R : Ring} (I J : Ideal R) : Type
  := ideal_eq (ideal_sum I J) (ideal_unit R).
Existing Class Coprime.

Global Instance ishprop_coprime `{Funext} {R : Ring}
  (I J : Ideal R) : IsHProp (Coprime I J).
Proof.
    unfold Coprime.
    exact _.
Defined.

Lemma equiv_coprime_sum `{Funext} {R : Ring} (I J : Ideal R)
  : Coprime I J
  <~> hexists (fun '(((i ; p) , (j ; q)) : sig I * sig J)
      => i + j = ring_one).
Proof.
  simpl.
  srapply equiv_iff_hprop.
  - intros c.
    pose (snd (c ring_one) tt) as d; clearbody d; clear c.
    strip_truncations.
    apply tr.
    induction d.
    + destruct x.
      * exists ((g ; s), (ring_zero; ideal_in_zero _)).
        apply rng_plus_zero_r.
      * exists ((ring_zero; ideal_in_zero _), (g ; s)).
        apply rng_plus_zero_l.
    + exists ((ring_zero; ideal_in_zero _), (ring_zero; ideal_in_zero _)).
      apply rng_plus_zero_l.
    + destruct IHd1 as [[[x xi] [y yj]] p].
      destruct IHd2 as [[[w wi] [z zj]] q].
      srefine (((_;_),(_;_));_).
      * exact (x - w).
      * by apply ideal_in_plus_negate.
      * exact (y - z).
      * by apply ideal_in_plus_negate.
      * cbn.
        refine (_ @ ap011 (fun x y => x - y) p q).
        rewrite <- 2 rng_plus_assoc.
        f_ap.
        rewrite negate_sg_op.
        rewrite rng_plus_comm.
        rewrite rng_plus_assoc.
        reflexivity.
  - intro x.
    strip_truncations.
    intros r.
    split;[intro; exact tt|].
    intros _.
    destruct x as [[[x xi] [y yj]] p].
    rewrite <- rng_mult_one_r.
    change (x + y = 1) in p.
    rewrite <- p.
    rewrite rng_dist_l.
    apply tr.
    rapply sgt_op'.
    + apply sgt_in.
      left.
      by apply isleftideal.
    + apply sgt_in.
      right.
      by apply isleftideal.
Defined.

(** *** Ideal notations *)

(** We declare and import a module for various (unicode) ideal notations. These exist in their own special case, and can be imported and used in other files when needing to reason about ideals. *)

Module Import Notation.
  Infix "⊆" := ideal_subset       : ideal_scope.
  Infix "↔" := ideal_eq           : ideal_scope.
  Infix "+" := ideal_sum          : ideal_scope.
  Infix "⋅" := ideal_product      : ideal_scope.
  Infix "∩" := ideal_intersection : ideal_scope.
  Infix "::" := ideal_quotient    : ideal_scope.
  Notation "〈 X 〉" := (ideal_generated X)  : ideal_scope.
  Notation Ann := ideal_annihilator.
End Notation.

(** *** Ideal lemmas *)

Section IdealLemmas.

  Context {R : Ring}.

  (** Subset relation is antisymmetric. *)
  Lemma ideal_subset_antisymm (I J : Subgroup R) : I ⊆ J -> J ⊆ I -> I ↔ J.
  Proof.
    intros p q x; split; by revert x.
  Defined.

  (** The zero ideal is contained in all ideals. *)
  Lemma ideal_zero_subset (I : Subgroup R) : ideal_zero R ⊆ I.
  Proof.
    intros x p; rewrite p; apply ideal_in_zero.
  Defined.

  (** The unit ideal contains all ideals. *)
  Lemma ideal_unit_subset (I : Subgroup R) : I ⊆ ideal_unit R.
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

  #[local] Hint Extern 4 => progress (cbv beta iota) : typeclass_instances.

  (** Products of ideals are included in their left factor *)
  Lemma ideal_product_subset_l (I J : Ideal R) : I ⋅ J ⊆ I.
  Proof.
    intros r p.
    strip_truncations.
    induction p as [r i | | r s p1 IHp1 p2 IHp2 ].
    + destruct i as [s t].
      by rapply isrightideal.
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
      by apply isleftideal.
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

  (** TODO: *)
  (** The product of ideals is an associative operation. *)
  (* Lemma ideal_product_assoc (I J K : Ideal R) : I ⋅ (J ⋅ K) ↔ (I ⋅ J) ⋅ K.
  Proof.
    intros r; split; apply Trunc_functor.
  Abort. *)

  (** Products of ideals are subsets of their intersection. *)
  Lemma ideal_product_subset_intersection (I J : Ideal R) : I ⋅ J ⊆ I ∩ J.
  Proof.
    apply ideal_intersection_subset.
    + apply ideal_product_subset_l.
    + apply ideal_product_subset_r.
  Defined.

  (** Sums of ideals are the smallest ideal containing the summands. *)
  Lemma ideal_sum_smallest (I J K : Ideal R) : I ⊆ K -> J ⊆ K -> (I + J) ⊆ K.
  Proof.
    intros p q.
    refine (ideal_sum_ind I J (fun x _ => K x) p q _ _).
    1: apply ideal_in_zero.
    intros y z s t.
    rapply ideal_in_plus_negate.
  Defined.

  (** Ideals absorb themselves under sum. *)
  Lemma ideal_sum_self (I : Ideal R) : I + I ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: by rapply ideal_sum_smallest.
    rapply ideal_sum_subset_l.
  Defined.

  (** Sums preserve inclusions in the left summand. *)
  Lemma ideal_sum_subset_pres_l (I J K : Ideal R) : I ⊆ J -> (I + K) ⊆ (J + K).
  Proof.
    intros p.
    apply ideal_sum_smallest.
    { transitivity J.
      1: exact p.
      apply ideal_sum_subset_l. }
    apply ideal_sum_subset_r.
  Defined.

  (** Sums preserve inclusions in the right summand. *)
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
  (** Note that this follows from left adjoints preserving colimits. The product of ideals is a functor whose right adjoint is the quotient ideal. *)
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

  (** Unit ideal is left multiplicative identity. *)
  Lemma ideal_product_unit_l I : ideal_unit R ⋅ I ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    1: apply ideal_product_subset_r.
    intros r p.
    rewrite <- rng_mult_one_l.
    by apply tr, sgt_in, ipn_in.
  Defined.

  (** Unit ideal is right multiplicative identity. *)
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

  (** Ideals are subsets of their ideal quotients *)
  Lemma ideal_quotient_subset (I J : Ideal R) : I ⊆ (I :: J).
  Proof.
    intros x i; split; apply tr; intros r j; cbn.
    - by rapply isrightideal.
    - by rapply isleftideal.
  Defined.

  (** If J divides I then the ideal quotient of J by I is trivial. *)
  Lemma ideal_quotient_trivial (I J : Ideal R)
    : I ⊆ J -> J :: I ↔ ideal_unit R.
  Proof.
    intros p.
    apply ideal_subset_antisymm.
    1: cbv; trivial.
    intros r _; split; apply tr; intros x q; cbn.
    - by apply isleftideal, p. 
    - rapply isrightideal.
      by apply p.
  Defined.

  (** The ideal quotient of I by unit is I. *)
  Lemma ideal_quotient_unit_bottom (I : Ideal R)
    : (I :: ideal_unit R) ↔ I.
  Proof.
    apply ideal_subset_antisymm.
    - intros r [p q].
      strip_truncations.
      rewrite <- rng_mult_one_r.
      exact (p ring_one tt).
    - apply ideal_quotient_subset.
  Defined.

  (** The ideal quotient of unit by I is unit. *)
  Lemma ideal_quotient_unit_top (I : Ideal R)
    : (ideal_unit R :: I) ↔ ideal_unit R.
  Proof.
    split.
    - cbn; trivial.
    - intros ?; split; apply tr;
      cbn; split; trivial. 
  Defined.

  (** The ideal quotient by a sum is an intersection of ideal quotients. *)
  Lemma ideal_quotient_sum (I J K : Ideal R)
    : (I :: (J + K)) ↔ (I :: J) ∩ (I :: K).
  Proof.
    apply ideal_subset_antisymm.
    { intros r [p q]; strip_truncations; split; split; apply tr; intros x jk.
      - by rapply p; rapply ideal_sum_subset_l.
      - by rapply q; rapply ideal_sum_subset_l.
      - by rapply p; rapply ideal_sum_subset_r.
      - by rapply q; rapply ideal_sum_subset_r. }
    intros r [[p q] [u v]]; strip_truncations; split; apply tr;
    intros x jk; strip_truncations.
    - induction jk as [? [] | | ? ? ? ? ? ? ].
      + by apply p.
      + by apply u.
      + apply u, ideal_in_zero.
      + rewrite rng_dist_l.
        rewrite rng_mult_negate_r.
        by apply ideal_in_plus_negate.
    - induction jk as [? [] | | ? ? ? ? ? ? ].
      + by apply q.
      + by apply v.
      + apply v, ideal_in_zero.
      + change (I ((g - h) * r)). 
        rewrite rng_dist_r.
        rewrite rng_mult_negate_l.
        by apply ideal_in_plus_negate.
  Defined.

  (** Ideal quotients distribute over intersections. *)
  Lemma ideal_quotient_intersection (I J K : Ideal R)
    : (I ∩ J :: K) ↔ (I :: K) ∩ (J :: K).
  Proof.
    apply ideal_subset_antisymm.
    - intros r [p q]; strip_truncations; split; split; apply tr; intros x k.
      1,3: by apply p.
      1,2: by apply q.
    - intros r [[p q] [u v]].
      strip_truncations; split; apply tr; intros x k; split.
      + by apply p.
      + by apply u.
      + by apply q.
      + by apply v.
  Defined.

  (** Annihilators reverse the order of inclusion. *)
  Lemma ideal_annihilator_subset (I J : Ideal R) : I ⊆ J -> Ann J ⊆ Ann I.
  Proof.
    intros p x [q q']; hnf in q, q'; strip_truncations;
      split; apply tr; intros y i.
    - by apply q, p.
    - by apply q', p.
  Defined.

  (** The annihilator of an ideal is equal to a quotient of zero. *)
  Lemma ideal_annihilator_zero_quotient (I : Ideal R)
    : Ann I ↔ ideal_zero R :: I.
  Proof.
    intros x; split.
    - intros [p q]; strip_truncations; split; apply tr; intros y i.
      + exact (p y i).
      + exact (q y i).
    - intros [p q]; strip_truncations; split; apply tr; intros y i.
      + exact (p y i).
      + exact (q y i).
  Defined.
  
End IdealLemmas.

(** ** Preimage of ideals under ring homomorphisms *)

(** The preimage of an ideal under a ring homomorphism is also itself an ideal. This is also known as the contraction of an ideal. *)

Global Instance isleftideal_preimage {R S : Ring} (f : R $-> S)
  (I : Subgroup S) `{IsLeftIdeal S I}
  : IsLeftIdeal (subgroup_preimage f I).
Proof.
  intros r x Ifx.
  nrefine (transport I (rng_homo_mult f _ _)^ _).
  rapply isleftideal.
  exact Ifx.
Defined.

Global Instance isrightideal_preimage {R S : Ring} (f : R $-> S)
  (I : Subgroup S) `{IsRightIdeal S I}
  : IsRightIdeal (subgroup_preimage f I)
  := isleftideal_preimage (R:=rng_op R) (S:=rng_op S)
      (fmap rng_op f) I.

Global Instance isideal_preimage {R S : Ring} (f : R $-> S)
  (I : Subgroup S) `{IsIdeal S I}
  : IsIdeal (subgroup_preimage f I)
  := {}.

Definition ideal_preimage {R S : Ring} (f : R $-> S) (I : Ideal S)
  : Ideal R
  := Build_Ideal R (subgroup_preimage f I) _.

(** ** Extensions of ideals *)

(** The extension of an ideal under a ring homomorphism is the ideal generated by the image of the ideal. *)
Definition ideal_extension {R S : Ring} (f : R $-> S) (I : Ideal R) : Ideal S
  := ideal_generated (fun s => exists r, I r /\ f r = s).

(** The extension of a preimage is always a subset of the original ideal. *)
Definition ideal_subset_extension_preimage {R S : Ring} (f : R $-> S)
  (I : Ideal S)
  : ideal_extension f (ideal_preimage f I) ⊆ I.
Proof.
  intros x.
  apply Trunc_rec.
  intros y.
  induction y.
  + destruct x as [s [p q]].
    destruct q; exact p.
  + apply ideal_in_zero.
  + by apply ideal_in_plus_negate.
  + by rapply isleftideal.
  + by rapply isrightideal.
Defined.

(** TODO: Maximal ideals *)
(** TODO: Principal ideal *)
(** TODO: Prime ideals *)
(** TODO: Radical ideals *)
(** TODO: Minimal ideals *)
(** TODO: Primary ideals *)
