Require Import Basics Types.
Require Import Spaces.Finite.Fin.
Require Import Classes.interfaces.canonical_names.
Require Import Algebra.Rings.Ring.
Require Import Algebra.Groups.Subgroup.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import WildCat.Core.

Declare Scope ideal_scope.
Delimit Scope ideal_scope with ideal.
Local Open Scope ideal_scope.
Local Open Scope predicate_scope.

(** * Left, Right and Two-sided Ideals *)

(** ** Definition of Ideals *)

(** An additive subgroup [I] of a ring [R] is a left ideal when it is closed under multiplication on the left. *)
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
Instance isideal_op {R : Ring} (I : Subgroup R)
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

Instance isrightdeal_rightideal {R} (I : RightIdeal R)
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

Definition rightideal_op (R : Ring) : LeftIdeal R -> RightIdeal (rng_op R)
  := idmap.

Definition leftideal_op (R : Ring) : RightIdeal R -> LeftIdeal (rng_op R)
  := idmap.

(** *** Truncatedness properties *)

Section IdealTrunc.
  (** Assuming [Funext] we can show that the ideal predicates are propositions. *) 
  Context `{Funext}.

  (** Being a left ideal is a proposition. *)
  #[export] Instance ishprop_isleftideal {R : Ring} (I : Subgroup R)
    : IsHProp (IsLeftIdeal I) := ltac:(unfold IsLeftIdeal; exact _).

  (** Being a right ideal is a proposition. *)
  #[export] Instance ishprop_isrightideal `{Funext} {R : Ring} (I : Subgroup R)
    : IsHProp (IsRightIdeal I) :=  ishprop_isleftideal _.

  (** Being a two-sided ideal is a proposition. *)
  #[export] Instance ishprop_isideal {R : Ring} (I : Subgroup R)
    : IsHProp (IsIdeal I)
    := istrunc_equiv_istrunc _ (issig_IsIdeal I).

  (** Assuming [Univalence] we can show that the ideal types are sets. Note that univalence is only used to prove that the type of [Subgroup]s is a set. *)
  Context `{Univalence}.

  (** The type of left ideals is a set. *)
  #[export] Instance ishset_leftideal {R : Ring} : IsHSet (LeftIdeal R)
    := istrunc_equiv_istrunc _ (issig_LeftIdeal R).
  
  (** The type of right ideals is a set. *)
  #[export] Instance ishset_rightideal {R : Ring} : IsHSet (RightIdeal R)
    := _.

  (** The type of ideals is a set. *)
  #[export] Instance ishset_ideal {R : Ring} : IsHSet (Ideal R)
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

(** *** Ideal equality *)

(** With univalence we can characterize equality of ideals. *)
Definition equiv_path_ideal `{Univalence} {R : Ring} {I J : Ideal R}
  : (I ↔ J) <~> I = J.
Proof.
  refine ((equiv_ap' (issig_Ideal R)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  rapply equiv_path_subgroup'.
Defined.

(** Under funext, ideal equality is a proposition. *)
Instance ishprop_ideal_eq `{Funext} {R : Ring} (I J : Ideal R)
  : IsHProp (I ↔ J) := _.

(** *** Invariance under subgroup equality *)

(** Being a left ideal is invariant under subgroup equality. *)
Definition isleftideal_eq {R : Ring} (I J : Subgroup R) (p : I ↔ J)
  : IsLeftIdeal I -> IsLeftIdeal J.
Proof.
  intros i r x j.
  apply p in j.
  apply p.
  by apply i.
Defined.

(** Being a right ideal is invariant under subgroup equality. *)
Definition isrightideal_eq {R : Ring} (I J : Subgroup R) (p : I ↔ J)
  : IsRightIdeal I -> IsRightIdeal J
  := isleftideal_eq (R := rng_op R) I J p.

(** ** Constructions of ideals *)

(** *** Zero Ideal *)

(** The trivial subgroup is a left ideal. *)
Instance isleftideal_trivial_subgroup (R : Ring)
  : IsLeftIdeal (trivial_subgroup R).
Proof.
  intros r x p.
  rhs_V napply (rng_mult_zero_r).
  f_ap.
Defined.

(** The trivial subgroup is a right ideal. *)
Instance isrightideal_trivial_subgroup (R : Ring)
  : IsRightIdeal (trivial_subgroup R)
  := isleftideal_trivial_subgroup _.

(** The trivial subgroup is an ideal. *)
Instance isideal_trivial_subgroup (R : Ring)
  : IsIdeal (trivial_subgroup R)
  := {}.

(** We call the trivial subgroup the "zero ideal". *)
Definition ideal_zero (R : Ring) : Ideal R := Build_Ideal R (trivial_subgroup R) _.

(** *** The unit ideal *)

(** The maximal subgroup is a left ideal. *)
Instance isleftideal_maximal_subgroup (R : Ring)
  : IsLeftIdeal (maximal_subgroup R)
  := ltac:(done).

(** The maximal subgroup is a right ideal. *)
Instance isrightideal_maximal_subgroup (R : Ring)
  : IsRightIdeal (maximal_subgroup R)
  := isleftideal_maximal_subgroup _.

(** The maximal subgroup is an ideal.  *)
Instance isideal_maximal_subgroup (R : Ring)
  : IsIdeal (maximal_subgroup R)
  := {}.

(** We call the maximal subgroup the "unit ideal". *)
Definition ideal_unit (R : Ring) : Ideal R
  := Build_Ideal R _ (isideal_maximal_subgroup R).

(** *** Intersection of two ideals *)

(** Intersections of underlying subgroups of left ideals are again left ideals. *)
Instance isleftideal_subgroup_intersection (R : Ring) (I J : Subgroup R)
  `{IsLeftIdeal R I, IsLeftIdeal R J}
  : IsLeftIdeal (subgroup_intersection I J).
Proof.
  intros r x [a b]; split; by apply isleftideal.
Defined.

(** Intersections of underlying subgroups of right ideals are again right ideals. *)
Instance isrightideal_subgroup_intersection (R : Ring) (I J : Subgroup R)
  `{IsRightIdeal R I, IsRightIdeal R J}
  : IsRightIdeal (subgroup_intersection I J)
  := isleftideal_subgroup_intersection _ _ _.

(** Intersections of underlying subgroups of ideals are again ideals. *)
Instance isideal_subgroup_intersection (R : Ring) (I J : Subgroup R)
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

(** *** Intersection of a family of ideals *)

(** Intersections of underlying subgroups of left ideals are again left ideals. *)
Instance isleftideal_subgroup_intersection_family (R : Ring) (I : Type) (J : I -> Subgroup R)
  {h : forall i, IsLeftIdeal (J i)}
  : IsLeftIdeal (subgroup_intersection_family I J).
Proof.
  intros r x; cbn.
  apply Trunc_functor.
  intros Jix i;  by apply isleftideal.
Defined.

(** Intersections of underlying subgroups of right ideals are again right ideals. *)
Instance isrightideal_subgroup_intersection_family (R : Ring) (I : Type) (J : I -> Subgroup R)
  {h : forall i, IsRightIdeal (J i)}
  : IsRightIdeal (subgroup_intersection_family I J)
  := isleftideal_subgroup_intersection_family _ _ _.

(** Intersections of underlying subgroups of ideals are again ideals. *)
Instance isideal_subgroup_intersection_family (R : Ring) (I : Type) (J : I -> Subgroup R)
  {h : forall i, IsIdeal (J i)}
  : IsIdeal (subgroup_intersection_family I J)
  := {}.

(** Intersection of left ideals. *)
Definition leftideal_intersection_family {R : Ring} (I : Type) (J : I -> LeftIdeal R)
  : LeftIdeal R
  := Build_LeftIdeal R (subgroup_intersection_family I J) _.

(** Intersection of right ideals. *)
Definition rightideal_intersection_family {R : Ring} (I : Type) (J : I -> RightIdeal R)
  : RightIdeal R
  := leftideal_intersection_family I J.

(** Intersection of ideals. *)
Definition ideal_intersection_family {R : Ring} (I : Type) (J : I -> Ideal R)
  : Ideal R
  := Build_Ideal R (subgroup_intersection_family I J) _.

(** *** Sum of ideals *)

(** The subgroup product of left ideals is again an ideal. *)
Instance isleftideal_subgroup_product (R : Ring) (I J : Subgroup R)
  `{IsLeftIdeal R I, IsLeftIdeal R J}
  : IsLeftIdeal (subgroup_product I J).
Proof.
  intros r.
  napply (subgroup_product_smallest I J
            (subgroup_preimage (grp_homo_rng_left_mult r) (subgroup_product I J))).
  all: cbn -[subgroup_generated].
  - intros x p.
    by apply subgroup_product_incl_l, isleftideal.
  - intros x p.
    by apply subgroup_product_incl_r, isleftideal.
Defined.

(** The subgroup product of right ideals is again an ideal. *)
Instance isrightideal_subgroup_product (R : Ring) (I J : Subgroup R)
  `{IsRightIdeal R I, IsRightIdeal R J}
  : IsRightIdeal (subgroup_product I J)
  := isleftideal_subgroup_product _ _ _.

(** The subgroup product of ideals is again an ideal. *)
Instance isideal_subgroup_product (R : Ring) (I J : Subgroup R)
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

(** The product ideal swapped is just the product ideal of the opposite ring. *)
Definition ideal_product_type_op {R : Ring} (I J : Subgroup R)
  : ideal_product_type (R:=R) I J ↔ ideal_product_type (R:=rng_op R) J I.
Proof.
  apply (subgroup_eq_functor_subgroup_generated _ _ grp_iso_id).
  apply pred_subset_antisymm; cbn; intros _ []; by napply ipn_in.
Defined.

(** The product of left ideals is a left ideal. *)
Instance isleftideal_ideal_product_type {R : Ring} (I J : Subgroup R)
  `{IsLeftIdeal R I, IsLeftIdeal R J}
  : IsLeftIdeal (ideal_product_type I J).
Proof.
  intro r.
  napply (functor_subgroup_generated _ _ (grp_homo_rng_left_mult r)).
  intros s [s1 s2 p1 p2]; cbn.
  rewrite simple_associativity.
  nrefine (ipn_in I J (r * s1) s2 _ p2).
  by apply isleftideal.
Defined.

(** The product of right ideals is a right ideal. *)
Instance isrightideal_ideal_product_type {R : Ring} (I J : Subgroup R)
  `{IsRightIdeal R I, IsRightIdeal R J}
  : IsRightIdeal (ideal_product_type I J).
Proof.
  napply isrightideal_eq.
  1: symmetry; rapply ideal_product_type_op.
  by apply isleftideal_ideal_product_type.
Defined.

(** The product of ideals is an ideal. *)
Instance isideal_ideal_product_type {R : Ring} (I J : Subgroup R)
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

Definition leftideal_product_op {R : Ring} (I J : RightIdeal R)
  : leftideal_product (leftideal_op R I) (leftideal_op R J)
    = rightideal_product I J
  := idpath.

Definition rightideal_product_op {R : Ring} (I J : LeftIdeal R)
  : rightideal_product (rightideal_op R I) (rightideal_op R J)
    = leftideal_product I J
  := idpath.

(** Product of ideals. *)
Definition ideal_product {R : Ring}
  : Ideal R -> Ideal R -> Ideal R
  := fun I J => Build_Ideal R (ideal_product_type I J) _.

(** *** The kernel of a ring homomorphism *)

(** The kernel of the underlying group homomorphism of a ring homomorphism is a left ideal. *)
Instance isleftideal_grp_kernel {R S : Ring} (f : RingHomomorphism R S)
  : IsLeftIdeal (grp_kernel f).
Proof.
  intros r x p.
  lhs napply rng_homo_mult.
  rhs_V napply (rng_mult_zero_r (f r)).
  by apply ap.
Defined.

(** The kernel of the underlying group homomorphism of a ring homomorphism is a right ideal. *)
Instance isrightideal_grp_kernel {R S : Ring} (f : RingHomomorphism R S)
  : IsRightIdeal (grp_kernel f)
  := isleftideal_grp_kernel (fmap rng_op f).

(** The kernel of the underlying group homomorphism of a ring homomorphism is an ideal. *)
Instance isideal_grp_kernel {R S : Ring} (f : RingHomomorphism R S)
  : IsIdeal (grp_kernel f)
  := {}.

(** The kernel of a ring homomorphism is an ideal. *)
Definition ideal_kernel {R S : Ring} (f : RingHomomorphism R S) : Ideal R
  := Build_Ideal R (grp_kernel f) _.

(** *** Ideal generated by a subset *)

(** It seems tempting to define ideals generated by a subset in terms of subgroups generated by a subset but this does not work. Left ideals also have to be closed under left multiplication by ring elements, and similarly for right and two sided ideals. Therefore we will do an analogous construction to the one done in Subgroup.v. *)

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
  snapply Build_LeftIdeal.
  - snapply Build_Subgroup'.
    + exact (fun x => merely (leftideal_generated_type X x)).
    + exact _.
    + apply tr, ligt_zero.
    + intros x y p q; strip_truncations.
      by apply tr, ligt_add_neg.
  - intros r x; apply Trunc_functor.
    exact ligt_mul.
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
  snapply Build_Ideal; [|split].
  - snapply Build_Subgroup'.
    + exact (fun x => merely (ideal_generated_type X x)).
    + exact _.
    + apply tr, igt_zero.
    + intros x y p q; strip_truncations.
      by apply tr, igt_add_neg.
  - intros r x; apply Trunc_functor.
    exact igt_mul_l.
  - intros x r; apply Trunc_functor.
    exact igt_mul_r.
Defined. 

Definition ideal_generated_rec {R : Ring} {X : R -> Type} {I : Ideal R}
  (p : X ⊆ I)
  : ideal_generated X ⊆ I.
Proof.
  intros x; apply Trunc_rec; intros q.
  induction q.
  - by apply p.
  - apply ideal_in_zero.
  - by apply ideal_in_plus_negate.
  - by apply isleftideal.
  - by rapply isrightideal.
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

(** *** Quotient (a.k.a colon) ideals *)

(** The definitions here are not entirely standard, but will become so when considering only commutative rings. For the non-commutative case there isn't a lot written about ideal quotients. *)

(** The subgroup corresponding to the left ideal quotient [I :: J] consists of the elements [r] in [R] such that [J x -> I (r * x)] for every [x] in [R]. *)
Definition subgroup_leftideal_quotient {R : Ring} (I : Subgroup R) (J : R -> Type)
  : Subgroup R.
Proof.
  snapply Build_Subgroup.
  (* We insert [merely] here to avoid needing [Funext]. *)
  - exact (fun r => merely (J ⊆ subgroup_preimage (grp_homo_rng_left_mult r) I)).
  (* This predicate is a subgroup, since it is equivalent to an intersection of a family of subgroups indexed by [sig J]. *)
  - rapply (issubgroup_equiv
              (H:=subgroup_intersection_family (sig J)
                    (fun x => subgroup_preimage (grp_homo_rng_right_mult x.1) I))).
    intro r; cbn.
    apply Trunc_functor_equiv.
    symmetry; napply equiv_sig_ind.
Defined.

(** The left ideal quotient of a left ideal is a left ideal. *)
Instance isleftideal_subgroup_leftideal_quotient {R : Ring}
  (I : Subgroup R) `{IsLeftIdeal R I} (J : R -> Type)
  : IsLeftIdeal (subgroup_leftideal_quotient I J).
Proof.
  intros r x p.
  strip_truncations; apply tr.
  intros s j; simpl.
  rewrite <- rng_mult_assoc.
  apply isleftideal.
  by napply p.
Defined.

(** The left ideal quotient by a left ideal is a right ideal. *)
Instance isrightideal_subgroup_leftideal_quotient {R : Ring}
  (I J : Subgroup R) `{IsLeftIdeal R J}
  : IsRightIdeal (subgroup_leftideal_quotient I J).
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
  : LeftIdeal R -> (R -> Type) -> LeftIdeal R
  := fun I J => Build_LeftIdeal R (subgroup_leftideal_quotient I J) _.
  
Definition subgroup_rightideal_quotient {R : Ring} (I : Subgroup R) (J : R -> Type)
  : Subgroup R
  := subgroup_leftideal_quotient (R:=rng_op R) I J. 

Instance isrightideal_subgroup_rightideal_quotient {R : Ring}
  (I : Subgroup R) `{IsRightIdeal R I} (J : R -> Type)
  : IsRightIdeal (subgroup_rightideal_quotient I J)
  := isleftideal_subgroup_leftideal_quotient (R:=rng_op R) I J.

Instance isleftideal_subgroup_rightideal_quotient {R : Ring}
  (I J : Subgroup R) `{IsRightIdeal R J}
  : IsLeftIdeal (subgroup_rightideal_quotient I J)
  := isrightideal_subgroup_leftideal_quotient (R:=rng_op R) I J.

(** We define the right ideal quotient as a right ideal. *)
Definition rightideal_quotient {R : Ring}
  : RightIdeal R -> (R -> Type) -> RightIdeal R
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
  snapply Build_Subgroup'.
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
Instance isleftideal_ideal_left_annihilator {R : Ring} (I : R -> Type)
  : IsLeftIdeal (subgroup_ideal_left_annihilator I).
Proof.
  intros r x p.
  strip_truncations; apply tr.
  intros s i.
  rewrite <- rng_mult_assoc, (p s i).
  apply rng_mult_zero_r.
Defined.

(** The left annihilator of a left ideal also happens to be a right ideal. In fact, left ideal could be weakened to subset closed under multiplication, however we don't need this generality currently. *)
Instance isrightideal_ideal_left_annihilator {R : Ring} (I : Subgroup R)
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
Instance isideal_ideal_left_annihilator {R : Ring} (I : Subgroup R)
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
Instance isleftideal_ideal_right_annihilator {R : Ring} (I : Subgroup R)
  `{IsRightIdeal R I}
  : IsLeftIdeal (subgroup_ideal_right_annihilator I)
  := isrightideal_ideal_left_annihilator (R:=rng_op R) I.

(** The right annihilator is a right ideal of the ring. *)
Instance isrightideal_ideal_right_annihilator {R : Ring} (I : R -> Type)
  : IsRightIdeal (subgroup_ideal_right_annihilator (R:=R) I)
  := isleftideal_ideal_left_annihilator (R:=rng_op R) I.

(** Therefore the annihilator of a right ideal is an ideal. *)
Instance isideal_ideal_right_annihilator {R : Ring} (I : Subgroup R)
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
  := ideal_sum I J ↔ ideal_unit R.
Existing Class Coprime.

Instance ishprop_coprime `{Funext} {R : Ring}
  (I J : Ideal R) : IsHProp (Coprime I J).
Proof.
    unfold Coprime.
    exact _.
Defined.

Definition equiv_coprime_sum `{Funext} {R : Ring} (I J : Ideal R)
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
        rhs_V exact (ap011 (fun x y => x - y) p q).
        lhs_V napply rng_plus_assoc.
        rhs_V napply rng_plus_assoc.
        f_ap.
        rewrite rng_negate_plus.
        rhs_V napply rng_plus_comm.
        rhs_V napply rng_plus_assoc.
        f_ap.
        apply commutativity.
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

(** We declare and import a module for various (Unicode) ideal notations. These exist in their own special case, and can be imported and used in other files when needing to reason about ideals. *)

Module Import Notation.
  Infix "+" := ideal_sum          : ideal_scope.
  Infix "⋅" := ideal_product      : ideal_scope.
  Infix "∩" := ideal_intersection : ideal_scope.
  Infix "::" := ideal_quotient    : ideal_scope.
  Notation "〈 X 〉" := (ideal_generated X)  : ideal_scope.
  Notation Ann := ideal_annihilator.
End Notation.

(** *** Ideal Lemmas *)

(** The zero ideal is contained in all ideals. *)
Definition ideal_zero_subset {R : Ring} (I : Subgroup R) : ideal_zero R ⊆ I
  := trivial_subgroup_rec _.

(** The unit ideal contains all ideals. *)
Definition ideal_unit_subset {R : Ring} (I : Subgroup R) : I ⊆ ideal_unit R
  := pred_unit_subset I.

(** Intersection includes into the left *)
Definition ideal_intersection_subset_l {R : Ring} (I J : Ideal R) : I ∩ J ⊆ I
  := pred_and_subset_l I J.

(** Intersection includes into the right *)
Definition ideal_intersection_subset_r {R : Ring} (I J : Ideal R) : I ∩ J ⊆ J
  := pred_and_subset_r I J.

(** Subsets of intersections *)
Definition ideal_intersection_subset {R : Ring} (I J K : Ideal R)
  : K ⊆ I -> K ⊆ J -> K ⊆ I ∩ J
  := pred_and_is_meet I J K.

(** Intersections are commutative *)
Definition ideal_intersection_comm {R : Ring} (I J : Ideal R)
  : I ∩ J ↔ J ∩ I
  := pred_and_comm I J.

(** Ideals include into their sum on the left *)
Definition ideal_sum_subset_l {R : Ring} (I J : Ideal R) : I ⊆ (I + J)
  := subgroup_product_incl_l.

(** Ideals include into their sum on the right *)
Definition ideal_sum_subset_r {R : Ring} (I J : Ideal R) : J ⊆ (I + J)
  := subgroup_product_incl_r.

#[local] Hint Extern 4 => progress (cbv beta iota) : typeclass_instances.

(** Products of ideals are included in their left factor *)
Definition ideal_product_subset_l {R : Ring} (I J : Ideal R) : I ⋅ J ⊆ I.
Proof.
  napply subgroup_generated_rec.
  intros _ [].
  by rapply isrightideal.
Defined.

(** Products of ideals are included in their right factor. *)
Definition ideal_product_subset_r {R : Ring} (I J : Ideal R) : I ⋅ J ⊆ J.
Proof.
  napply subgroup_generated_rec.
  intros _ [].
  by rapply isleftideal.
Defined.

(** Products of ideals preserve subsets on the left *)
Definition ideal_product_subset_pres_l {R : Ring} (I J K : Ideal R)
  : I ⊆ J -> I ⋅ K ⊆ J ⋅ K.
Proof.
  intros p.
  apply (functor_subgroup_generated _ _ grp_iso_id).
  intros _ [].
  apply ipn_in.
  1: apply p.
  1,2: assumption.
Defined.

(** Products of ideals preserve subsets on the right *)
Definition ideal_product_subset_pres_r {R : Ring} (I J K : Ideal R)
  : I ⊆ J -> K ⋅ I ⊆ K ⋅ J.
Proof.
  intros p.
  apply (functor_subgroup_generated _ _ grp_iso_id).
  intros _ [].
  apply ipn_in.
  2: apply p.
  1,2: assumption.
Defined.

(** The product of opposite ideals is the opposite of the reversed product. *)
Definition ideal_product_op {R : Ring} (I J : Ideal R)
  : (ideal_op R I) ⋅ (ideal_op R J)
    ↔ ideal_op R (J ⋅ I).
Proof.
  rapply ideal_product_type_op.
Defined.

Definition ideal_product_op_triple {R : Ring} (I J K : Ideal R)
  : ideal_op R ((K ⋅ J) ⋅ I)
      ⊆ (ideal_op R I) ⋅ ((ideal_op R J) ⋅ (ideal_op R K)).
Proof.
  intros x i.
  apply (ideal_product_op (R:=rng_op R)).
  napply (ideal_product_subset_pres_l (R:=R)).
  1: napply (ideal_product_op (R:=rng_op R)).
  apply i.
Defined.

(** The product of ideals is an associative operation. *)
Definition ideal_product_assoc {R : Ring} (I J K : Ideal R)
  : I ⋅ (J ⋅ K) ↔ (I ⋅ J) ⋅ K.
Proof.
  assert (f : forall (R : Ring) (I J K : Ideal R), I ⋅ (J ⋅ K) ⊆ (I ⋅ J) ⋅ K).
  - clear R I J K; intros R I J K.
    napply subgroup_generated_rec.
    intros _ [r s IHr IHs].
    revert IHs.
    rapply (functor_subgroup_generated _ _ (grp_homo_rng_left_mult r)); clear s.
    intros _ [s t IHs IHt]; cbn.
    rewrite rng_mult_assoc.
    by apply ipn_in; [ apply tr, sgt_in, ipn_in | ].
  - apply pred_subset_antisymm; only 1: apply f.
    intros x i.
    apply (ideal_product_op_triple (R:=rng_op R) I J K).
    napply f.
    apply ideal_product_op_triple.
    exact i.
Defined.

(** Products of ideals are subsets of their intersection. *)
Definition ideal_product_subset_intersection {R : Ring} (I J : Ideal R)
  : I ⋅ J ⊆ I ∩ J.
Proof.
  apply ideal_intersection_subset.
  + apply ideal_product_subset_l.
  + apply ideal_product_subset_r.
Defined.

(** Sums of ideals are the smallest ideal containing the summands. *)
Definition ideal_sum_smallest {R : Ring} (I J K : Ideal R)
  : I ⊆ K -> J ⊆ K -> (I + J) ⊆ K
  := subgroup_product_smallest I J K.

(** Ideals absorb themselves under sum. *)
Definition ideal_sum_self {R : Ring} (I : Ideal R)
  : I + I ↔ I
  := subgroup_product_self I.

(** Sums preserve inclusions in the left summand. *)
Definition ideal_sum_subset_pres_l {R : Ring} (I J K : Ideal R)
  : I ⊆ J -> (I + K) ⊆ (J + K)
  := subgroup_product_subset_pres_l I J K.

(** Sums preserve inclusions in the right summand. *)
Definition ideal_sum_subset_pres_r {R : Ring} (I J K : Ideal R)
  : I ⊆ J -> (K + I) ⊆ (K + J)
  := subgroup_product_subset_pres_r I J K.

(** Sums preserve inclusions in both summands. *)
Definition ideal_sum_subset_pres {R : Ring} (I J K L : Ideal R)
  : I ⊆ J -> K ⊆ L -> (I + K) ⊆ (J + L)
  := subgroup_product_subset_pres I J K L.

(** Sums preserve ideal equality in both summands. *)
Definition ideal_sum_eq {R : Ring} (I J K L : Ideal R)
  : I ↔ J -> K ↔ L -> (I + K) ↔ (J + L)
  := subgroup_product_eq I J K L.

(** The sum of two opposite ideals is the opposite of their sum. *)
Definition ideal_sum_op {R : Ring} (I J : Ideal R)
  : ideal_op R I + ideal_op R J ↔ ideal_op R (I + J)
  := reflexivity _.

(** Products left distribute over sums. Note that this follows from left adjoints preserving colimits. The product of ideals is a functor whose right adjoint is the quotient ideal. *)
Definition ideal_dist_l {R : Ring} (I J K : Ideal R)
  : I ⋅ (J + K) ↔ I ⋅ J + I ⋅ K.
Proof.
  (** We split into two directions. *)
  apply pred_subset_antisymm.
  (** We deal with the difficult inclusion first. The proof comes down to breaking down the definition and reassembling into the right. *)
  { apply subgroup_generated_rec.
    intros _ [r s p q].
    revert s q.
    napply (subgroup_product_smallest J K
              (subgroup_preimage (grp_homo_rng_left_mult r) (I ⋅ J + I ⋅ K))).
    all: cbn -[subgroup_generated ideal_product].
    - intros x j.
      apply subgroup_product_incl_l.
      by apply tr, sgt_in, ipn_in.
    - intros x k.
      apply subgroup_product_incl_r.
      by apply tr, sgt_in, ipn_in. }
  (** This is the easy direction which can use previous lemmas. *)
  apply ideal_sum_smallest.
  1,2: apply ideal_product_subset_pres_r.
  1: apply ideal_sum_subset_l.
  apply ideal_sum_subset_r.
Defined.

(** Products distribute over sums on the right. *)
Definition ideal_dist_r {R : Ring} (I J K : Ideal R)
  : (I + J) ⋅ K ↔ I ⋅ K + J ⋅ K.
Proof.
  change I with (ideal_op _ (ideal_op R I)).
  change J with (ideal_op _ (ideal_op R J)).
  change K with (ideal_op _ (ideal_op R K)).
  etransitivity.
  2: rapply ideal_sum_eq; symmetry; apply (ideal_product_op (R:=rng_op R)).
  etransitivity.
  2: apply (ideal_dist_l (R:=rng_op R)).
  etransitivity.
  2: apply (ideal_product_op (R:=rng_op R)).
  reflexivity.
Defined.

(** Ideal sums are commutative *)
Definition ideal_sum_comm {R : Ring} (I J : Ideal R) : I + J ↔ J + I
  := subgroup_product_comm I J.

(** Zero ideal is left additive identity. *) 
Definition ideal_sum_zero_l {R : Ring} I : ideal_zero R + I ↔ I
  := subgroup_product_trivial_l I.

(** Zero ideal is right additive identity. *)
Definition ideal_sum_zero_r {R : Ring} I : I + ideal_zero R ↔ I
  := subgroup_product_trivial_r I.

(** Unit ideal is left multiplicative identity. *)
Definition ideal_product_unit_l {R : Ring} I : ideal_unit R ⋅ I ↔ I.
Proof.
  apply pred_subset_antisymm.
  1: apply ideal_product_subset_r.
  intros r p.
  rewrite <- rng_mult_one_l.
  by apply tr, sgt_in, ipn_in.
Defined.

(** Unit ideal is right multiplicative identity. *)
Definition ideal_product_unit_r {R : Ring} I : I ⋅ ideal_unit R ↔ I.
Proof.
  apply pred_subset_antisymm.
  1: apply ideal_product_subset_l.
  intros r p.
  rewrite <- rng_mult_one_r.
  by apply tr, sgt_in, ipn_in.
Defined.

(** Intersecting with unit ideal on the left does nothing. *)
Definition ideal_intresection_unit_l {R : Ring} I : ideal_unit R ∩ I ↔ I
  := pred_and_unit_l I.

(** Intersecting with unit ideal on right does nothing. *)
Definition ideal_intersection_unit_r {R : Ring} I : I ∩ ideal_unit R ↔ I
  := pred_and_unit_r I.

(** Product of intersection and sum is subset of sum of products *)
Definition ideal_product_intersection_sum_subset {R : Ring} (I J : Ideal R)
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
Definition ideal_quotient_subset {R : Ring} (I J : Ideal R) : I ⊆ (I :: J).
Proof.
  intros x i; split; apply tr; intros r j; cbn.
  - by rapply isrightideal.
  - by rapply isleftideal.
Defined.

Definition leftideal_quotient_subset_l {R : Ring} (I J K : Ideal R) (p : I ⊆ J)
  : leftideal_quotient I K ⊆ leftideal_quotient J K.
Proof.
  apply (pred_subset_postcomp merely (@Trunc_functor _)).
  intros r q.
  rapply (transitivity q).
  by apply functor_subgroup_preimage.
Defined.

Definition ideal_quotient_subset_l {R : Ring} (I J K : Ideal R) (p : I ⊆ J)
  : (I :: K) ⊆ (J :: K).
Proof.
  napply pred_and_is_meet.
  - rapply (transitivity (pred_and_subset_l _ _)).
    by apply leftideal_quotient_subset_l.
  - rapply (transitivity (pred_and_subset_r _ _)).
    exact (leftideal_quotient_subset_l (R:=rng_op R) I J K p).
Defined.

(** If [J] divides [I] then the ideal quotient of [J] by [I] is trivial. *)
Definition ideal_quotient_trivial {R : Ring} (I J : Ideal R)
  : I ⊆ J -> J :: I ↔ ideal_unit R.
Proof.
  intros p.
  apply pred_subset_antisymm.
  1: cbv; trivial.
  intros r _; split; apply tr; intros x q; cbn.
  - by apply isleftideal, p. 
  - rapply isrightideal.
    by apply p.
Defined.

(** The ideal quotient of [I] by the unit ideal is [I]. *)
Definition ideal_quotient_unit_bottom {R : Ring} (I : Ideal R)
  : (I :: ideal_unit R) ↔ I.
Proof.
  apply pred_subset_antisymm.
  - intros r [p q].
    strip_truncations.
    rewrite <- rng_mult_one_r.
    exact (p ring_one tt).
  - apply ideal_quotient_subset.
Defined.

(** The ideal quotient of the unit ideal by [I] is the unit ideal. *)
Definition ideal_quotient_unit_top {R : Ring} (I : Ideal R)
  : (ideal_unit R :: I) ↔ ideal_unit R.
Proof.
  split.
  - cbn; trivial.
  - intros ?; split; apply tr;
    cbn; split; trivial. 
Defined.

(** The ideal quotient by a sum is an intersection of ideal quotients. *)
Definition ideal_quotient_sum {R : Ring} (I J K : Ideal R)
  : (I :: (J + K)) ↔ (I :: J) ∩ (I :: K).
Proof.
  apply pred_subset_antisymm.
  { intros r [p q]; strip_truncations; split; split; apply tr; intros x jk.
    - by rapply p; rapply ideal_sum_subset_l.
    - by rapply q; rapply ideal_sum_subset_l.
    - by rapply p; rapply ideal_sum_subset_r.
    - by rapply q; rapply ideal_sum_subset_r. }
  intros r [[p q] [u v]]; strip_truncations; split; apply tr.
  - napply subgroup_generated_rec.
    by napply pred_or_is_join.
  - napply subgroup_generated_rec.
    by napply pred_or_is_join.
Defined.

(** Ideal quotients distribute over intersections. *)
Definition ideal_quotient_intersection {R : Ring} (I J K : Ideal R)
  : (I ∩ J :: K) ↔ (I :: K) ∩ (J :: K).
Proof.
  apply pred_subset_antisymm.
  - napply pred_and_is_meet.
    + napply ideal_quotient_subset_l.
      apply pred_and_subset_l.
    + napply ideal_quotient_subset_l.
      apply pred_and_subset_r.
  - intros r [[p q] [u v]].
    strip_truncations; split; apply tr; by napply pred_and_is_meet.
Defined.

(** Annihilators reverse the order of inclusion. *)
Definition ideal_annihilator_subset {R : Ring} (I J : Ideal R)
  : I ⊆ J -> Ann J ⊆ Ann I.
Proof.
  intros p x [q q']; hnf in q, q'; strip_truncations;
    split; apply tr; intros y i.
  - by apply q, p.
  - by apply q', p.
Defined.

(** The annihilator of an ideal is equal to a quotient of zero. *)
Definition ideal_annihilator_zero_quotient {R : Ring} (I : Ideal R)
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

(** ** Preimage of ideals under ring homomorphisms *)

(** The preimage of an ideal under a ring homomorphism is also itself an ideal. This is also known as the contraction of an ideal. *)

Instance isleftideal_preimage {R S : Ring} (f : R $-> S)
  (I : Subgroup S) `{IsLeftIdeal S I}
  : IsLeftIdeal (subgroup_preimage f I).
Proof.
  intros r x Ifx.
  nrefine (transport I (rng_homo_mult f _ _)^ _).
  rapply isleftideal.
  exact Ifx.
Defined.

Instance isrightideal_preimage {R S : Ring} (f : R $-> S)
  (I : Subgroup S) `{IsRightIdeal S I}
  : IsRightIdeal (subgroup_preimage f I)
  := isleftideal_preimage (R:=rng_op R) (S:=rng_op S)
      (fmap rng_op f) I.

Instance isideal_preimage {R S : Ring} (f : R $-> S)
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
  apply ideal_generated_rec.
  intros s [r [p q]].
  destruct q.
  exact p.
Defined.

(** TODO: Maximal ideals *)
(** TODO: Principal ideal *)
(** TODO: Prime ideals *)
(** TODO: Radical ideals *)
(** TODO: Minimal ideals *)
(** TODO: Primary ideals *)
