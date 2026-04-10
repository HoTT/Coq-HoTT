(** * Semi-additive categories

    Categories with zero objects and biproducts, which automatically
    have commutative monoid structures on hom-sets. *)

From HoTT Require Import Basics.Overture.
From HoTT.Categories Require Import Category.Core.
From HoTT.Categories.Additive Require Import ZeroObjects Biproducts.
From HoTT.Classes.interfaces Require Import abstract_algebra.

(** This lets us use "+" notation for the [sgop] instance defined below. *)
Local Open Scope mc_add_scope.

(** ** Definition of semi-additive category *)

Class SemiAdditiveCategory := {
  cat : PreCategory;
  semiadditive_zero :: ZeroObject cat;
  semiadditive_biproduct :: forall (X Y : object cat), Biproduct X Y
}.

Coercion cat : SemiAdditiveCategory >-> PreCategory.

(** Notation for biproduct objects *)
Local Notation "X ⊕ Y" :=
  (semiadditive_biproduct X Y)
  (at level 40, left associativity).

(** ** Morphism addition via biproducts

    Addition is the codiagonal composed with the pairing morphism. *)

Section MorphismAddition.
  Context (C : SemiAdditiveCategory) (X Y : object C).

  (** Codiagonal composed with pairing. *)
  #[export] Instance sgop_morphism : SgOp (morphism C X Y) :=
    fun f g =>
      (biproduct_codiagonal Y o biproduct_sum_pair f g)%morphism.

  (** The zero morphism is the unit for addition. *)
  #[export] Instance monunit_morphism : MonUnit (morphism C X Y)
    := @zero_morphism C semiadditive_zero X Y.

End MorphismAddition.

(** ** Identity laws for morphism addition *)

Section IdentityLaws.
  Context (C : SemiAdditiveCategory).

  (** Zero is a left identity for morphism addition. *)
  Theorem zero_left_identity (X Y : object C) (f : morphism C X Y)
    : sgop_morphism C X Y (zero_morphism X Y) f = f.
  Proof.
    unfold sgop_morphism.
    rapply biproduct_codiagonal_sum_pair_zero_l.
  Qed.

  (** Zero is a right identity for morphism addition. *)
  Theorem zero_right_identity (X Y : object C) (f : morphism C X Y)
    : sgop_morphism C X Y f (zero_morphism X Y) = f.
  Proof.
    unfold sgop_morphism.
    rapply biproduct_codiagonal_sum_pair_zero_r.
  Qed.

End IdentityLaws.

(** ** Commutativity of morphism addition *)

Theorem morphism_addition_commutative (C : SemiAdditiveCategory)
  (X Y : object C)
  : Commutative (@sgop_morphism C X Y).
Proof.
  intros f g.
  unfold sgop_morphism, biproduct_sum_pair.
  rewrite (biproduct_prod_swap f g).
  rewrite <- Category.Core.associativity.
  rewrite biproduct_codiagonal_swap_invariant.
  reflexivity.
Qed.

(** ** Associativity of morphism addition *)

Section Associativity.
  Context (C : SemiAdditiveCategory).

  (** Addition is natural in the domain. *)
  Lemma addition_precompose
    (X Y W : object C) (f g : morphism C X Y) (a : morphism C W X)
    : (sgop_morphism C X Y f g o a)%morphism
      = sgop_morphism C W Y (f o a)%morphism (g o a)%morphism.
  Proof.
    unfold sgop_morphism, biproduct_codiagonal, biproduct_sum_pair.
    rewrite Category.Core.associativity.
    rewrite (@biproduct_prod_mor_nat C semiadditive_zero Y Y _ W X f g a).
    reflexivity.
  Qed.

  (** Addition is natural in the codomain. *)
  Lemma addition_postcompose
    (X Y Y' : object C) (f g : morphism C X Y) (a : morphism C Y Y')
    : (a o sgop_morphism C X Y f g)%morphism
      = sgop_morphism C X Y' (a o f)%morphism (a o g)%morphism.
  Proof.
    unfold sgop_morphism.
    rewrite <- Category.Core.associativity.
    rewrite (biproduct_codiagonal_natural a).
    rewrite <- (biproduct_codiagonal_factor_through_sum_map a a).
    rewrite Category.Core.associativity.
    rewrite <- (biproduct_sum_pair_natural a f g).
    reflexivity.
  Qed.

  Lemma addition_of_pairs (X Y : object C) (f1 f2 g1 g2 : morphism C X Y)
    : sgop_morphism C X (Y ⊕ Y)
        (biproduct_sum_pair f1 g1)
        (biproduct_sum_pair f2 g2)
      = biproduct_sum_pair
          (sgop_morphism C X Y f1 f2)
          (sgop_morphism C X Y g1 g2).
  Proof.
    rapply biproduct_prod_unique.
    - rewrite addition_postcompose.
      rewrite biproduct_prod_beta_l.
      rewrite biproduct_prod_beta_l.
      reflexivity.
    - rewrite addition_postcompose.
      rewrite biproduct_prod_beta_r.
      rewrite biproduct_prod_beta_r.
      reflexivity.
  Qed.

  (** Associativity follows by functoriality of pairing and codiagonal. *)
  Theorem morphism_addition_associative
    (X Y : object C) (f g h : morphism C X Y)
    : ((f + g) + h = f + (g + h))%morphism.
  Proof.
    unfold sgop_morphism at 1.
    etransitivity
      ((biproduct_codiagonal Y
        o biproduct_sum_pair (sgop_morphism C X Y f g)
            (sgop_morphism C X Y (zero_morphism X Y) h))%morphism).
    - rewrite (zero_left_identity C X Y h).
      reflexivity.
    - rewrite <- (addition_of_pairs X Y f g (zero_morphism X Y) h).
      rewrite (addition_postcompose
                 X
                 (Y ⊕ Y)
                 Y
                 (biproduct_sum_pair f (zero_morphism X Y))
                 (biproduct_sum_pair g h)
                 (biproduct_codiagonal Y)).
      rewrite biproduct_codiagonal_sum_pair_zero_r.
      fold (sgop_morphism C X Y g h).
      reflexivity.
  Qed.

End Associativity.

(** ** Main theorem: morphism sets form commutative monoids *)

#[export] Instance is_commutative_monoid_morphisms
  (C : SemiAdditiveCategory) (X Y : object C)
  : IsCommutativeMonoid (morphism C X Y).
Proof.
  split.
  - split.
    + split.
      * exact _.
      * intros f g h.
        unfold sg_op, sgop_morphism.
        symmetry.
        rapply (morphism_addition_associative C X Y).
    + intro f.
      unfold mon_unit, monunit_morphism, sg_op, sgop_morphism.
      rapply (zero_left_identity C X Y).
    + intro f.
      unfold mon_unit, monunit_morphism, sg_op, sgop_morphism.
      rapply (zero_right_identity C X Y).
  - intros f g.
    unfold sg_op, sgop_morphism.
    rapply (morphism_addition_commutative C X Y).
Defined.
