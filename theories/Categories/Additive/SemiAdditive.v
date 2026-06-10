(** * Semi-additive categories

    Categories with zero objects and biproducts, which automatically
    have commutative monoid structures on hom-sets. *)

From HoTT Require Import Basics.Overture Basics.PathGroupoids Basics.Tactics.
From HoTT.Classes.interfaces Require Import abstract_algebra.
From HoTT.Categories Require Import Category.Core.
From HoTT.Categories.Additive Require Import ZeroObjects Biproducts.

Local Open Scope morphism_scope.

(** This lets us use "+" for the [SgOp] instance and "0" for the [MonUnit]
    instance defined below. *)
Local Open Scope mc_add_scope.

(** ** Definition of semi-additive category *)

Class SemiAdditiveCategory := {
  cat : PreCategory;
  semiadditive_zero :: ZeroObject cat;
  semiadditive_biproduct :: forall (X Y : object cat),
    Biproduct semiadditive_zero X Y
}.

Coercion cat : SemiAdditiveCategory >-> PreCategory.

(** Notation for biproduct objects *)
Local Notation "X ⊕ Y" := (semiadditive_biproduct X Y).

(** ** Morphism addition via biproducts

    Addition is the codiagonal composed with the pairing morphism. *)

Section MorphismAddition.
  Context {C : SemiAdditiveCategory} {X Y : object C}.

  (** Codiagonal composed with pairing. *)
  #[export] Instance sgop_morphism : SgOp (morphism C X Y)
    := fun f g =>
        biproduct_codiagonal Y o biproduct_prod_mor (Y ⊕ Y) f g.

  (** The zero morphism is the unit for addition. *)
  #[export] Instance monunit_morphism : MonUnit (morphism C X Y)
    := zero_morphism X Y.

End MorphismAddition.

(** ** Identity laws for morphism addition *)

Section IdentityLaws.
  Context {C : SemiAdditiveCategory}.

  (** Zero is a left identity for morphism addition. *)
  Definition zero_left_identity {X Y : object C} (f : morphism C X Y)
    : 0 + f = f
    := biproduct_codiagonal_prod_zero_l f.

  (** Zero is a right identity for morphism addition. *)
  Definition zero_right_identity {X Y : object C} (f : morphism C X Y)
    : f + 0 = f
    := biproduct_codiagonal_prod_zero_r f.

End IdentityLaws.

(** ** Commutativity of morphism addition *)

Theorem morphism_addition_commutative {C : SemiAdditiveCategory}
  {X Y : object C}
  : Commutative (@sgop_morphism C X Y).
Proof.
  intros f g.
  unfold sgop_morphism.
  rewrite (biproduct_prod_swap f g).
  rewrite <- associativity.
  rewrite biproduct_codiagonal_swap_invariant.
  reflexivity.
Qed.

(** ** Associativity of morphism addition *)

Section Associativity.
  Context {C : SemiAdditiveCategory}.

  (** Addition is natural in the domain. *)
  Lemma addition_precompose {X Y W : object C}
    (f g : morphism C X Y) (a : morphism C W X)
    : (f + g) o a = (f o a) + (g o a).
  Proof.
    unfold sg_op, sgop_morphism.
    rewrite associativity.
    apply ap, biproduct_prod_mor_nat.
  Qed.

  (** Addition is natural in the codomain. *)
  Lemma addition_postcompose {X Y Y' : object C}
    (f g : morphism C X Y) (a : morphism C Y Y')
    : a o (f + g) = (a o f) + (a o g).
  Proof.
    unfold sg_op, sgop_morphism.
    rewrite <- associativity.
    rewrite (biproduct_codiagonal_nat a).
    rewrite <- (biproduct_codiagonal_factor_through_sum_map a a).
    rewrite associativity.
    rewrite <- (biproduct_sum_map_prod a a f g).
    reflexivity.
  Qed.

  (** Sum of pairings is the pairing of the sums. *)
  Lemma addition_of_pairs {X Y Y' : object C}
    (f1 f2 : morphism C X Y) (g1 g2 : morphism C X Y')
    : biproduct_prod_mor (Y ⊕ Y') f1 g1 + biproduct_prod_mor (Y ⊕ Y') f2 g2
      = biproduct_prod_mor (Y ⊕ Y') (f1 + f2) (g1 + g2).
  Proof.
    rapply biproduct_prod_unique.
    - rewrite addition_postcompose.
      rewrite 2 biproduct_prod_beta_l.
      reflexivity.
    - rewrite addition_postcompose.
      rewrite 2 biproduct_prod_beta_r.
      reflexivity.
  Qed.

  (** Associativity follows by functoriality of pairing and codiagonal. *)
  Theorem morphism_addition_associative {X Y : object C}
    (f g h : morphism C X Y)
    : f + (g + h) = (f + g) + h.
  Proof.
    lhs_V exact (ap (fun w => w + (g + h)) (zero_right_identity f)).
    lhs_V exact (ap (fun p => biproduct_codiagonal Y o p)
                   (addition_of_pairs f 0 g h)).
    lhs napply addition_postcompose.
    exact (ap (fun w => (f + g) + w) (zero_left_identity h)).
  Qed.

End Associativity.

(** ** Main theorem: morphism sets form commutative monoids *)

#[export] Instance is_commutative_monoid_morphisms
  (C : SemiAdditiveCategory) (X Y : object C)
  : IsCommutativeMonoid (morphism C X Y).
Proof.
  repeat split.
  - exact _.
  - exact morphism_addition_associative.
  - exact zero_left_identity.
  - exact zero_right_identity.
  - exact morphism_addition_commutative.
Defined.

(** ** Uniqueness of the enrichment

    The canonical addition is the unique family of operations on hom-sets
    with units that distributes over composition.  Commutativity and
    associativity of [op] are not assumed; they follow from uniqueness. *)

Section EnrichmentUniqueness.
  Context {C : SemiAdditiveCategory}
    (op : forall (X Y : object C), morphism C X Y -> morphism C X Y -> morphism C X Y)
    (op_zero : forall (X Y : object C), morphism C X Y)
    (op_zero_l : forall (X Y : object C) (f : morphism C X Y),
      op X Y (op_zero X Y) f = f)
    (op_zero_r : forall (X Y : object C) (f : morphism C X Y),
      op X Y f (op_zero X Y) = f)
    (op_postcompose : forall (X Y Z : object C)
      (h : morphism C Y Z) (f g : morphism C X Y),
      h o op X Y f g = op X Z (h o f) (h o g))
    (op_precompose : forall (X Y Z : object C)
      (f g : morphism C Y Z) (h : morphism C X Y),
      op Y Z f g o h = op X Z (f o h) (g o h))
    (op_zero_postcompose : forall (X Y Z : object C) (h : morphism C Y Z),
      h o op_zero X Y = op_zero X Z).

  (** The unit of any such operation is the zero morphism. *)
  Lemma op_zero_unique (X Y : object C)
    : op_zero X Y = zero_morphism X Y.
  Proof.
    lhs_V apply (op_zero_postcompose X semiadditive_zero Y
      (zero_morphism semiadditive_zero Y)).
    apply morphism_through_zero_is_zero.
  Qed.

  (** Any such operation decomposes the identity of a self-biproduct. *)
  Lemma op_decompose_id (X : object C)
    : op (X ⊕ X) (X ⊕ X)
        (inl (X ⊕ X) o outl (X ⊕ X))
        (inr (X ⊕ X) o outr (X ⊕ X))
      = 1.
  Proof.
    set (B := X ⊕ X).
    transitivity (biproduct_prod_mor B (outl B) (outr B)).
    - apply (biproduct_prod_unique B).
      + rewrite op_postcompose.
        rewrite <- !associativity.
        rewrite (beta_l (biproduct_is B)).
        rewrite (mixed_l (biproduct_is B)).
        rewrite left_identity.
        rewrite zero_morphism_left.
        rewrite <- op_zero_unique.
        apply op_zero_r.
      + rewrite op_postcompose.
        rewrite <- !associativity.
        rewrite (mixed_r (biproduct_is B)).
        rewrite (beta_r (biproduct_is B)).
        rewrite left_identity.
        rewrite zero_morphism_left.
        rewrite <- op_zero_unique.
        apply op_zero_l.
    - symmetry.
      apply (biproduct_prod_unique B).
      all: apply right_identity.
  Qed.

  (** The canonical addition is the unique such operation. *)
  Theorem morphism_addition_unique {X Y : object C} (f g : morphism C X Y)
    : op X Y f g = f + g.
  Proof.
    symmetry.
    unfold sg_op, sgop_morphism, biproduct_codiagonal.
    rewrite <- (left_identity C _ _
      (biproduct_prod_mor (Y ⊕ Y) f g)).
    rewrite <- (op_decompose_id Y).
    rewrite <- associativity.
    rewrite op_postcompose.
    rewrite op_precompose.
    apply ap011.
    - rewrite !associativity.
      rewrite biproduct_prod_beta_l.
      rewrite <- associativity.
      rewrite biproduct_coprod_beta_l.
      apply left_identity.
    - rewrite !associativity.
      rewrite biproduct_prod_beta_r.
      rewrite <- associativity.
      rewrite biproduct_coprod_beta_r.
      apply left_identity.
  Qed.

End EnrichmentUniqueness.
