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
  (biproduct_obj (biproduct_data (semiadditive_biproduct X Y)))
  (at level 40, left associativity).

(** ** Morphism addition via biproducts 

    Addition is the codiagonal composed with the pairing morphism. *)

Section MorphismAddition.
  Context (C : SemiAdditiveCategory) (X Y : object C).
  
  (** Codiagonal composed with pairing. *)
  #[export] Instance sgop_morphism : SgOp (morphism C X Y) :=
    fun f g =>
      (biproduct_coprod_mor _ Y 1%morphism 1%morphism
       o biproduct_prod_mor _ X f g)%morphism.
  
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
    rewrite biproduct_prod_zero_l.
    rewrite <- Category.Core.associativity.
    rewrite biproduct_coprod_beta_r.
    rapply Category.Core.left_identity.
  Qed.

  (** Zero is a right identity for morphism addition. *)
  Theorem zero_right_identity (X Y : object C) (f : morphism C X Y)
    : sgop_morphism C X Y f (zero_morphism X Y) = f.
  Proof.
    unfold sgop_morphism.
    rewrite biproduct_prod_zero_r.
    rewrite <- Category.Core.associativity.
    rewrite biproduct_coprod_beta_l.
    rapply Category.Core.left_identity.
  Qed.

End IdentityLaws.

(** ** Swap morphism for biproducts *)

Section BiproductSwap.
  Context (C : SemiAdditiveCategory).

  (** The swap morphism for biproducts. *)
  Definition biproduct_swap (A : object C)
    : morphism C (A ⊕ A) (A ⊕ A)
    := biproduct_prod_mor _ (A ⊕ A) (outr _) (outl _).

  (** Swapping components of a biproduct morphism. *)
  Lemma biproduct_prod_swap (A B : object C) (f g : morphism C A B)
    : biproduct_prod_mor _ A g f
      = (biproduct_swap B o biproduct_prod_mor _ A f g)%morphism.
  Proof.
    symmetry.
    rapply biproduct_prod_unique.
    - rewrite <- Category.Core.associativity.
      unfold biproduct_swap.
      rewrite biproduct_prod_beta_l.
      rapply biproduct_prod_beta_r.
    - rewrite <- Category.Core.associativity.
      unfold biproduct_swap.
      rewrite biproduct_prod_beta_r.
      rapply biproduct_prod_beta_l.
  Qed.

  (** Swap composed with left injection gives right injection. *)
  Lemma swap_inl (Y : object C)
    : (biproduct_swap Y o Biproducts.inl _)%morphism = Biproducts.inr _.
  Proof.
    unfold biproduct_swap.
    rewrite biproduct_prod_comp.
    rewrite (beta_l (biproduct_is _)).
    rewrite (mixed_r (biproduct_is _)).
    rewrite biproduct_prod_zero_l.
    rewrite Category.Core.right_identity.
    reflexivity.
  Qed.

  (** Swap composed with right injection gives left injection. *)
  Lemma swap_inr (Y : object C)
    : (biproduct_swap Y o Biproducts.inr _)%morphism = Biproducts.inl _.
  Proof.
    unfold biproduct_swap.
    rewrite biproduct_prod_comp.
    rewrite (mixed_l (biproduct_is _)).
    rewrite (beta_r (biproduct_is _)).
    rewrite biproduct_prod_zero_r.
    rewrite Category.Core.right_identity.
    reflexivity.
  Qed.

  (** The codiagonal is invariant under swapping. *)
  Lemma codiagonal_swap_invariant (Y : object C)
    : (biproduct_coprod_mor _ Y 1%morphism 1%morphism o biproduct_swap Y)%morphism
      = biproduct_coprod_mor _ Y 1%morphism 1%morphism.
  Proof.
    rapply (biproduct_coprod_unique _).
    - rewrite Category.Core.associativity.
      rewrite swap_inl.
      rapply biproduct_coprod_beta_r.
    - rewrite Category.Core.associativity.
      rewrite swap_inr.
      rapply biproduct_coprod_beta_l.
  Qed.

End BiproductSwap.

(** ** Commutativity of morphism addition *)

  Theorem morphism_addition_commutative (C : SemiAdditiveCategory)
    (X Y : object C)
    : Commutative (@sgop_morphism C X Y).
  Proof.
    intros f g.
    unfold sgop_morphism.
    rewrite (biproduct_prod_swap C X Y f g).
    rewrite <- Category.Core.associativity.
    rewrite codiagonal_swap_invariant.
    reflexivity.
  Qed.

(** ** Associativity of morphism addition *)

Section Associativity.
  Context (C : SemiAdditiveCategory).

  Lemma codiagonal_postcompose_any (Y Y' : object C) (a : morphism C Y Y')
    : (a o biproduct_coprod_mor _ Y 1%morphism 1%morphism)%morphism
      = biproduct_coprod_mor _ Y' a a.
  Proof.
    rapply (biproduct_coprod_unique _ Y' a a).
    - rewrite Category.Core.associativity.
      rewrite biproduct_coprod_beta_l.
      rapply Category.Core.right_identity.
    - rewrite Category.Core.associativity.
      rewrite biproduct_coprod_beta_r.
      rapply Category.Core.right_identity.
  Qed.

  Lemma addition_precompose
    (X Y W : object C) (f g : morphism C X Y) (a : morphism C W X)
    : (sgop_morphism C X Y f g o a)%morphism
      = sgop_morphism C W Y (f o a)%morphism (g o a)%morphism.
  Proof.
    unfold sgop_morphism.
    rewrite Category.Core.associativity.
    rewrite (@biproduct_prod_comp C semiadditive_zero Y Y _ W X f g a).
    reflexivity.
  Qed.

  Lemma biproduct_pair_naturality (X Y Y' : object C) (a : morphism C Y Y') (f g : morphism C X Y)
    : biproduct_prod_mor _ X (a o f) (a o g)
      = (biproduct_prod_mor _ (Y ⊕ Y) (a o outl _) (a o outr _)
         o biproduct_prod_mor _ X f g)%morphism.
  Proof.
    symmetry.
    rapply biproduct_prod_unique.
    - rewrite <- Category.Core.associativity.
      rewrite biproduct_prod_beta_l.
      rewrite Category.Core.associativity.
      rewrite biproduct_prod_beta_l.
      reflexivity.
    - rewrite <- Category.Core.associativity.
      rewrite biproduct_prod_beta_r.
      rewrite Category.Core.associativity.
      rewrite biproduct_prod_beta_r.
      reflexivity.
  Qed.
  
  Lemma codiagonal_pair_inl (Y Y' : object C) (a b : morphism C Y Y')
    : (biproduct_coprod_mor _ Y' 1%morphism 1%morphism
       o (biproduct_prod_mor _ (Y ⊕ Y) (a o outl _) (b o outr _)
          o Biproducts.inl _))%morphism
      = a.
  Proof.
    rewrite <- Category.Core.associativity.
    rewrite addition_precompose.
    rewrite Category.Core.associativity.
    rewrite (beta_l (biproduct_is _)).
    rewrite Category.Core.right_identity.
    rewrite Category.Core.associativity.
    rewrite (mixed_r (biproduct_is _)).
    rewrite zero_morphism_right.
    apply zero_right_identity.
  Qed.

  Lemma codiagonal_pair_inr (Y Y' : object C) (a b : morphism C Y Y')
    : (biproduct_coprod_mor _ Y' 1%morphism 1%morphism
       o (biproduct_prod_mor _ (Y ⊕ Y) (a o outl _) (b o outr _)
          o Biproducts.inr _))%morphism
      = b.
  Proof.
    rewrite <- Category.Core.associativity.
    rewrite addition_precompose.
    rewrite Category.Core.associativity.
    rewrite (mixed_l (biproduct_is _)).
    rewrite zero_morphism_right.
    rewrite Category.Core.associativity.
    rewrite (beta_r (biproduct_is _)).
    rewrite Category.Core.right_identity.
    apply zero_left_identity.
  Qed.

  Lemma codiagonal_factor_through_pair (Y Y' : object C) (a b : morphism C Y Y')
    : (biproduct_coprod_mor _ Y' 1%morphism 1%morphism
       o biproduct_prod_mor _ (Y ⊕ Y) (a o outl _) (b o outr _))%morphism
      = biproduct_coprod_mor _ Y' a b.
  Proof.
    rapply (biproduct_coprod_unique _ Y' a b).
    - rewrite Category.Core.associativity.
      rapply codiagonal_pair_inl.
    - rewrite Category.Core.associativity.
      rapply codiagonal_pair_inr.
  Qed.

  Lemma addition_postcompose
    (X Y Y' : object C) (f g : morphism C X Y) (a : morphism C Y Y')
    : (a o sgop_morphism C X Y f g)%morphism
      = sgop_morphism C X Y' (a o f)%morphism (a o g)%morphism.
  Proof.
    unfold sgop_morphism.
    rewrite <- Category.Core.associativity.
    rewrite (codiagonal_postcompose_any Y Y' a).
    rewrite <- (codiagonal_factor_through_pair Y Y' a a).
    rewrite Category.Core.associativity.
    rewrite <- (biproduct_pair_naturality X Y Y' a f g).
    reflexivity.
  Qed.
  
  Lemma addition_of_pairs (X Y : object C) (f1 f2 g1 g2 : morphism C X Y)
    : sgop_morphism C X (Y ⊕ Y)
        (biproduct_prod_mor _ X f1 g1)
        (biproduct_prod_mor _ X f2 g2)
      = biproduct_prod_mor _ X
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

  Theorem morphism_addition_associative
    (X Y : object C) (f g h : morphism C X Y)
    : ((f + g) + h = f + (g + h))%morphism.
  Proof.
    set (BY := semiadditive_biproduct Y Y).
    unfold sgop_morphism at 1.
    etransitivity
      ((biproduct_coprod_mor BY Y 1%morphism 1%morphism
        o biproduct_prod_mor BY X ((f + g)%morphism) 
            ((zero_morphism X Y + h)%morphism))%morphism).
    { refine (
        ap011 (fun x y =>
          (biproduct_coprod_mor BY Y 1%morphism 1%morphism
           o biproduct_prod_mor BY X x y)%morphism)
          (idpath _)
          ((@zero_left_identity C X Y h)^)
      ). }
    rewrite <- (addition_of_pairs X Y f g (zero_morphism X Y) h).
    rewrite (addition_postcompose
               X
               (Y ⊕ Y)
               Y
               (biproduct_prod_mor BY X f (zero_morphism X Y))
               (biproduct_prod_mor BY X g h)
               (biproduct_coprod_mor BY Y 1%morphism 1%morphism)).
    rewrite biproduct_prod_zero_r.
    rewrite <- Category.Core.associativity.
    rewrite biproduct_coprod_beta_l.
    rewrite Category.Core.left_identity.
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
