(** * Semi-additive categories

    Categories with zero objects and biproducts, which automatically 
    have commutative monoid structure on hom-sets. *)

From HoTT Require Import Basics Types.
From HoTT.Categories Require Import Category Functor.
From HoTT.Categories.Additive Require Import ZeroObjects Biproducts.
From HoTT.Classes.interfaces Require Import abstract_algebra canonical_names.

(** ** Definition of semi-additive category *)

Class SemiAdditiveCategory := {
  cat : PreCategory;
  semiadditive_zero :: ZeroObject cat;
  semiadditive_biproduct : forall (X Y : object cat), Biproduct X Y
}.

Coercion cat : SemiAdditiveCategory >-> PreCategory.

(** ** Morphism addition via biproducts 

    Key idea: addition of f,g : X → Y is the codiagonal ∇ : Y⊕Y → Y
    postcomposed with the pairing ⟨f,g⟩ : X → Y⊕Y. *)

Section MorphismAddition.
  Context (C : SemiAdditiveCategory) (X Y : object C).
  
  (** Direct, standard definition: ∇ ∘ ⟨f,g⟩. *)
  Definition morphism_addition : SgOp (morphism C X Y) :=
    fun f g =>
      (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 
         1%morphism 1%morphism
       o biproduct_prod_mor (semiadditive_biproduct Y Y) X 
         f g)%morphism.
  
  (** The zero morphism is the unit for addition. *)
  Definition morphism_zero : MonUnit (morphism C X Y)
    := @zero_morphism C semiadditive_zero X Y.
    
End MorphismAddition.

(** Make the operations instances for typeclass search. *)
#[export] Instance morphism_sgop (C : SemiAdditiveCategory) 
  (X Y : object C) : SgOp (morphism C X Y) 
  := morphism_addition C X Y.

#[export] Instance morphism_monunit (C : SemiAdditiveCategory) 
  (X Y : object C) : MonUnit (morphism C X Y) 
  := morphism_zero C X Y.

(** ** Notation for morphism addition *)

Notation "f + g" := (morphism_addition _ _ _ f g) : morphism_scope.

(** ** Biproduct characterization lemmas *)

Section BiproductCharacterization.
  Context (C : SemiAdditiveCategory).

  (** Every morphism into a biproduct is uniquely determined by 
      its projections. *)
  Lemma biproduct_morphism_unique (Y Z : object C)
    (h : morphism C Z 
      (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y))))
    (f g : morphism C Z Y)
    : (outl (biproduct_data (semiadditive_biproduct Y Y)) o h 
       = f)%morphism
    -> (outr (biproduct_data (semiadditive_biproduct Y Y)) o h 
        = g)%morphism
    -> h = biproduct_prod_mor (semiadditive_biproduct Y Y) Z f g.
  Proof.
    intros Hl Hr.
    set (contr_instance := prod_universal 
      (biproduct_universal (semiadditive_biproduct Y Y)) Z f g).
    set (c := @center _ contr_instance).
    change (h = pr1 c).
    set (hpair := (h; (Hl, Hr)) : {h : morphism C Z _ & _}).
    exact (ap pr1 (@path_contr _ contr_instance hpair c)).
  Qed.

  (** Special cases: biproduct morphisms with zero components. *)
  Lemma biproduct_zero_right_is_inl (Y Z : object C) 
    (h : morphism C Z Y)
    : biproduct_prod_mor (semiadditive_biproduct Y Y) Z 
        h (zero_morphism Z Y)
      = (Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)) 
         o h)%morphism.
  Proof.
    symmetry.
    rapply biproduct_morphism_unique.
    - rewrite <- Category.Core.associativity.
      rewrite (beta_l (biproduct_is (semiadditive_biproduct Y Y))).
      rapply Category.Core.left_identity.
    - rewrite <- Category.Core.associativity.
      rewrite (mixed_r (biproduct_is (semiadditive_biproduct Y Y))).
      rapply zero_morphism_left.
  Qed.

  Lemma biproduct_zero_left_is_inr (Y Z : object C) 
    (h : morphism C Z Y)
    : biproduct_prod_mor (semiadditive_biproduct Y Y) Z 
        (zero_morphism Z Y) h
      = (Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)) 
         o h)%morphism.
  Proof.
    symmetry.
    rapply biproduct_morphism_unique.
    - rewrite <- Category.Core.associativity.
      rewrite (mixed_l (biproduct_is (semiadditive_biproduct Y Y))).
      rapply zero_morphism_left.
    - rewrite <- Category.Core.associativity.
      rewrite (beta_r (biproduct_is (semiadditive_biproduct Y Y))).
      rapply Category.Core.left_identity.
  Qed.

  (** Composition of biproduct morphisms. *)
  Lemma biproduct_comp_general (W X Y Z : object C)
    (f : morphism C W X) (g : morphism C W Y) (h : morphism C Z W)
    : (biproduct_prod_mor (semiadditive_biproduct X Y) W f g 
       o h)%morphism
      = biproduct_prod_mor (semiadditive_biproduct X Y) Z 
          (f o h) (g o h).
  Proof.
    set (XY := semiadditive_biproduct X Y).
    set (bp_univ := prod_universal (biproduct_universal XY) Z 
      (f o h) (g o h)).
    set (lhs := (biproduct_prod_mor XY W f g o h)%morphism).
    assert (Hl : (outl (biproduct_data XY) o lhs)%morphism 
            = (f o h)%morphism).
    { unfold lhs. 
      rewrite <- Category.Core.associativity.
      rewrite biproduct_prod_beta_l.
      reflexivity. }
    assert (Hr : (outr (biproduct_data XY) o lhs)%morphism 
            = (g o h)%morphism).
    { unfold lhs.
      rewrite <- Category.Core.associativity.
      rewrite biproduct_prod_beta_r.
      reflexivity. }
    exact (ap pr1 (@path_contr _ bp_univ (lhs; (Hl, Hr)) 
      (@center _ bp_univ))).
  Qed.

End BiproductCharacterization.

(** ** Identity laws for morphism addition *)

Section IdentityLaws.
  Context (C : SemiAdditiveCategory).

  (** Zero is a left identity for morphism addition. *)
  Theorem zero_left_identity (X Y : object C) (f : morphism C X Y)
    : morphism_addition C X Y (zero_morphism X Y) f = f.
  Proof.
    unfold morphism_addition.
    rewrite biproduct_zero_left_is_inr.
    rewrite <- Category.Core.associativity.
    rewrite biproduct_coprod_beta_r.
    rapply Category.Core.left_identity.
  Qed.

  (** Zero is a right identity for morphism addition. *)
  Theorem zero_right_identity (X Y : object C) (f : morphism C X Y)
    : morphism_addition C X Y f (zero_morphism X Y) = f.
  Proof.
    unfold morphism_addition.
    rewrite biproduct_zero_right_is_inl.
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
    : morphism C 
        (biproduct_obj (biproduct_data (semiadditive_biproduct A A)))
        (biproduct_obj (biproduct_data (semiadditive_biproduct A A)))
    := biproduct_prod_mor (semiadditive_biproduct A A) 
         (biproduct_obj (biproduct_data (semiadditive_biproduct A A)))
         (outr (biproduct_data (semiadditive_biproduct A A)))
         (outl (biproduct_data (semiadditive_biproduct A A))).

  (** Swapping components of a biproduct morphism. *)
  Lemma biproduct_prod_swap (A B : object C) 
    (f g : morphism C A B)
    : biproduct_prod_mor (semiadditive_biproduct B B) A g f 
      = (biproduct_swap B o 
         biproduct_prod_mor (semiadditive_biproduct B B) A f g)%morphism.
  Proof.
    symmetry.
    rapply biproduct_morphism_unique.
    - rewrite <- Category.Core.associativity.
      unfold biproduct_swap.
      rewrite biproduct_prod_beta_l.
      rapply biproduct_prod_beta_r.
    - rewrite <- Category.Core.associativity.
      rewrite biproduct_prod_beta_r.
      rapply biproduct_prod_beta_l.
  Qed.

  (** Swap composed with left injection gives right injection. *)
  Lemma swap_inl (Y : object C)
    : (biproduct_swap Y o 
       Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)))%morphism
      = Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)).
  Proof.
    unfold biproduct_swap; simpl.
    rewrite biproduct_comp_general.
    rewrite (beta_l (biproduct_is (semiadditive_biproduct Y Y))).
    rewrite (mixed_r (biproduct_is (semiadditive_biproduct Y Y))).
    rewrite biproduct_zero_left_is_inr.
    rewrite Category.Core.right_identity.
    reflexivity.
  Qed.

  (** Swap composed with right injection gives left injection. *)
  Lemma swap_inr (Y : object C)
    : (biproduct_swap Y o 
       Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)))%morphism
      = Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)).
  Proof.
    unfold biproduct_swap; simpl.
    rewrite biproduct_comp_general.
    rewrite (mixed_l (biproduct_is (semiadditive_biproduct Y Y))).
    rewrite (beta_r (biproduct_is (semiadditive_biproduct Y Y))).
    rewrite biproduct_zero_right_is_inl.
    rewrite Category.Core.right_identity.
    reflexivity.
  Qed.

  (** The codiagonal is invariant under swapping. *)
  Lemma codiagonal_swap_invariant (Y : object C)
    : (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 
         1%morphism 1%morphism o
       biproduct_swap Y)%morphism 
      = biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 
          1%morphism 1%morphism.
  Proof.
    rapply (biproduct_coprod_unique (semiadditive_biproduct Y Y)).
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
  (X Y : object C) : Commutative (@morphism_addition C X Y).
Proof.
  intros f g.
  unfold morphism_addition.
  rewrite (biproduct_prod_swap C X Y f g).
  rewrite <- Category.Core.associativity.
  rewrite codiagonal_swap_invariant.
  reflexivity.
Qed.

(** ** Associativity of morphism addition *)

Section Associativity.
  Context (C : SemiAdditiveCategory).

  Lemma codiagonal_postcompose_any
    (Y Y' : object C) (a : morphism C Y Y')
    : (a o biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 
           1%morphism 1%morphism)%morphism
      = biproduct_coprod_mor (semiadditive_biproduct Y Y) Y' a a.
  Proof.
    set (B := semiadditive_biproduct Y Y).
    rapply (biproduct_coprod_unique B Y' a a).
    - rewrite Category.Core.associativity.
      rewrite biproduct_coprod_beta_l.
      rapply Category.Core.right_identity.
    - rewrite Category.Core.associativity.
      rewrite biproduct_coprod_beta_r.
      rapply Category.Core.right_identity.
  Qed.

  Lemma addition_precompose
    (X Y W : object C) (f g : morphism C X Y) (a : morphism C W X)
    : (morphism_addition C X Y f g o a)%morphism
      = morphism_addition C W Y (f o a)%morphism (g o a)%morphism.
  Proof.
    unfold morphism_addition.
    rewrite Category.Core.associativity.
    rewrite (@biproduct_comp_general C X Y Y W f g a).
    reflexivity.
  Qed.

  Lemma biproduct_pair_naturality
    (X Y Y' : object C) (a : morphism C Y Y')
    (f g : morphism C X Y)
    : biproduct_prod_mor (semiadditive_biproduct Y' Y') X (a o f) (a o g)
      = (biproduct_prod_mor (semiadditive_biproduct Y' Y')
           (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
           (a o outl (biproduct_data (semiadditive_biproduct Y Y)))
           (a o outr (biproduct_data (semiadditive_biproduct Y Y)))
         o biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism.
  Proof.
    symmetry.
    rapply (biproduct_morphism_unique C Y' X).
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

  Lemma codiagonal_pair_inl
    (Y Y' : object C) (a b : morphism C Y Y')
    : (biproduct_coprod_mor (semiadditive_biproduct Y' Y') Y' 
         1%morphism 1%morphism
       o (biproduct_prod_mor (semiadditive_biproduct Y' Y')
            (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
            (a o outl (biproduct_data (semiadditive_biproduct Y Y)))
            (b o outr (biproduct_data (semiadditive_biproduct Y Y)))
          o Biproducts.inl 
              (biproduct_data (semiadditive_biproduct Y Y))))%morphism
      = a.
  Proof.
    set (BY  := semiadditive_biproduct Y Y).
    set (BY' := semiadditive_biproduct Y' Y').
    rewrite <- Category.Core.associativity.
    rewrite (@addition_precompose
               (biproduct_obj (biproduct_data BY))
               Y'
               Y
               ((a o outl (biproduct_data BY))%morphism)
               ((b o outr (biproduct_data BY))%morphism)
               (Biproducts.inl (biproduct_data BY))).
    transitivity (morphism_addition C Y Y' a (zero_morphism Y Y')).
    - rapply ap011.
      + rewrite Category.Core.associativity.
        rewrite (beta_l (biproduct_is (semiadditive_biproduct Y Y))).
        rapply Category.Core.right_identity.
      + rewrite Category.Core.associativity.
        rewrite (mixed_r (biproduct_is (semiadditive_biproduct Y Y))).
        rapply zero_morphism_right.
    - rapply zero_right_identity.
  Qed.

  Lemma codiagonal_pair_inr
    (Y Y' : object C) (a b : morphism C Y Y')
    : (biproduct_coprod_mor (semiadditive_biproduct Y' Y') Y' 
         1%morphism 1%morphism
       o (biproduct_prod_mor (semiadditive_biproduct Y' Y')
            (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
            (a o outl (biproduct_data (semiadditive_biproduct Y Y)))
            (b o outr (biproduct_data (semiadditive_biproduct Y Y)))
          o Biproducts.inr 
              (biproduct_data (semiadditive_biproduct Y Y))))%morphism
      = b.
  Proof.
    set (BY  := semiadditive_biproduct Y Y).
    set (BY' := semiadditive_biproduct Y' Y').
    rewrite <- Category.Core.associativity.
    rewrite (@addition_precompose
               (biproduct_obj (biproduct_data BY))
               Y'
               Y
               ((a o outl (biproduct_data BY))%morphism)
               ((b o outr (biproduct_data BY))%morphism)
               (Biproducts.inr (biproduct_data BY))).
    transitivity (morphism_addition C Y Y' (zero_morphism Y Y') b).
    - rapply ap011.
      + rewrite Category.Core.associativity.
        rewrite (mixed_l (biproduct_is BY)).
        rapply zero_morphism_right.
      + rewrite Category.Core.associativity.
        rewrite (beta_r (biproduct_is BY)).
        rapply Category.Core.right_identity.
    - rapply zero_left_identity.
  Qed.

  Lemma codiagonal_factor_through_pair
    (Y Y' : object C) (a b : morphism C Y Y')
    : (biproduct_coprod_mor (semiadditive_biproduct Y' Y') Y' 
         1%morphism 1%morphism
       o biproduct_prod_mor (semiadditive_biproduct Y' Y')
           (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
           (a o outl (biproduct_data (semiadditive_biproduct Y Y)))
           (b o outr (biproduct_data (semiadditive_biproduct Y Y))))%morphism
      = biproduct_coprod_mor (semiadditive_biproduct Y Y) Y' a b.
  Proof.
    set (BY  := semiadditive_biproduct Y Y).
    set (BY' := semiadditive_biproduct Y' Y').
    rapply (biproduct_coprod_unique BY Y' a b).
    - rewrite Category.Core.associativity.
      rapply codiagonal_pair_inl.
    - rewrite Category.Core.associativity.
      rapply codiagonal_pair_inr.
  Qed.

  Lemma addition_postcompose
    (X Y Y' : object C) (f g : morphism C X Y) (a : morphism C Y Y')
    : (a o morphism_addition C X Y f g)%morphism
      = morphism_addition C X Y' (a o f)%morphism (a o g)%morphism.
  Proof.
    unfold morphism_addition.
    set (BY  := semiadditive_biproduct Y Y).
    set (BY' := semiadditive_biproduct Y' Y').
    rewrite <- Category.Core.associativity.
    rewrite (codiagonal_postcompose_any Y Y' a).
    rewrite <- (codiagonal_factor_through_pair Y Y' a a).
    rewrite Category.Core.associativity.
    rewrite <- (biproduct_pair_naturality X Y Y' a f g).
    reflexivity.
  Qed.

  Lemma outl_addition_of_pairs
    (X Y : object C)
    (f1 f2 g1 g2 : morphism C X Y)
    : (outl (biproduct_data (semiadditive_biproduct Y Y)) o
       morphism_addition C X
         (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
         (biproduct_prod_mor (semiadditive_biproduct Y Y) X f1 g1)
         (biproduct_prod_mor (semiadditive_biproduct Y Y) X f2 g2))%morphism
      = morphism_addition C X Y f1 f2.
  Proof.
    set (BY := semiadditive_biproduct Y Y).
    rewrite (@addition_postcompose
             X
             (biproduct_obj (biproduct_data BY))
             Y
             (biproduct_prod_mor BY X f1 g1)
             (biproduct_prod_mor BY X f2 g2)
             (outl (biproduct_data BY))).
    rewrite biproduct_prod_beta_l.
    rewrite biproduct_prod_beta_l.
    reflexivity.
  Qed.

  Lemma outr_addition_of_pairs
    (X Y : object C)
    (f1 f2 g1 g2 : morphism C X Y)
    : (outr (biproduct_data (semiadditive_biproduct Y Y)) o
       morphism_addition C X
         (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
         (biproduct_prod_mor (semiadditive_biproduct Y Y) X f1 g1)
         (biproduct_prod_mor (semiadditive_biproduct Y Y) X f2 g2))%morphism
      = morphism_addition C X Y g1 g2.
  Proof.
    set (BY := semiadditive_biproduct Y Y).
    rewrite (@addition_postcompose
             X
             (biproduct_obj (biproduct_data BY))
             Y
             (biproduct_prod_mor BY X f1 g1)
             (biproduct_prod_mor BY X f2 g2)
             (outr (biproduct_data BY))).
    rewrite biproduct_prod_beta_r.
    rewrite biproduct_prod_beta_r.
    reflexivity.
  Qed.

  Lemma addition_of_pairs
    (X Y : object C)
    (f1 f2 g1 g2 : morphism C X Y)
    : morphism_addition C X
        (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
        (biproduct_prod_mor (semiadditive_biproduct Y Y) X f1 g1)
        (biproduct_prod_mor (semiadditive_biproduct Y Y) X f2 g2)
      = biproduct_prod_mor (semiadditive_biproduct Y Y) X
          (morphism_addition C X Y f1 f2)
          (morphism_addition C X Y g1 g2).
  Proof.
    set (BY := semiadditive_biproduct Y Y).
    refine (biproduct_morphism_unique C Y X
              (morphism_addition C X 
                (biproduct_obj (biproduct_data BY))
                (biproduct_prod_mor BY X f1 g1)
                (biproduct_prod_mor BY X f2 g2))
              (morphism_addition C X Y f1 f2)
              (morphism_addition C X Y g1 g2)
              _ _).
    - rapply outl_addition_of_pairs.
    - rapply outr_addition_of_pairs.
  Qed.

  Theorem morphism_addition_associative
    (X Y : object C) (f g h : morphism C X Y)
    : ((f + g) + h = f + (g + h))%morphism.
  Proof.
    set (BY := semiadditive_biproduct Y Y).
    unfold morphism_addition at 1.
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
               (biproduct_obj (biproduct_data BY))
               Y
               (biproduct_prod_mor BY X f (zero_morphism X Y))
               (biproduct_prod_mor BY X g h)
               (biproduct_coprod_mor BY Y 1%morphism 1%morphism)).
    rewrite biproduct_zero_right_is_inl.
    rewrite <- Category.Core.associativity.
    rewrite biproduct_coprod_beta_l.
    rewrite Category.Core.left_identity.
    fold (morphism_addition C X Y g h).
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
        unfold sg_op, morphism_sgop.
        symmetry.
        rapply (morphism_addition_associative C X Y).
    + intro f.
      unfold mon_unit, morphism_monunit, sg_op, morphism_sgop.
      rapply (zero_left_identity C X Y).
    + intro f.
      unfold mon_unit, morphism_monunit, sg_op, morphism_sgop.
      rapply (zero_right_identity C X Y).
  - intros f g.
    unfold sg_op, morphism_sgop.
    rapply (morphism_addition_commutative C X Y).
Defined.

(** ** Bilinearity of composition *)

Theorem composition_left_distributive (C : SemiAdditiveCategory) 
  {X Y Z : object C}
  (h : morphism C Y Z) (f g : morphism C X Y)
  : (h o (f + g))%morphism = ((h o f) + (h o g))%morphism.
Proof.
  exact (addition_postcompose C X Y Z f g h).
Qed.

Theorem composition_right_distributive (C : SemiAdditiveCategory) 
  {X Y Z : object C}
  (f g : morphism C Y Z) (h : morphism C X Y)
  : ((f + g) o h)%morphism = ((f o h) + (g o h))%morphism.
Proof.
  exact (addition_precompose C Y Z X f g h).
Qed.

(** ** Export hints and derived instances *)

#[export] Instance is_semigroup_morphisms (C : SemiAdditiveCategory) 
  (X Y : object C) : IsSemiGroup (morphism C X Y)
  := _.
  
#[export] Instance is_commutative_semigroup_morphisms 
  (C : SemiAdditiveCategory) (X Y : object C)
  : IsCommutativeSemiGroup (morphism C X Y).
Proof.
  split.
  - exact _.
  - exact _.
Defined.
    
