(** * Opposite Categories

    The opposite category construction reverses all morphisms. This file
    shows that additive categories have a natural opposite structure where
    all the additive structure is preserved.
    
    Contents:
    - Basic opposite category construction
    - Opposite zero objects
    - Opposite biproducts
    - Opposite additive categories
    - Basic properties of opposite constructions
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.
Require Import AdditiveCategories.

(** * Basic Opposite Category Construction *)

Definition opposite_category (C : PreCategory) : PreCategory.
Proof.
  exact (@Build_PreCategory
    (object C)
    (fun X Y => morphism C Y X)
    (fun X => 1%morphism)
    (fun X Y Z f g => (g o f)%morphism)
    (fun s d d' d'' m1 m2 m3 => (Category.Core.associativity C d'' d' d s m3 m2 m1)^)
    (fun a b f => Category.Core.right_identity C b a f)
    (fun a b f => Category.Core.left_identity C b a f)
    (fun s d => trunc_morphism C d s)).
Defined.

(** * Basic Properties *)

Section BasicProperties.
  Context {C : PreCategory}.

  (** Objects are the same in both categories. *)
  Lemma opposite_objects : object (opposite_category C) = object C.
  Proof.
    reflexivity.
  Qed.

  (** Morphisms are reversed. *)
  Lemma opposite_morphisms (X Y : object C) 
    : morphism (opposite_category C) X Y = morphism C Y X.
  Proof.
    reflexivity.
  Qed.

  (** Identity morphisms are preserved. *)
  Lemma opposite_identity (X : object C)
    : (1%morphism : morphism (opposite_category C) X X) = (1%morphism : morphism C X X).
  Proof.
    reflexivity.
  Qed.

  (** Composition is reversed. *)
  Lemma opposite_composition {X Y Z : object C} 
    (f : morphism C X Y) (g : morphism C Y Z)
    : let f_op : morphism (opposite_category C) Y X := f in
      let g_op : morphism (opposite_category C) Z Y := g in
      (f_op o g_op)%morphism = (g o f)%morphism.
  Proof.
    reflexivity.
  Qed.

End BasicProperties.

(** * Opposite Zero Object *)

Section OppositeZero.
  Context {C : PreCategory} (Z : ZeroObject C).

  Definition opposite_zero_object : ZeroObject (opposite_category C).
  Proof.
    exact (Build_ZeroObject 
      (opposite_category C)
      (zero Z)
      (fun X => is_terminal Z X)
      (fun X => is_initial Z X)).
  Defined.

  (** Zero morphisms dualize correctly. *)
  Theorem zero_morphism_opposite (X Y : object C)
    : zero_morphism opposite_zero_object Y X = zero_morphism Z X Y.
  Proof.
    unfold zero_morphism.
    simpl.
    reflexivity.
  Qed.

End OppositeZero.

(** * Opposite Biproducts *)

Section OppositeBiproducts.
  Context {C : PreCategory} {X Y : object C}.

  (** Opposite biproduct data swaps the roles of X and Y. *)
  Definition opposite_biproduct_data (B : BiproductData X Y)
    : BiproductData (C:=opposite_category C) Y X.
  Proof.
    exact (Build_BiproductData
      (opposite_category C) Y X
      (biproduct_obj B)
      (outr B)
      (outl B)
      (inr B)
      (inl B)).
  Defined.

  (** Properties of opposite biproducts. *)
  
  Lemma opposite_biproduct_beta_l (B : BiproductData X Y) (Z : ZeroObject C) 
    (H : IsBiproduct B Z)
    : (outl (opposite_biproduct_data B) o inl (opposite_biproduct_data B) = 1)%morphism.
  Proof.
    simpl.
    exact (beta_r H).
  Qed.

  Lemma opposite_biproduct_beta_r (B : BiproductData X Y) (Z : ZeroObject C) 
    (H : IsBiproduct B Z)
    : (outr (opposite_biproduct_data B) o inr (opposite_biproduct_data B) = 1)%morphism.
  Proof.
    simpl.
    exact (beta_l H).
  Qed.

  Lemma opposite_biproduct_mixed_r (B : BiproductData X Y) (Z : ZeroObject C) 
    (H : IsBiproduct B Z)
    : (outr (opposite_biproduct_data B) o inl (opposite_biproduct_data B))%morphism = 
      zero_morphism (opposite_zero_object Z) Y X.
  Proof.
    simpl.
    exact (mixed_r H).
  Qed.

  Lemma opposite_biproduct_mixed_l (B : BiproductData X Y) (Z : ZeroObject C) 
    (H : IsBiproduct B Z)
    : (outl (opposite_biproduct_data B) o inr (opposite_biproduct_data B))%morphism = 
      zero_morphism (opposite_zero_object Z) X Y.
  Proof.
    simpl.
    exact (mixed_l H).
  Qed.

  Definition opposite_is_biproduct (B : BiproductData X Y) (Z : ZeroObject C) 
    (H : IsBiproduct B Z)
    : IsBiproduct (opposite_biproduct_data B) (opposite_zero_object Z).
  Proof.
    exact (Build_IsBiproduct
      (opposite_category C) Y X
      (opposite_biproduct_data B)
      (opposite_zero_object Z)
      (opposite_biproduct_beta_l B Z H)
      (opposite_biproduct_beta_r B Z H)
      (opposite_biproduct_mixed_l B Z H)
      (opposite_biproduct_mixed_r B Z H)).
  Defined.

End OppositeBiproducts.

(** * Universal Property of Opposite Biproducts *)

Section OppositeUniversal.
  Context {C : PreCategory} {X Y : object C}.

  (** Helper equivalence for swapping products. *)
  Lemma swap_product_equiv {A : Type} {P Q : A -> Type}
    : {a : A & (P a * Q a)} <~> {a : A & (Q a * P a)}.
  Proof.
    apply equiv_functor_sigma_id.
    intro a.
    apply equiv_prod_symm.
  Defined.

  Lemma swap_product_contr {A : Type} {P Q : A -> Type}
    : Contr {a : A & (P a * Q a)} ->
      Contr {a : A & (Q a * P a)}.
  Proof.
    intro H.
    apply (contr_equiv' _ (swap_product_equiv)).
  Qed.

  Lemma opposite_coprod_universal (B : BiproductData X Y) 
    (H : HasBiproductUniversal B)
    : forall (W : object (opposite_category C)) 
             (f : morphism (opposite_category C) Y W) 
             (g : morphism (opposite_category C) X W),
      Contr {h : morphism (opposite_category C) (biproduct_obj (opposite_biproduct_data B)) W | 
             (h o inl (opposite_biproduct_data B) = f)%morphism /\ 
             (h o inr (opposite_biproduct_data B) = g)%morphism}.
  Proof.
    intros W f g.
    simpl in *.
    apply swap_product_contr.
    exact (prod_universal H W g f).
  Qed.

  Lemma opposite_prod_universal (B : BiproductData X Y) 
    (H : HasBiproductUniversal B)
    : forall (W : object (opposite_category C)) 
             (f : morphism (opposite_category C) W Y) 
             (g : morphism (opposite_category C) W X),
      Contr {h : morphism (opposite_category C) W (biproduct_obj (opposite_biproduct_data B)) | 
             (outl (opposite_biproduct_data B) o h = f)%morphism /\ 
             (outr (opposite_biproduct_data B) o h = g)%morphism}.
  Proof.
    intros W f g.
    simpl in *.
    apply swap_product_contr.
    exact (coprod_universal H W g f).
  Qed.

  Definition opposite_biproduct_universal (B : BiproductData X Y) 
    (H : HasBiproductUniversal B)
    : HasBiproductUniversal (opposite_biproduct_data B).
  Proof.
    exact (Build_HasBiproductUniversal
      (opposite_category C) Y X
      (opposite_biproduct_data B)
      (opposite_coprod_universal B H)
      (opposite_prod_universal B H)).
  Defined.

  Definition opposite_biproduct (Z : ZeroObject C) (B : Biproduct X Y Z)
    : Biproduct (C:=opposite_category C) Y X (opposite_zero_object Z).
  Proof.
    exact (Build_Biproduct
      (opposite_category C) Y X
      (opposite_zero_object Z)
      (opposite_biproduct_data (biproduct_data B))
      (opposite_is_biproduct (biproduct_data B) Z (biproduct_is B))
      (opposite_biproduct_universal (biproduct_data B) (biproduct_universal B))).
  Defined.

End OppositeUniversal.

(** * Opposite Additive Category *)

Definition opposite_additive_category (A : AdditiveCategory) : AdditiveCategory.
Proof.
  refine (Build_AdditiveCategory
    (opposite_category A)
    (opposite_zero_object (add_zero A))
    (fun X Y => opposite_biproduct (add_zero A) (add_biproduct A Y X))).
Defined.

(** Notation for opposite additive category. *)
Notation "A ^add_op" := (opposite_additive_category A) (at level 10).

(** * Properties of Opposite Additive Categories *)

Section OppositeAdditiveProperties.
  Context (A : AdditiveCategory).

  (** The underlying category of the opposite is the opposite of the underlying category. *)
  Lemma opposite_additive_underlying : cat (A^add_op) = opposite_category A.
  Proof.
    reflexivity.
  Qed.

  (** Zero morphisms are preserved. *)
  Lemma opposite_additive_zero_morphism (X Y : object A)
    : add_zero_morphism (A^add_op) Y X = add_zero_morphism A X Y.
  Proof.
    unfold add_zero_morphism.
    apply zero_morphism_opposite.
  Qed.

  (** Biproduct objects are preserved. *)
  Lemma opposite_biproduct_obj (X Y : object A)
    : add_biproduct_obj (A^add_op) X Y = add_biproduct_obj A Y X.
  Proof.
    reflexivity.
  Qed.

End OppositeAdditiveProperties.

(** * Double Opposite Properties *)

Section DoubleOpposite.
  Context (C : PreCategory).

  (** Double opposite functor returns to the original category. *)
  Definition double_opposite_functor : Functor ((opposite_category (opposite_category C))) C.
  Proof.
    exact (Build_Functor
      ((opposite_category (opposite_category C))) C
      (fun X => X)
      (fun X Y f => f)
      (fun X Y Z f g => idpath)
      (fun X => idpath)).
  Defined.

  Definition to_double_opposite_functor : Functor C ((opposite_category (opposite_category C))).
  Proof.
    exact (Build_Functor
      C ((opposite_category (opposite_category C)))
      (fun X => X)
      (fun X Y f => f)
      (fun X Y Z f g => idpath)
      (fun X => idpath)).
  Defined.

  (** Basic involution properties. *)
  
  Lemma opposite_involution_objects : object ((opposite_category (opposite_category C))) = object C.
  Proof.
    reflexivity.
  Qed.

  Lemma opposite_involution_morphisms (X Y : object C)
    : morphism ((opposite_category (opposite_category C))) X Y = morphism C X Y.
  Proof.
    reflexivity.
  Qed.

End DoubleOpposite.

(** * Isomorphisms in Opposite Categories *)

Section OppositeIsomorphisms.
  Context {C : PreCategory}.

  (** Basic definition of isomorphism (local to this file). *)
  Definition IsIsomorphism {X Y : object C} (f : morphism C X Y) : Type
    := { g : morphism C Y X | (g o f = 1)%morphism /\ (f o g = 1)%morphism }.

  (** Isomorphisms are preserved by the opposite construction. *)
  Lemma opposite_preserves_iso {X Y : object C} (f : morphism C X Y)
    : IsIsomorphism f -> 
      { g : morphism (opposite_category C) X Y | 
        (g o f = 1)%morphism /\ (f o g = 1)%morphism }.
  Proof.
    intro H.
    destruct H as [g [Hgf Hfg]].
    exists g.
    split.
    - simpl. exact Hfg.
    - simpl. exact Hfg.
  Qed.

End OppositeIsomorphisms.

(** * Export Hints *)

Hint Resolve 
  opposite_biproduct_beta_l opposite_biproduct_beta_r
  opposite_preserves_iso
  : opposite.

Hint Rewrite 
  @opposite_additive_zero_morphism
  @zero_morphism_opposite
  : opposite_simplify.

(** The next file in the library will be [OppositePreStable.v] which shows
    how pre-stable structures behave under the opposite construction. *)