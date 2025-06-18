(** * Biproducts in Categories with Zero Objects

    This file defines biproducts - objects that are simultaneously products
    and coproducts. In additive categories, finite products and coproducts
    coincide, yielding biproducts.
    
    Contents:
    - BiproductData: The structural data of a biproduct
    - IsBiproduct: The axioms that make biproduct data into a true biproduct
    - HasBiproductUniversal: The universal property characterization
    - Biproduct: The complete biproduct structure
    - Helper functions for accessing biproduct components
    
    A biproduct of objects X and Y comes with:
    - Injections: inl : X → X⊕Y and inr : Y → X⊕Y
    - Projections: outl : X⊕Y → X and outr : X⊕Y → Y
    - Relations: outl∘inl = 1, outr∘inr = 1
    - Mixed terms are zero: outl∘inr = 0, outr∘inl = 0
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.

(** * Biproduct Structures *)

(** ** Biproduct Data
    
    The data of a biproduct consists of an object together with injection
    and projection morphisms.
*)

Record BiproductData {C : PreCategory} (X Y : object C) := {
  biproduct_obj : object C;
  
  (* Coproduct structure: injections *)
  inl : morphism C X biproduct_obj;
  inr : morphism C Y biproduct_obj;
  
  (* Product structure: projections *)
  outl : morphism C biproduct_obj X;
  outr : morphism C biproduct_obj Y
}.

Arguments biproduct_obj {C X Y} b : rename.
Arguments inl {C X Y} b : rename.
Arguments inr {C X Y} b : rename.
Arguments outl {C X Y} b : rename.
Arguments outr {C X Y} b : rename.

(** ** Biproduct Axioms
    
    The axioms that make biproduct data into an actual biproduct.
    These ensure the projection-injection pairs behave correctly.
*)

Record IsBiproduct {C : PreCategory} {X Y : object C} 
                   (B : BiproductData X Y) (Z : ZeroObject C) := {
  (* Projection-injection identities *)
  beta_l : (outl B o inl B = 1)%morphism;
  beta_r : (outr B o inr B = 1)%morphism;
  
  (* Mixed terms are zero *)
  mixed_l : (outl B o inr B)%morphism = zero_morphism Z Y X;
  mixed_r : (outr B o inl B)%morphism = zero_morphism Z X Y
}.

Arguments beta_l {C X Y B Z} i : rename.
Arguments beta_r {C X Y B Z} i : rename.
Arguments mixed_l {C X Y B Z} i : rename.
Arguments mixed_r {C X Y B Z} i : rename.

(** ** Universal Property of Biproducts
    
    The universal property states that morphisms into/out of the biproduct
    are uniquely determined by their components.
*)

Record HasBiproductUniversal {C : PreCategory} {X Y : object C} 
                             (B : BiproductData X Y) := {
  (* Universal property as a coproduct *)
  coprod_universal : forall (W : object C) 
    (f : morphism C X W) (g : morphism C Y W),
    Contr {h : morphism C (biproduct_obj B) W | 
           (h o inl B = f)%morphism /\ 
           (h o inr B = g)%morphism};
  
  (* Universal property as a product *)
  prod_universal : forall (W : object C) 
    (f : morphism C W X) (g : morphism C W Y),
    Contr {h : morphism C W (biproduct_obj B) | 
           (outl B o h = f)%morphism /\ 
           (outr B o h = g)%morphism}
}.

Arguments coprod_universal {C X Y B} u W f g : rename.
Arguments prod_universal {C X Y B} u W f g : rename.

(** ** Complete Biproduct Structure
    
    A biproduct is biproduct data together with the proof that it satisfies
    the biproduct axioms and universal property.
*)

Record Biproduct {C : PreCategory} (X Y : object C) (Z : ZeroObject C) := {
  biproduct_data : BiproductData X Y;
  biproduct_is : IsBiproduct biproduct_data Z;
  biproduct_universal : HasBiproductUniversal biproduct_data
}.

Arguments biproduct_data {C X Y Z} b : rename.
Arguments biproduct_is {C X Y Z} b : rename.
Arguments biproduct_universal {C X Y Z} b : rename.

(** * Biproduct Operations *)

Section BiproductOperations.
  Context {C : PreCategory} {X Y : object C} {Z : ZeroObject C}.
  Variable (B : Biproduct X Y Z).

  (** The underlying biproduct object. *)
  Definition biproduct : object C := biproduct_obj (biproduct_data B).

  (** ** Accessing Morphisms *)
  
  Definition bi_inl : morphism C X biproduct := inl (biproduct_data B).
  Definition bi_inr : morphism C Y biproduct := inr (biproduct_data B).
  Definition bi_outl : morphism C biproduct X := outl (biproduct_data B).
  Definition bi_outr : morphism C biproduct Y := outr (biproduct_data B).

  (** ** Uniqueness from Universal Property *)

  (** Extract the unique morphism from the coproduct universal property. *)
  Definition biproduct_coprod_mor (W : object C) 
    (f : morphism C X W) (g : morphism C Y W)
    : morphism C biproduct W
    := pr1 (@center _ (coprod_universal (biproduct_universal B) W f g)).

  Lemma biproduct_coprod_beta_l (W : object C) 
    (f : morphism C X W) (g : morphism C Y W)
    : (biproduct_coprod_mor W f g o bi_inl = f)%morphism.
  Proof.
    unfold biproduct_coprod_mor, bi_inl.
    generalize (@center _ (coprod_universal (biproduct_universal B) W f g)).
    intros [h [Hl Hr]].
    simpl.
    exact Hl.
  Qed.

  Lemma biproduct_coprod_beta_r (W : object C) 
    (f : morphism C X W) (g : morphism C Y W)
    : (biproduct_coprod_mor W f g o bi_inr = g)%morphism.
  Proof.
    unfold biproduct_coprod_mor, bi_inr.
    generalize (@center _ (coprod_universal (biproduct_universal B) W f g)).
    intros [h [Hl Hr]].
    simpl.
    exact Hr.
  Qed.

  (** Extract the unique morphism from the product universal property. *)
  Definition biproduct_prod_mor (W : object C) 
    (f : morphism C W X) (g : morphism C W Y)
    : morphism C W biproduct
    := pr1 (@center _ (prod_universal (biproduct_universal B) W f g)).

  Lemma biproduct_prod_beta_l (W : object C) 
    (f : morphism C W X) (g : morphism C W Y)
    : (bi_outl o biproduct_prod_mor W f g = f)%morphism.
  Proof.
    unfold biproduct_prod_mor, bi_outl.
    generalize (@center _ (prod_universal (biproduct_universal B) W f g)).
    intros [h [Hl Hr]].
    simpl.
    exact Hl.
  Qed.

  Lemma biproduct_prod_beta_r (W : object C) 
    (f : morphism C W X) (g : morphism C W Y)
    : (bi_outr o biproduct_prod_mor W f g = g)%morphism.
  Proof.
    unfold biproduct_prod_mor, bi_outr.
    generalize (@center _ (prod_universal (biproduct_universal B) W f g)).
    intros [h [Hl Hr]].
    simpl.
    exact Hr.
  Qed.

(** ** Uniqueness Properties *)

  Lemma biproduct_coprod_unique (W : object C) 
    (f : morphism C X W) (g : morphism C Y W)
    (h : morphism C biproduct W)
    : (h o bi_inl = f)%morphism -> 
      (h o bi_inr = g)%morphism ->
      h = biproduct_coprod_mor W f g.
  Proof.
    intros Hl Hr.
    unfold biproduct_coprod_mor, bi_inl, bi_inr in *.
    assert (p : (h; (Hl, Hr)) = @center _ (coprod_universal (biproduct_universal B) W f g)).
    { apply (@path_contr _ (coprod_universal (biproduct_universal B) W f g)). }
    exact (ap pr1 p).
  Qed.

  Lemma biproduct_prod_unique (W : object C) 
    (f : morphism C W X) (g : morphism C W Y)
    (h : morphism C W biproduct)
    : (bi_outl o h = f)%morphism -> 
      (bi_outr o h = g)%morphism ->
      h = biproduct_prod_mor W f g.
  Proof.
    intros Hl Hr.
    unfold biproduct_prod_mor, bi_outl, bi_outr in *.
    assert (p : (h; (Hl, Hr)) = @center _ (prod_universal (biproduct_universal B) W f g)).
    { apply (@path_contr _ (prod_universal (biproduct_universal B) W f g)). }
    exact (ap pr1 p).
  Qed.

End BiproductOperations.

(** * Export Hints *)

Hint Resolve 
  biproduct_coprod_beta_l biproduct_coprod_beta_r
  biproduct_prod_beta_l biproduct_prod_beta_r
  : biproduct.

Hint Rewrite 
  @zero_morphism_left @zero_morphism_right
  : biproduct_simplify.

(** The next file in the library will be [AdditiveCategories.v] which defines
    additive categories using zero objects and biproducts. *)