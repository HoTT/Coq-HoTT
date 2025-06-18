(** * Technical Lemmas for the Octahedral Axiom

    This file develops the technical machinery needed for the octahedral axiom (TR4).
    The octahedral axiom describes how distinguished triangles arising from 
    composable morphisms fit together in a precise octahedral pattern.
    
    Contents:
    - Universal property of cofibers
    - Fundamental lemmas for cofiber compositions
    - Construction of octahedral morphisms
    - Properties of octahedral morphisms
    - Uniqueness results
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import Triangles.
Require Import PreStableCofiber.

(** * Universal Property of Cofibers *)

Section UniversalProperty.
  Context (S : PreStableCategoryWithCofiber).

  (** The universal property states that morphisms from the source that vanish
      on the given morphism factor uniquely through the cofiber. *)
  Definition cofiber_universal_property : Type
    := forall (X Y : object S) (f : morphism S X Y) (W : object S)
              (h : morphism S Y W),
       (h o f)%morphism = add_zero_morphism S X W ->
       { k : morphism S (@cofiber S X Y f) W |
         (k o @cofiber_in S X Y f)%morphism = h /\
         forall k' : morphism S (@cofiber S X Y f) W,
         (k' o @cofiber_in S X Y f)%morphism = h -> k' = k }.

End UniversalProperty.

(** * Fundamental Lemmas for Cofiber Compositions *)

Section CofiberCompositions.
  Context (S : PreStableCategoryWithCofiber).

  (** The cofiber inclusion of a composite morphism vanishes when composed
      with the composite itself. *)
  Lemma cofiber_in_composition {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : (@cofiber_in S A C (g o f)%morphism o g o f)%morphism = 
      add_zero_morphism S A (@cofiber S A C (g o f)%morphism).
  Proof.
    (* The expression (cofiber_in S (g o f) o g o f) is parsed as 
       ((cofiber_in S (g o f) o g) o f) *)
    (* We want to rewrite it as (cofiber_in S (g o f) o (g o f)) *)
    rewrite morphism_associativity.
    (* Apply the cofiber condition *)
    apply (@cofiber_cond1 S A C (g o f)%morphism).
  Qed.

  (** A morphism that vanishes after precomposition with f factors uniquely
      through the cofiber of f. *)
  Lemma morphism_vanishing_on_f_factors
    (H_universal : cofiber_universal_property S)
    {A B W : object S} (f : morphism S A B) (h : morphism S B W)
    : (h o f)%morphism = add_zero_morphism S A W ->
      { k : morphism S (@cofiber S A B f) W |
        (k o @cofiber_in S A B f)%morphism = h /\
        forall k' : morphism S (@cofiber S A B f) W,
        (k' o @cofiber_in S A B f)%morphism = h -> k' = k }.
  Proof.
    intro H_zero.
    
    (* Apply the universal property directly *)
    destruct (H_universal A B f W h H_zero) as [k [Hk_comm Hk_unique]].
    
    (* Package the result *)
    exists k.
    split.
    - exact Hk_comm.
    - exact Hk_unique.
  Qed.

  (** Any morphism factoring through a cofiber vanishes on the original morphism. *)
  Lemma morphism_through_cofiber_vanishes_on_f {A B W : object S} (f : morphism S A B) 
    (k : morphism S B W) (k' : morphism S (@cofiber S A B f) W)
    : k = (k' o @cofiber_in S A B f)%morphism ->
      (k o f)%morphism = add_zero_morphism S A W.
  Proof.
    intro H_factor.
    rewrite H_factor.
    (* Now we have ((k' o cofiber_in S f) o f) *)
    rewrite morphism_associativity.
    (* Now we have (k' o (cofiber_in S f o f)) *)
    rewrite (@cofiber_cond1 S A B f).
    apply zero_morphism_right.
  Qed.

  (** The uniqueness aspect of the universal property: morphisms from the
      cofiber are determined by their composition with the cofiber inclusion. *)
  Lemma cofiber_morphism_uniqueness
    (H_universal : cofiber_universal_property S)
    {A B W : object S} (f : morphism S A B)
    (k₁ k₂ : morphism S (@cofiber S A B f) W)
    : (k₁ o @cofiber_in S A B f)%morphism = (k₂ o @cofiber_in S A B f)%morphism ->
      k₁ = k₂.
  Proof.
    intro H_eq.
    
    (* Both k₁ and k₂ satisfy the factorization property for the same morphism *)
    pose (h := (k₁ o @cofiber_in S A B f)%morphism).
    
    (* First, show that h ∘ f = 0 *)
    assert (H_zero : (h o f)%morphism = add_zero_morphism S A W).
    {
      unfold h.
      rewrite morphism_associativity.
      rewrite (@cofiber_cond1 S A B f).
      apply zero_morphism_right.
    }
    
    (* Apply universal property to get uniqueness *)
    destruct (H_universal A B f W h H_zero) as [k [Hk_comm Hk_unique]].
    
    (* k₁ satisfies the property *)
    assert (H1 : k₁ = k).
    { apply Hk_unique. unfold h. reflexivity. }
    
    (* k₂ also satisfies the property *)
    assert (H2 : k₂ = k).
    { apply Hk_unique. unfold h. rewrite <- H_eq. reflexivity. }
    
    (* Therefore k₁ = k₂ *)
    rewrite H1, H2.
    reflexivity.
  Qed.

End CofiberCompositions.

(** * Construction of Octahedral Morphisms *)

Section OctahedralMorphisms.
  Context (S : PreStableCategoryWithCofiber)
          (H_universal : cofiber_universal_property S).

  (** The cofiber inclusion of a composite, when composed with the second morphism,
      vanishes on the first. *)
  Lemma cofiber_composite_vanishes_on_first {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
      add_zero_morphism S A (@cofiber S A C (g o f)%morphism).
  Proof.
    (* We have ((cofiber_in(g∘f) ∘ g) ∘ f) *)
    (* First show this equals cofiber_in(g∘f) ∘ (g ∘ f) *)
    assert (H: ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
               (@cofiber_in S A C (g o f)%morphism o (g o f)%morphism)%morphism).
    {
      rewrite morphism_associativity.
      reflexivity.
    }
    rewrite H.
    (* Now apply the cofiber condition *)
    exact (@cofiber_cond1 S A C (g o f)%morphism).
  Qed.

  (** The first octahedral morphism: cofiber(f) → cofiber(g∘f). *)
  Lemma cofiber_composite_factors_through_first {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : { u : morphism S (@cofiber S A B f) (@cofiber S A C (g o f)%morphism) |
        (u o @cofiber_in S A B f)%morphism = 
        (@cofiber_in S A C (g o f)%morphism o g)%morphism }.
  Proof.
    (* We need to show that (cofiber_in(g∘f) ∘ g) vanishes on f *)
    assert (H_zero : ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
                     add_zero_morphism S A (@cofiber S A C (g o f)%morphism)).
    {
      apply cofiber_composite_vanishes_on_first.
    }
    
    (* Apply the universal property of cofiber(f) *)
    destruct (morphism_vanishing_on_f_factors S H_universal f 
             (@cofiber_in S A C (g o f)%morphism o g)%morphism H_zero)
      as [u [Hu_comm Hu_unique]].
    
    (* Return just the existence part *)
    exists u.
    exact Hu_comm.
  Qed.

  (** Induced morphisms between cofibers from commutative squares. *)
  Lemma cofiber_morphism_from_square
    {A₁ B₁ A₂ B₂ : object S}
    (f₁ : morphism S A₁ B₁) (f₂ : morphism S A₂ B₂)
    (α : morphism S A₁ A₂) (β : morphism S B₁ B₂)
    : (β o f₁)%morphism = (f₂ o α)%morphism ->
      { γ : morphism S (@cofiber S A₁ B₁ f₁) (@cofiber S A₂ B₂ f₂) |
        (γ o @cofiber_in S A₁ B₁ f₁)%morphism = 
        (@cofiber_in S A₂ B₂ f₂ o β)%morphism }.
  Proof.
    intro H_square.
    
    (* We need to show that cofiber_in(f₂) ∘ β vanishes on f₁ *)
    assert (H_zero : ((@cofiber_in S A₂ B₂ f₂ o β)%morphism o f₁)%morphism =
                     add_zero_morphism S A₁ (@cofiber S A₂ B₂ f₂)).
    {
      rewrite morphism_associativity.
      rewrite H_square.
      rewrite <- morphism_associativity.
      rewrite (@cofiber_cond1 S A₂ B₂ f₂).
      apply zero_morphism_left.
    }
    
    (* Apply universal property and extract just the existence part *)
    destruct (morphism_vanishing_on_f_factors S H_universal f₁ 
             (@cofiber_in S A₂ B₂ f₂ o β)%morphism H_zero)
      as [γ [Hγ_comm Hγ_unique]].
    
    exists γ.
    exact Hγ_comm.
  Qed.

End OctahedralMorphisms.

(** * Properties of Octahedral Morphisms *)

Section OctahedralProperties.
  Context (S : PreStableCategoryWithCofiber).

  (** Composition of compatible cofiber morphisms behaves predictably. *)
  Lemma cofiber_morphism_composition {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    (u : morphism S (@cofiber S A B f) (@cofiber S B C g))
    (v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism))
    : (u o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism ->
      (v o @cofiber_in S B C g)%morphism = @cofiber_in S A C (g o f)%morphism ->
      ((v o u)%morphism o @cofiber_in S A B f)%morphism = 
      (@cofiber_in S A C (g o f)%morphism o g)%morphism.
  Proof.
    intros Hu Hv.
    
    (* We have ((v ∘ u) ∘ cofiber_in(f)) and want to show it equals 
       cofiber_in(g∘f) ∘ g *)
    rewrite morphism_associativity.
    (* Now we have: v ∘ (u ∘ cofiber_in(f)) *)
    rewrite Hu.
    (* Now we have: v ∘ (cofiber_in(g) ∘ g) *)
    rewrite <- morphism_associativity.
    (* Now we have: (v ∘ cofiber_in(g)) ∘ g *)
    rewrite Hv.
    (* Now we have: cofiber_in(g∘f) ∘ g *)
    reflexivity.
  Qed.

End OctahedralProperties.

(** * Uniqueness Results *)

Section UniquenessResults.
  Context (S : PreStableCategoryWithCofiber)
          (H_universal : cofiber_universal_property S).

  (** The octahedral morphisms are unique when they exist. *)
  Theorem octahedral_morphism_unique {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    (u1 u2 : morphism S (@cofiber S A B f) (@cofiber S B C g))
    : (u1 o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism ->
      (u2 o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism ->
      u1 = u2.
  Proof.
    intros H1 H2.
    
    (* Both u1 and u2 satisfy the same property, so by uniqueness they're equal *)
    assert (H_zero : ((@cofiber_in S B C g o g)%morphism o f)%morphism =
                     add_zero_morphism S A (@cofiber S B C g)).
    {
      (* We have (cofiber_in(g) ∘ g) ∘ f *)
      (* By cofiber_cond1, cofiber_in(g) ∘ g = 0 *)
      pose proof (@cofiber_cond1 S B C g) as H_cond.
      rewrite H_cond.
      (* Now we have 0 ∘ f = 0 *)
      apply zero_morphism_left.
    }
    
    (* Apply the uniqueness part of the universal property *)
    destruct (H_universal A B f (@cofiber S B C g) 
             (@cofiber_in S B C g o g)%morphism H_zero) as [u [Hu Hu_unique]].
    
    rewrite (Hu_unique u1 H1).
    rewrite (Hu_unique u2 H2).
    reflexivity.
  Qed.

  (** If the octahedral morphism exists, it's unique. *)
  Theorem octahedral_u_unique {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : forall (u1 u2 : morphism S (@cofiber S A B f) (@cofiber S A C (g o f)%morphism)),
      (u1 o @cofiber_in S A B f)%morphism = 
      (@cofiber_in S A C (g o f)%morphism o g)%morphism ->
      (u2 o @cofiber_in S A B f)%morphism = 
      (@cofiber_in S A C (g o f)%morphism o g)%morphism ->
      u1 = u2.
  Proof.
    intros u1 u2 H1 H2.
    
    (* Both morphisms vanish on f *)
    assert (H_zero : ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
                     add_zero_morphism S A (@cofiber S A C (g o f)%morphism)).
    {
      apply cofiber_composite_vanishes_on_first.
    }
    
    (* Apply uniqueness from the universal property *)
    destruct (morphism_vanishing_on_f_factors S H_universal f 
             (@cofiber_in S A C (g o f)%morphism o g)%morphism H_zero)
      as [u [Hu Hu_unique]].
    
    rewrite (Hu_unique u1 H1).
    rewrite (Hu_unique u2 H2).
    reflexivity.
  Qed.

End UniquenessResults.

(** * Export Hints *)

Hint Resolve 
  cofiber_in_composition
  morphism_through_cofiber_vanishes_on_f
  cofiber_composite_vanishes_on_first
  : octahedral.

Hint Resolve
  octahedral_morphism_unique
  octahedral_u_unique
  : octahedral_unique.

(** The next file in the library will be [OctahedralAxiom.v] which uses
    these lemmas to state and establish the octahedral axiom TR4. *)