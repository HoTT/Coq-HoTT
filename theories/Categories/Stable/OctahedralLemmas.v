(** * Technical lemmas for the octahedral axiom

    Technical machinery for TR4: cofiber universal properties, composition lemmas,
    and construction of octahedral morphisms.
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import Triangles.
Require Import PreStableCofiber.

(** * Universal property of cofibers *)

Section UniversalProperty.
  Context (S : PreStableCategoryWithCofiber).

  (** The universal property states that morphisms from the source that vanish
      on the given morphism factor uniquely through the cofiber. *)
  Definition cofiber_universal_property
    : Type
    := forall (X Y : object S) (f : morphism S X Y) (W : object S)
              (h : morphism S Y W),
       (h o f)%morphism = add_zero_morphism S X W ->
       { k : morphism S (@cofiber S X Y f) W |
         (k o @cofiber_in S X Y f)%morphism = h /\
         forall k' : morphism S (@cofiber S X Y f) W,
         (k' o @cofiber_in S X Y f)%morphism = h -> k' = k }.

End UniversalProperty.

(** * Fundamental lemmas for cofiber compositions *)

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
    rewrite (@cofiber_cond
    