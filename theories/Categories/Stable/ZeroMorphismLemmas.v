(** * Transport Lemmas and Morphism Properties for Categories with Zero Objects

    This file contains technical lemmas about morphisms in categories with zero
    objects, particularly focusing on transport along equality proofs and
    morphism composition properties.
    
    Contents:
    - Transport lemmas for morphisms along object equalities
    - Interaction of transport with initial/terminal morphisms
    - Basic morphism identities (included here for completeness)
    - Helper lemmas for morphism equations
    
    These lemmas are essential for working with morphisms in stable category theory,
    where we frequently need to transport along equivalences.
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor.
Require Import ZeroObjects.

(** * Transport Lemmas for Morphisms
    
    These lemmas handle how morphisms behave under transport along
    equality proofs between objects.
*)

Section TransportLemmas.
  Context {C : PreCategory}.

  (** Transport distributes over composition. *)
  Lemma transport_compose_morphism
    {X Y Z W : object C} (p : X = W)
    (f : morphism C X Y) (g : morphism C Y Z)
    : transport (fun U => morphism C U Z) p (g o f)%morphism =
      (g o transport (fun U => morphism C U Y) p f)%morphism.
  Proof.
    destruct p; reflexivity.
  Qed.

  (** Transport in the middle of a composition. *)
  Lemma transport_morphism_compose_middle
    {W X Y Z : object C} (p : W = X)
    (f : morphism C Y W) (g : morphism C Z Y)
    : (transport (fun U => morphism C Y U) p f o g)%morphism =
      transport (fun U => morphism C Z U) p (f o g)%morphism.
  Proof.
    destruct p. reflexivity.
  Qed.

  (** Composing transported morphisms. *)
  Lemma transport_compose_both_inverse
    {W X Y Z : object C} (p : W = X)
    (f : morphism C W Z) (g : morphism C Y W)
    : (transport (fun U : object C => morphism C U Z) p f o 
       transport (fun U : object C => morphism C Y U) p g)%morphism =
      (f o g)%morphism.
  Proof.
    destruct p. reflexivity.
  Qed.

  (** Transport inverse cancels transport. *)
  Lemma transport_inverse_is_inverse {A : Type} {B : A -> Type}
    {x y : A} (p : x = y) (b : B x)
    : transport B p^ (transport B p b) = b.
  Proof.
    destruct p. reflexivity.
  Qed.

  (** Transport along inverse path. *)
  Lemma transport_inverse_eq {A : Type} {P : A -> Type} 
    {x y : A} (p : x = y) (u : P x) (v : P y)
    : transport P p u = v -> u = transport P p^ v.
  Proof.
    intro H.
    rewrite <- H.
    destruct p.
    reflexivity.
  Qed.

  (** Morphism equation via transport inverse. *)
  Lemma morphism_eq_transport_inverse
    {W X Y : object C} (p : W = X)
    (f : morphism C W Y) (g : morphism C X Y)
    : transport (fun Z => morphism C Z Y) p f = g ->
      f = transport (fun Z => morphism C Z Y) p^ g.
  Proof.
    intro H.
    rewrite <- H.
    destruct p.
    reflexivity.
  Qed.

End TransportLemmas.

(** * Transport with Zero Objects *)

Section TransportZero.
  Context {C : PreCategory} (Z : ZeroObject C).

  (** Transport of initial morphisms. *)
  Lemma transport_initial_morphism
    (I I' X : object C) (p : I = I')
    (H_initial : Contr (morphism C I X))
    (H_initial' : Contr (morphism C I' X))
    (f : morphism C I X)
    : transport (fun U => morphism C U X) p f = 
      @center _ H_initial'.
  Proof.
    apply (@contr _ H_initial' (transport (fun U => morphism C U X) p f))^.
  Qed.

  (** Transport of terminal morphisms. *)
  Lemma transport_terminal_morphism
    (X T T' : object C) (p : T = T')
    (H_terminal : Contr (morphism C X T))
    (H_terminal' : Contr (morphism C X T'))
    (f : morphism C X T)
    : transport (fun U => morphism C X U) p f = 
      @center _ H_terminal'.
  Proof.
    apply (@contr _ H_terminal' (transport (fun U => morphism C X U) p f))^.
  Qed.

End TransportZero.

(** * Basic Morphism Identities
    
    These are included here for completeness, as they are used throughout
    the library. They are just the standard category laws.
*)

Section MorphismIdentities.
  Context {C : PreCategory}.

  Lemma morphism_right_identity {X Y : object C} (f : morphism C X Y)
    : (f o 1)%morphism = f.
  Proof.
    apply Category.Core.right_identity.
  Qed.

  Lemma morphism_left_identity {X Y : object C} (f : morphism C X Y)
    : (1 o f)%morphism = f.
  Proof.
    apply Category.Core.left_identity.
  Qed.

  Lemma morphism_associativity {W X Y Z : object C} 
    (f : morphism C W X) (g : morphism C X Y) (h : morphism C Y Z)
    : ((h o g) o f)%morphism = (h o (g o f))%morphism.
  Proof.
    apply Category.Core.associativity.
  Qed.

End MorphismIdentities.

(** * Helper Lemmas for Morphism Equations *)

Section MorphismHelpers.
  Context {C : PreCategory}.

  (** Applying a morphism to both sides of an equation. *)
  Lemma ap_morphism_comp_left {X Y Z : object C} 
    (f : morphism C Y Z) (g h : morphism C X Y)
    : g = h -> (f o g)%morphism = (f o h)%morphism.
  Proof.
    intro H.
    rewrite H.
    reflexivity.
  Qed.

  Lemma ap_morphism_comp_right {X Y Z : object C}
    (p1 p2 : morphism C Y Z) (q : morphism C X Y)
    : p1 = p2 -> (p1 o q)%morphism = (p2 o q)%morphism.
  Proof.
    intro H.
    rewrite H.
    reflexivity.
  Qed.

  (** Identity in the middle of a composition. *)
  Lemma composition_with_identity_middle {A B X D : object C}
    (f : morphism C X D)
    (g : morphism C B X) 
    (h : morphism C A B)
    : (f o 1 o g o h)%morphism = (f o g o h)%morphism.
  Proof.
    rewrite morphism_right_identity.
    reflexivity.
  Qed.

  (** Rearranging associativity. *)
  Lemma rearrange_middle_composition {A B X D E : object C}
    (f : morphism C D E)
    (g : morphism C X D)
    (h : morphism C B X)
    (k : morphism C A B)
    : (f o (g o (h o k)))%morphism = (f o ((g o h) o k))%morphism.
  Proof.
    rewrite morphism_associativity.
    reflexivity.
  Qed.

End MorphismHelpers.

(** * Export Hints and Notations *)

Hint Rewrite 
  @morphism_left_identity 
  @morphism_right_identity 
  @transport_inverse_is_inverse 
  : morphism_simplify.

Hint Resolve 
  @transport_initial_morphism 
  @transport_terminal_morphism 
  : transport_morphism.

(** The next file in the library will be [Biproducts.v] which defines
    biproduct structures in categories with zero objects. *)