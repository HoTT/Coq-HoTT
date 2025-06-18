(** * Zero Objects in Categories

    This file defines zero objects and zero morphisms in categories, establishing
    the foundational concepts needed for additive and stable category theory.
    
    A zero object is an object that is both initial and terminal, serving as
    the categorical analog of the zero element in an abelian group.
    
    Contents:
    - Definition of zero objects
    - Zero morphisms between arbitrary objects
    - Uniqueness properties of initial and terminal morphisms
    - Basic lemmas about zero morphisms
    
    This is part of the stable category theory library in Homotopy Type Theory.
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories Require Import InitialTerminalCategory.

(** * Zero Objects
    
    A zero object in a category is an object that is both initial and terminal.
    This is the categorical analog of the zero element in an abelian group.
*)

Record ZeroObject (C : PreCategory) := {
  zero : object C;
  is_initial : forall X, Contr (morphism C zero X);
  is_terminal : forall X, Contr (morphism C X zero)
}.

Arguments zero {C} z : rename.
Arguments is_initial {C} z X : rename.
Arguments is_terminal {C} z X : rename.

(** The zero morphism between any two objects is the unique morphism
    that factors through the zero object. *)

Definition zero_morphism {C : PreCategory} (Z : ZeroObject C) (X Y : object C)
  : morphism C X Y
  := (@center _ (@is_initial _ Z Y) o @center _ (@is_terminal _ Z X))%morphism.

(** * Basic Properties of Zero Objects *)

(** ** Uniqueness of Initial and Terminal Morphisms *)

(** Any two morphisms from an initial object are equal. *)
Lemma initial_morphism_unique {C : PreCategory} 
  (I : object C) (X : object C)
  (H_initial : Contr (morphism C I X))
  (f g : morphism C I X)
  : f = g.
Proof.
  transitivity (@center _ H_initial).
  - exact (@contr _ H_initial f)^.
  - exact (@contr _ H_initial g).
Qed.

(** Any two morphisms to a terminal object are equal. *)
Lemma terminal_morphism_unique {C : PreCategory} 
  (X : object C) (T : object C)
  (H_terminal : Contr (morphism C X T))
  (f g : morphism C X T)
  : f = g.
Proof.
  transitivity (@center _ H_terminal).
  - exact (@contr _ H_terminal f)^.
  - exact (@contr _ H_terminal g).
Qed.

(** ** Properties of Zero Morphisms *)

(** Any morphism that factors through a zero object is the zero morphism. *)
Lemma morphism_through_zero_is_zero {C : PreCategory} 
  (Z : ZeroObject C) (X Y : object C)
  (f : morphism C X (zero Z))
  (g : morphism C (zero Z) Y)
  : (g o f)%morphism = zero_morphism Z X Y.
Proof.
  unfold zero_morphism.
  apply ap011.
  - apply initial_morphism_unique.
    apply (is_initial Z).
  - apply terminal_morphism_unique.
    apply (is_terminal Z).
Qed.

(** ** Special Properties of Zero Endomorphisms *)

(** The morphism from zero to itself is the identity. *)
Lemma zero_to_zero_is_id {C : PreCategory} (Z : ZeroObject C)
  : @center _ (is_initial Z (zero Z)) = 1%morphism.
Proof.
  apply (@contr _ (is_initial Z (zero Z))).
Qed.

(** The terminal morphism from zero to itself is the identity. *)
Lemma terminal_zero_to_zero_is_id {C : PreCategory} (Z : ZeroObject C)
  : @center _ (is_terminal Z (zero Z)) = 
    (1%morphism : morphism C (zero Z) (zero Z)).
Proof.
  apply terminal_morphism_unique.
  apply (is_terminal Z (zero Z)).
Qed.

(** Composition with a terminal morphism to zero gives zero morphism. *)
Lemma terminal_comp_is_zero {C : PreCategory} (Z : ZeroObject C) 
  (X Y : object C) 
  (f : morphism C X (zero Z))
  : (@center _ (is_initial Z Y) o f)%morphism = 
    zero_morphism Z X Y.
Proof.
  apply morphism_through_zero_is_zero.
Qed.

(** The zero morphism from zero is the initial morphism. *)
Lemma zero_morphism_from_zero {C : PreCategory} (Z : ZeroObject C) 
  (Y : object C)
  : zero_morphism Z (zero Z) Y = @center _ (is_initial Z Y).
Proof.
  unfold zero_morphism.
  assert (H: @center _ (is_terminal Z (zero Z)) = 
            (1%morphism : morphism C (zero Z) (zero Z))).
  { 
    apply (@contr _ (is_terminal Z (zero Z))).
  }
  rewrite H.
  apply Category.Core.right_identity.
Qed.

(** ** Composition Properties of Zero Morphisms *)

(** Composition with zero morphism on the right. *)
Lemma zero_morphism_right {C : PreCategory} (Z : ZeroObject C) 
  {X Y W : object C}
  (g : morphism C Y W)
  : (g o zero_morphism Z X Y)%morphism = zero_morphism Z X W.
Proof.
  unfold zero_morphism.
  assert (H: (g o @center _ (is_initial Z Y))%morphism = 
             @center _ (is_initial Z W)).
  {
    symmetry.
    apply (@contr _ (is_initial Z W)).
  }
  rewrite <- Category.Core.associativity.
  rewrite H.
  reflexivity.
Qed.

(** Composition with zero morphism on the left. *)
Lemma zero_morphism_left {C : PreCategory} (Z : ZeroObject C) 
  {X Y W : object C}
  (f : morphism C X Y)
  : (zero_morphism Z Y W o f)%morphism = zero_morphism Z X W.
Proof.
  unfold zero_morphism.
  assert (H: (@center _ (is_terminal Z Y) o f)%morphism = 
             @center _ (is_terminal Z X)).
  {
    symmetry.
    apply (@contr _ (is_terminal Z X)).
  }
  rewrite Category.Core.associativity.
  rewrite H.
  reflexivity.
Qed.

(** ** Export Hints *)

Arguments zero_morphism {C} Z X Y : simpl never.
Hint Resolve initial_morphism_unique terminal_morphism_unique : morphism_unique.
Hint Rewrite @zero_morphism_left @zero_morphism_right : zero_morphism.

(** The next file in the library will be [ZeroMorphismLemmas.v] which contains
    transport lemmas and additional properties of morphisms in categories with
    zero objects. *)