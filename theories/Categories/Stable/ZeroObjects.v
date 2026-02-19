(** * Zero objects in categories

    Zero objects (both initial and terminal) and zero morphisms, foundational
    concepts for additive and stable category theory.
*)

From HoTT Require Import Basics Types.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories Require Import InitialTerminalCategory.
From HoTT.Categories.Category Require Import Objects.

(** * Zero objects
    
    A zero object in a category is an object that is both initial and terminal.
    Such objects play a fundamental role in additive and abelian categories,
    where they enable the definition of zero morphisms and kernels.
*)

Record ZeroObject (C : PreCategory) := {
  zero : object C;
  is_initial :: IsInitialObject C zero;
  is_terminal :: IsTerminalObject C zero
}.

Arguments zero {C} z : rename.
Arguments is_initial {C} z : rename.
Arguments is_terminal {C} z : rename.

(** The zero morphism between any two objects is the unique morphism
    that factors through the zero object. *)

Definition zero_morphism {C : PreCategory} (Z : ZeroObject C) (X Y : object C)
  : morphism C X Y
  := (@center _ (@is_initial _ Z Y) o @center _ (@is_terminal _ Z X))%morphism.

(** * Basic properties of zero objects *)

(** ** Uniqueness of initial and terminal morphisms *)

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

(** ** Properties of zero morphisms *)

(** Any morphism that factors through a zero object is the zero morphism. *)
Lemma morphism_through_zero_is_zero {C : PreCategory} 
  (Z : ZeroObject C) (X Y : object C)
  (f : morphism C X (zero Z))
  (g : morphism C (zero Z) Y)
  : (g o f)%morphism = zero_morphism Z X Y.
Proof.
  unfold zero_morphism.
  apply ap011.
  - rapply initial_morphism_unique.
  - rapply terminal_morphism_unique.
Qed.

(** ** Special properties of zero endomorphisms *)

(** The morphism from zero to itself is the identity. *)
Lemma zero_to_zero_is_id {C : PreCategory} (Z : ZeroObject C)
  : @center _ (is_initial Z (zero Z)) = 1%morphism.
Proof.
  rapply contr.
Qed.

(** The terminal morphism from zero to itself is the identity. *)
Lemma terminal_zero_to_zero_is_id {C : PreCategory} (Z : ZeroObject C)
  : @center _ (is_terminal Z (zero Z)) = 
    (1%morphism : morphism C (zero Z) (zero Z)).
Proof.
  rapply terminal_morphism_unique.
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
    rapply contr.
  }
  rewrite H.
  apply Category.Core.right_identity.
Qed.

(** ** Composition properties of zero morphisms *)

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
    rapply contr.
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
    rapply contr.
  }
  rewrite Category.Core.associativity.
  rewrite H.
  reflexivity.
Qed.

(** ** Export hints *)

Arguments zero_morphism {C} Z X Y : simpl never.
Hint Resolve initial_morphism_unique terminal_morphism_unique : morphism_unique.
Hint Rewrite @zero_morphism_left @zero_morphism_right : zero_morphism.
