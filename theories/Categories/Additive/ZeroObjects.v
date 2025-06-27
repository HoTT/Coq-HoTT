(** * Zero objects in categories

    Zero objects (both initial and terminal) and zero morphisms, foundational
    concepts for additive and stable category theory.
*)

From HoTT Require Import Basics Types.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories Require Import InitialTerminalCategory.

(** * Zero objects
    
    A zero object in a category is an object that is both initial and terminal.
    Such objects play a fundamental role in additive and abelian categories,
    where they enable the definition of zero morphisms and kernels.
*)

Class ZeroObject (C : PreCategory) := {
  zero : object C;
  is_initial :: IsInitialObject C zero;
  is_terminal :: IsTerminalObject C zero
}.

Coercion zero : ZeroObject >-> object.

Arguments zero {C} z : rename.
Arguments is_initial {C} z : rename.
Arguments is_terminal {C} z : rename.

Instance initialobject_zeroobject {C : PreCategory} (Z : ZeroObject C)
  : InitialObject C
  := {| object_initial := zero Z; isinitial_object_initial := _ |}.

Instance terminalobject_zeroobject {C : PreCategory} (Z : ZeroObject C)
  : TerminalObject C
  := {| object_terminal := zero Z; isterminal_object_terminal := _ |}.

(** The zero morphism between any two objects is the unique morphism
    that factors through the zero object. *)

Definition zero_morphism {C : PreCategory} {Z : ZeroObject C} (X Y : object C)
  : morphism C X Y
  := morphism_from_initial Y o morphism_to_terminal X.

Arguments zero_morphism {C Z} X Y : simpl never.

(** * Basic properties of zero objects *)

(** ** Properties of zero morphisms *)

(** Any morphism that factors through a zero object is the zero morphism. *)
Lemma morphism_through_zero_is_zero {C : PreCategory} 
  {Z : ZeroObject C} {X Y : object C}
  (f : morphism C X Z)
  (g : morphism C Z Y)
  : (g o f)%morphism = zero_morphism X Y.
Proof.
  unfold zero_morphism.
  apply ap011.
  - rapply initial_morphism_unique.
  - rapply terminal_morphism_unique.
Qed.

(** ** Composition properties of zero morphisms *)

(** Composition with zero morphism on the right. *)
Lemma zero_morphism_right {C : PreCategory} {Z : ZeroObject C}
  {X Y W : object C}
  (g : morphism C Y W)
  : (g o zero_morphism X Y)%morphism = zero_morphism X W.
Proof.
  rewrite <- Category.Core.associativity.
  apply morphism_through_zero_is_zero.
Qed.

(** Composition with zero morphism on the left. *)
Lemma zero_morphism_left {C : PreCategory} {Z : ZeroObject C}
  {X Y W : object C}
  (f : morphism C X Y)
  : (zero_morphism Y W o f)%morphism = zero_morphism X W.
Proof.
  rewrite Category.Core.associativity.
  apply morphism_through_zero_is_zero.
Qed.

(** ** Export hints *)

Hint Rewrite @zero_morphism_left @zero_morphism_right : zero_morphism.
