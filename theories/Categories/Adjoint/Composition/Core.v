(** * Composition of adjunctions [F' ⊣ G' → F ⊣ G → (F' ∘ F) ⊣ (G ∘ G')] *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Functor.Composition.Core HoTT.Categories.NaturalTransformation.Composition.Core.
Require Import HoTT.Categories.Functor.Identity HoTT.Categories.NaturalTransformation.Identity.
Require HoTT.Categories.NaturalTransformation.Composition.Laws.
Require Import HoTT.Categories.Adjoint.UnitCounit HoTT.Categories.Adjoint.Core.
Require Import HoTT.Categories.Category.Morphisms.
Require Import HoTT.Tactics.
Require Import HoTT.Basics.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.

(** ** via the unit+counit+zig+zag definition *)
Section compose.
  Variables C D E : PreCategory.

  Variable F : Functor C D.
  Variable F' : Functor D E.
  Variable G : Functor D C.
  Variable G' : Functor E D.

  Variable A' : F' -| G'.
  Variable A : F -| G.

  Definition compose_unit
  : NaturalTransformation 1 ((G o G') o (F' o F)).
  Proof.
    pose (unit A) as eta.
    pose (unit A') as eta'.
    refine ((fun (T : NaturalTransformation _ _)
                 (U : NaturalTransformation _ _)
             => T o (G oL eta' oR F) o U o eta) _ _);
      NaturalTransformation.Composition.Laws.nt_solve_associator.
  Defined.

  Definition compose_counit
  : NaturalTransformation ((F' o F) o (G o G')) 1.
  Proof.
    pose (counit A) as eps.
    pose (counit A') as eps'.
    refine ((fun (T : NaturalTransformation _ _)
                 (U : NaturalTransformation _ _)
             => eps' o U o (F' oL eps oR G') o T) _ _);
      NaturalTransformation.Composition.Laws.nt_solve_associator.
  Defined.

  Definition compose : F' o F -| G o G'.
  Proof.
    exists compose_unit compose_counit;
    simpl;
    abstract (
        repeat
          match goal with
            | _ => intro
            | _ => reflexivity
            | _ => progress rewrite ?identity_of, ?left_identity, ?right_identity
            | _ => rewrite <- ?composition_of, unit_counit_equation_1
            | _ => rewrite <- ?composition_of, unit_counit_equation_2
            | [ A : _ -| _ |- _ = 1%morphism ]
              => (etransitivity; [ | apply (unit_counit_equation_1 A) ];
                  instantiate; try_associativity_quick f_ap)
            | [ A : _ -| _ |- _ = 1%morphism ]
              => (etransitivity; [ | apply (unit_counit_equation_2 A) ];
                  instantiate; try_associativity_quick f_ap)
            | _ => repeat (try_associativity_quick rewrite <- !composition_of);
                  progress repeat apply ap;
                  rewrite ?composition_of
            | [ |- context[components_of ?T] ]
              => (try_associativity_quick simpl rewrite <- (commutes T));
                try_associativity_quick (apply concat_right_identity
                                               || apply concat_left_identity)
            | [ |- context[components_of ?T] ]
              => (try_associativity_quick simpl rewrite (commutes T));
                try_associativity_quick (apply concat_right_identity
                                               || apply concat_left_identity)
          end
      ).
  Defined.
End compose.

Module Export AdjointCompositionCoreNotations.
  Infix "o" := compose : adjunction_scope.
End AdjointCompositionCoreNotations.
