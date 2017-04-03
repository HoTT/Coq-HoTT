(** * Composition of functors *)
Require Import Category.Core Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section composition.
  Variables B C D E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  (** We usually don't want to see the proofs of composition in functors, because the proofs are hProps, and so we don't care about them.  But occasionally, we want to be able to reduce the proofs.  Having the proofs transparent allows the composition of the identity functor with itself to be judgementally the identity.  Since the only way to hide something from within a proof is [abstract], and that makes the definitions opaque, we need to define the laws separately. *)

  Local Notation c_object_of c := (G (F c)) (only parsing).
  Local Notation c_morphism_of m := (G _1 (F _1 m)) (only parsing).
  Definition compose_composition_of s d d'
      (m1 : morphism C s d) (m2 : morphism C d d')
  : c_morphism_of (m2 o m1) = c_morphism_of m2 o c_morphism_of m1
    := transport (@paths _ (c_morphism_of (m2 o m1)))
                 (composition_of G _ _ _ _ _)
                 (ap (fun m => G _1 m) (composition_of F _ _ _ m1 m2)).

  Definition compose_identity_of x
  : c_morphism_of (identity x) = identity (c_object_of x)
    := transport (@paths _ _)
                 (identity_of G _)
                 (ap (fun m => G _1 m) (identity_of F x)).

  Definition compose : Functor C E
    := Build_Functor
         C E
         (fun c => G (F c))
         (fun _ _ m => G _1 (F _1 m))
         compose_composition_of
         compose_identity_of.
End composition.

Global Arguments compose_composition_of / .
Global Arguments compose_identity_of / .

Module Export FunctorCompositionCoreNotations.
  Infix "o" := compose : functor_scope.
End FunctorCompositionCoreNotations.
