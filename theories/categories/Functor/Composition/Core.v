Require Import Category.Core Functor.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section composition.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  (** We usually don't want to see the proofs of composition in functors, because the proofs are hProps, and so we don't care about them.  But occasionally, we want to be able to reduce the proofs.  Having the proofs transparent allows the composition of the identity functor with itself to be judgementally the identity.  Since the only way to hide something from within a proof is [abstract], and that makes the definitions opaque, we need to define the laws separately.  We use [Opaque] to make them transparent to the unification engine, but opaque to simplification. *)

  Local Notation c_object_of c := (G (F c)) (only parsing).
  Local Notation c_morphism_of m := (morphism_of G (morphism_of F m)) (only parsing).
  (** We use [rewrite <-] because the resulting [match]es look better. *)
  Let compose_composition_of' s d d'
      (m1 : morphism C s d) (m2 : morphism C d d')
  : c_morphism_of (m2 o m1) = c_morphism_of m2 o c_morphism_of m1.
  Proof.
    rewrite <- !composition_of.
    reflexivity.
  Defined.
  Definition compose_composition_of s d d' m1 m2
    := Eval cbv beta iota zeta delta
            [compose_composition_of' internal_paths_rew] in
        @compose_composition_of' s d d' m1 m2.

  Let compose_identity_of' x
  : c_morphism_of (identity x) = identity (c_object_of x).
  Proof.
    rewrite <- !identity_of.
    reflexivity.
  Defined.
  Definition compose_identity_of x
    := Eval cbv beta iota zeta delta
            [compose_identity_of' internal_paths_rew] in
        @compose_identity_of' x.

  Global Arguments compose_composition_of / .
  Global Arguments compose_identity_of / .
  Global Opaque compose_composition_of compose_identity_of.

  Definition compose : Functor C E
    := Build_Functor
         C E
         (fun c => G (F c))
         (fun _ _ m => morphism_of G (morphism_of F m))
         compose_composition_of
         compose_identity_of.
End composition.

Global Arguments compose_composition_of / .
Global Arguments compose_identity_of / .

Module Export FunctorCompositionCoreNotations.
  Infix "o" := compose : functor_scope.
End FunctorCompositionCoreNotations.
