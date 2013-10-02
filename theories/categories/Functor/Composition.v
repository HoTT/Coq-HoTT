Require Export Category.Core Functor.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section functor_composition.
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
  Let functor_compose_composition_of' s d d'
      (m1 : morphism C s d) (m2 : morphism C d d')
  : c_morphism_of (m2 o m1) = c_morphism_of m2 o c_morphism_of m1.
  Proof.
    rewrite <- !composition_of.
    reflexivity.
  Defined.
  Definition functor_compose_composition_of s d d' m1 m2
    := Eval cbv beta iota zeta delta
            [functor_compose_composition_of' internal_paths_rew] in
        @functor_compose_composition_of' s d d' m1 m2.

  Let functor_compose_identity_of' x
  : c_morphism_of (identity x) = identity (c_object_of x).
  Proof.
    rewrite <- !identity_of.
    reflexivity.
  Defined.
  Definition functor_compose_identity_of x
    := Eval cbv beta iota zeta delta
            [functor_compose_identity_of' internal_paths_rew] in
        @functor_compose_identity_of' x.

  Global Arguments functor_compose_composition_of / .
  Global Arguments functor_compose_identity_of / .
  Global Opaque functor_compose_composition_of functor_compose_identity_of.

  Definition functor_compose : Functor C E
    := Build_Functor
         C E
         (fun c => G (F c))
         (fun _ _ m => morphism_of G (morphism_of F m))
         functor_compose_composition_of
         functor_compose_identity_of.
End functor_composition.

Infix "o" := functor_compose : functor_scope.

Global Arguments functor_compose_composition_of / .
Global Arguments functor_compose_identity_of / .
