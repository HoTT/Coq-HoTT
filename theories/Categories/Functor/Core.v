(** * Definition of a functor *)
Require Import Category.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Declare Scope functor_scope.
Delimit Scope functor_scope with functor.

Local Open Scope morphism_scope.

Section Functor.
  Variables C D : PreCategory.

  (** Quoting from the lecture notes for MIT's 18.705, Commutative Algebra:

      A map of categories is known as a functor. Namely, given
      categories [C] and [C'], a (covariant) functor [F : C -> C'] is
      a rule that assigns to each object [A] of [C] an object [F A] of
      [C'] and to each map [m : A -> B] of [C] a map [F m : F A -> F
      B] of [C'] preserving composition and identity; that is,

     (1) [F (m' ∘ m) = (F m') ∘ (F m)] for maps [m : A -> B] and [m' :
         B -> C] of [C], and

     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A]
         is the identity morphism of [A]. **)

  Record Functor :=
    {
      object_of :> C -> D;
      morphism_of : forall s d, morphism C s d
                                -> morphism D (object_of s) (object_of d);
      composition_of : forall s d d'
                              (m1 : morphism C s d) (m2: morphism C d d'),
                         morphism_of _ _ (m2 o m1)
                         = (morphism_of _ _ m2) o (morphism_of _ _ m1);
      identity_of : forall x, morphism_of _ _ (identity x)
                              = identity (object_of x)
    }.
End Functor.

Bind Scope functor_scope with Functor.

Create HintDb functor discriminated.

Arguments Functor C D : assert.
Arguments object_of {C%category D%category} F%functor c%object : rename, simpl nomatch.
Arguments morphism_of [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Arguments composition_of [C D] F _ _ _ _ _ : rename.
Arguments identity_of [C D] F _ : rename.

Module Export FunctorCoreNotations.
  (** Perhaps we should consider making this more global? *)
  Local Notation "C --> D" := (Functor C D) : type_scope.
  Notation "F '_0' x" := (object_of F x) : object_scope.
  Notation "F '_1' m" := (morphism_of F m) : morphism_scope.
End FunctorCoreNotations.

Hint Resolve @composition_of @identity_of : category functor.
Hint Rewrite @identity_of : category.
Hint Rewrite @identity_of : functor.
