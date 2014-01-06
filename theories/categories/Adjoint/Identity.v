Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity NaturalTransformation.Identity.
Require Import Adjoint.UnitCounit Adjoint.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section identity.
  (** There is an identity adjunction.  It does the obvious thing. *)

  Definition identity C : @Adjunction C C 1 1
    := @Build_AdjunctionUnitCounit
         C C 1 1
         1
         1
         (fun _ => identity_identity _ _)
         (fun _ => identity_identity _ _).
End identity.

Module Export AdjointIdentityNotations.
  Notation "1" := (identity _) : adjunction_scope.
End AdjointIdentityNotations.
