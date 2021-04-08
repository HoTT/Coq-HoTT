(** * Identity adjunction [1 ⊣ 1] *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Functor.Identity HoTT.Categories.NaturalTransformation.Identity.
Require Import HoTT.Categories.Adjoint.UnitCounit HoTT.Categories.Adjoint.Core.

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
