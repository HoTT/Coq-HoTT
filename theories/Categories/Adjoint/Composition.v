(** * Adjunction composition *)
(** ** Definition *)
Require Adjoint.Composition.Core.
(** ** Associativity *)
Require Adjoint.Composition.AssociativityLaw.
(** * Left and right identity laws *)
Require Adjoint.Composition.IdentityLaws.

Include Adjoint.Composition.Core.
Include Adjoint.Composition.AssociativityLaw.
Include Adjoint.Composition.IdentityLaws.

Module Export AdjointCompositionNotations.
  Include AdjointCompositionCoreNotations.
End AdjointCompositionNotations.
