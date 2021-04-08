(** * Adjunction composition *)
(** ** Definition *)
Require HoTT.Categories.Adjoint.Composition.Core.
(** ** Associativity *)
Require HoTT.Categories.Adjoint.Composition.AssociativityLaw.
(** * Left and right identity laws *)
Require HoTT.Categories.Adjoint.Composition.IdentityLaws.

Include Adjoint.Composition.Core.
Include Adjoint.Composition.AssociativityLaw.
Include Adjoint.Composition.IdentityLaws.

Module Export AdjointCompositionNotations.
  Include AdjointCompositionCoreNotations.
End AdjointCompositionNotations.
