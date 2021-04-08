(** * Composition of natural transformations *)
(** ** Composition *)
Require HoTT.Categories.NaturalTransformation.Composition.Core.
(** ** Functoriality *)
Require HoTT.Categories.NaturalTransformation.Composition.Functorial.
(** ** Laws about composition *)
Require HoTT.Categories.NaturalTransformation.Composition.Laws.

Include NaturalTransformation.Composition.Core.
Include NaturalTransformation.Composition.Functorial.
Include NaturalTransformation.Composition.Laws.

Module Export NaturalTransformationCompositionNotations.
  Include NaturalTransformation.Composition.Core.NaturalTransformationCompositionCoreNotations.
End NaturalTransformationCompositionNotations.
