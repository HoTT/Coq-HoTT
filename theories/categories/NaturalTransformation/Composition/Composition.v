(** * Composition of natural transformations *)
(** ** Composition *)
Require NaturalTransformation.Composition.Core.
(** ** Functoriality *)
Require NaturalTransformation.Composition.Functorial.
(** ** Laws about composition *)
Require NaturalTransformation.Composition.Laws.

Include NaturalTransformation.Composition.Core.
Include NaturalTransformation.Composition.Functorial.
Include NaturalTransformation.Composition.Laws.

Module Export NaturalTransformationCompositionNotations.
  Include NaturalTransformation.Composition.Core.NaturalTransformationCompositionCoreNotations.
End NaturalTransformationCompositionNotations.
