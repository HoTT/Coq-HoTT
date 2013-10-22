(** Since there are only notations in [NaturalTransformation.Notations], we can just export those. *)
Require Export NaturalTransformation.Notations.

Require NaturalTransformation.CompositionLaws.
Require NaturalTransformation.Composition.
Require NaturalTransformation.Core.
Require NaturalTransformation.Duals.
Require NaturalTransformation.Identity.
Require NaturalTransformation.Paths.
Require NaturalTransformation.Sum.

Include NaturalTransformation.CompositionLaws.
Include NaturalTransformation.Composition.
Include NaturalTransformation.Core.
Include NaturalTransformation.Duals.
Include NaturalTransformation.Identity.
Include NaturalTransformation.Paths.
Include NaturalTransformation.Sum.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
