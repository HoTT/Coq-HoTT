(** Since there are only notations in [Functor.Notations], we can just export those. *)
Require Export Functor.Notations.

Require Functor.CompositionLaws.
Require Functor.Composition.
Require Functor.Core.
Require Functor.Duals.
Require Functor.Identity.
Require Functor.Paths.
Require Functor.Sum.

Include Functor.CompositionLaws.
Include Functor.Composition.
Include Functor.Core.
Include Functor.Duals.
Include Functor.Identity.
Include Functor.Paths.
Include Functor.Sum.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
