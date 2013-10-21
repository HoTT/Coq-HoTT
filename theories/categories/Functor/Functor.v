(** Since there are only notations in [Functor.Notations], we can just export those. *)
Require Export Functor.Notations.

Require Functor.CompositionLaws.
Require Functor.Composition.
Require Functor.Core.
Require Functor.Dual.
Require Functor.Identity.
Require Functor.Paths.
Require Functor.Prod.
Require Functor.Sum.

Include Functor.CompositionLaws.
Include Functor.Composition.
Include Functor.Core.
Include Functor.Dual.
Include Functor.Identity.
Include Functor.Paths.
Include Functor.Prod.
Include Functor.Sum.
(** We don't want to make utf-8 notations the default, so we don't export them. *)

(** Since [Prod] is a separate sub-directory, we need to re-create the module structure *)
Module Prod.
  Require Functor.Prod.Prod.
  Include Functor.Prod.Prod.
End Prod.
