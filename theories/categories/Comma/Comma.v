(** Since there are only notations in [Comma.Notations], we can just export those. *)
Require Export Comma.Notations.

Require Comma.Core.
Require Comma.Dual.
Require Comma.Projection.
Require Comma.InducedFunctors.
Require Comma.ProjectionFunctors.
Require Comma.Functorial.

Include Comma.Core.
Include Comma.Dual.
Include Comma.Projection.
Include Comma.InducedFunctors.
Include Comma.ProjectionFunctors.
Include Comma.Functorial.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
