(** * Comma Categories *)
(** Since there are only notations in [Comma.Notations], we can just export those. *)
Local Set Warnings Append "-notation-overridden".
Require Export Comma.Notations.

(** ** Definitions *)
Require Comma.Core.
(** ** Duals *)
Require Comma.Dual.
(** ** Projection functors *)
Require Comma.Projection.
Require Comma.InducedFunctors.
(** ** Functoriality *)
Require Comma.ProjectionFunctors.
Require Comma.Functorial.

Include Comma.Core.
Include Comma.Dual.
Include Comma.Projection.
Include Comma.InducedFunctors.
Include Comma.ProjectionFunctors.
Include Comma.Functorial.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
