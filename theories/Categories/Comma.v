(** * Comma Categories *)
(** Since there are only notations in [Comma.Notations], we can just export those. *)
Local Set Warnings Append "-notation-overridden".
Require Export HoTT.Categories.Comma.Notations.

(** ** Definitions *)
Require HoTT.Categories.Comma.Core.
(** ** Duals *)
Require HoTT.Categories.Comma.Dual.
(** ** Projection functors *)
Require HoTT.Categories.Comma.Projection.
Require HoTT.Categories.Comma.InducedFunctors.
(** ** Functoriality *)
Require HoTT.Categories.Comma.ProjectionFunctors.
Require HoTT.Categories.Comma.Functorial.

Include Comma.Core.
Include Comma.Dual.
Include Comma.Projection.
Include Comma.InducedFunctors.
Include Comma.ProjectionFunctors.
Include Comma.Functorial.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
