(** Since there are only notations in [Category.Notations], we can just export those. *)
Require Export Category.Notations.

Require Category.Core.
Require Category.Dual.
Require Category.Morphisms.
Require Category.Objects.
Require Category.Prod.
Require Category.Strict.
Require Category.Sum.
Require Category.Univalent.

Include Category.Core.
Include Category.Dual.
Include Category.Morphisms.
Include Category.Objects.
Include Category.Prod.
Include Category.Strict.
Include Category.Sum.
Include Category.Univalent.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
