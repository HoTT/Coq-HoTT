(** Since there are only notations in [FunctorCategory.Notations], we can just export those. *)
Require Export FunctorCategory.Notations.

Require FunctorCategory.Core.
Require FunctorCategory.Morphisms.
Require FunctorCategory.Functorial.
Require FunctorCategory.Dual.

Include FunctorCategory.Core.
Include FunctorCategory.Morphisms.
Include FunctorCategory.Functorial.
Include FunctorCategory.Dual.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
