(** * Categories *)
(** We collect here all of the files about categories. *)
(** Since there are only notations in [Category.Notations], we can just export those. *)
Require Export Category.Notations.

(** ** Definition of precategories *)
Require Category.Core.
(** ** Opposite precategories *)
Require Category.Dual.
(** ** Morphisms in precategories *)
Require Category.Morphisms.
(** ** Universal objects *)
Require Category.Objects.
(** ** Product precategories *)
Require Category.Prod.
(** ** ∑-precategories *)
Require Category.Sigma.Sigma.
(** ** Strict categories *)
Require Category.Strict.
(** ** Coproduct precategories *)
Require Category.Sum.
(** ** Categories (univalent or saturated) *)
Require Category.Univalent.

Include Category.Core.
Include Category.Dual.
Include Category.Morphisms.
Include Category.Objects.
Include Category.Prod.
(** We use the [Sigma] folder only to allow us to split up the various files and group conceptually similar lemmas, but not for namespacing.  So we include the main file in it. *)
Include Category.Sigma.Sigma.
Include Category.Strict.
Include Category.Sum.
Include Category.Univalent.
(** We don't want to make utf-8 notations the default, so we don't export them. *)

(** ** Subcategories *)
(** For the subfolders, we need to re-create the module structure *)
Module Subcategory.
  Require Category.Subcategory.Subcategory.
  Include Category.Subcategory.Subcategory.
End Subcategory.
