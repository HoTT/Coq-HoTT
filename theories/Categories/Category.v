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
(** ** Classification of path space *)
Require Category.Paths.
(** ** Universal objects *)
Require Category.Objects.
(** ** Product precategories *)
Require Category.Prod.
(** ** Dependent product precategories *)
Require Category.Pi.
(** ** ∑-precategories *)
Require Category.Sigma.
(** ** Strict categories *)
Require Category.Strict.
(** ** Coproduct precategories *)
Require Category.Sum.
(** ** Categories (univalent or saturated) *)
Require Category.Univalent.

Local Set Warnings Append "-notation-overridden".
Include Category.Core.
Include Category.Dual.
Include Category.Morphisms.
Include Category.Paths.
Include Category.Objects.
Include Category.Prod.
Include Category.Pi.
(** We use the [Sigma] folder only to allow us to split up the various files and group conceptually similar lemmas, but not for namespacing.  So we include the main file in it. *)
Include Category.Sigma.
Include Category.Strict.
Include Category.Sum.
Include Category.Univalent.
(** We don't want to make utf-8 notations the default, so we don't export them. *)

(** ** Subcategories *)
(** For the subfolders, we need to re-create the module structure.  Alas, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
Require Category.Subcategory.
