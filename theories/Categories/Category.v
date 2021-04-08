(** * Categories *)
(** We collect here all of the files about categories. *)
(** Since there are only notations in [Category.Notations], we can just export those. *)
Require Export HoTT.Categories.Category.Notations.

(** ** Definition of precategories *)
Require HoTT.Categories.Category.Core.
(** ** Opposite precategories *)
Require HoTT.Categories.Category.Dual.
(** ** Morphisms in precategories *)
Require HoTT.Categories.Category.Morphisms.
(** ** Classification of path space *)
Require HoTT.Categories.Category.Paths.
(** ** Universal objects *)
Require HoTT.Categories.Category.Objects.
(** ** Product precategories *)
Require HoTT.Categories.Category.Prod.
(** ** Dependent product precategories *)
Require HoTT.Categories.Category.Pi.
(** ** ∑-precategories *)
Require HoTT.Categories.Category.Sigma.
(** ** Strict categories *)
Require HoTT.Categories.Category.Strict.
(** ** Coproduct precategories *)
Require HoTT.Categories.Category.Sum.
(** ** Categories (univalent or saturated) *)
Require HoTT.Categories.Category.Univalent.

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
Require HoTT.Categories.Category.Subcategory.
