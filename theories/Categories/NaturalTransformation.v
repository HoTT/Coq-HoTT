(** * Natural Transformations *)
(** Since there are only notations in [NaturalTransformation.Notations], we can just export those. *)
Require Export HoTT.Categories.NaturalTransformation.Notations.

(** ** Definition of natural transformation *)
Require HoTT.Categories.NaturalTransformation.Core.
(** ** Composition of natural transformations *)
Require HoTT.Categories.NaturalTransformation.Composition.Core.
(** ** Dual natural transformations *)
Require HoTT.Categories.NaturalTransformation.Dual.
(** ** Identity natural transformation *)
Require HoTT.Categories.NaturalTransformation.Identity.
(** ** Natural isomorphisms *)
Require HoTT.Categories.NaturalTransformation.Isomorphisms.
(** ** Path space of natural transformation type *)
Require HoTT.Categories.NaturalTransformation.Paths.
(** ** Pointwise natural transformations *)
Require HoTT.Categories.NaturalTransformation.Pointwise.
(** ** Sums of natural transformations *)
Require HoTT.Categories.NaturalTransformation.Sum.
(** ** Products of natural transformations *)
Require HoTT.Categories.NaturalTransformation.Prod.

Include NaturalTransformation.Core.
Include NaturalTransformation.Composition.Core.
Include NaturalTransformation.Dual.
Include NaturalTransformation.Identity.
Include NaturalTransformation.Isomorphisms.
Include NaturalTransformation.Paths.
Include NaturalTransformation.Pointwise.
Include NaturalTransformation.Sum.
Include NaturalTransformation.Prod.
(** We don't want to make utf-8 notations the default, so we don't export them. *)

(** Since [Composition] is a separate sub-directory, we need to re-create the module structure *)
(** We want to have the following as subdirectories/modules, not at top level.  Unfortunately, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
Require HoTT.Categories.NaturalTransformation.Composition.
