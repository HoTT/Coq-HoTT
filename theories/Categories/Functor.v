(** * Functors *)
(** Since there are only notations in [Functor.Notations], we can just export those. *)
Require Export HoTT.Categories.Functor.Notations.

(** ** Definition *)
Require HoTT.Categories.Functor.Core.
(** ** Composition *)
Require HoTT.Categories.Functor.Composition.Core.
(** ** Duals *)
Require HoTT.Categories.Functor.Dual.
(** ** Identity *)
Require HoTT.Categories.Functor.Identity.
(** ** Classification of path space *)
Require HoTT.Categories.Functor.Paths.
(** ** Product functors *)
Require HoTT.Categories.Functor.Prod.Core.
(** ** Coproduct functors *)
Require HoTT.Categories.Functor.Sum.
(** ** Full, Faithful, Fully Faithful *)
Require HoTT.Categories.Functor.Attributes.
(** ** Pointwise functors (functoriality of functor category construction) *)
Require HoTT.Categories.Functor.Pointwise.Core.

Include Functor.Composition.Core.
Include Functor.Core.
Include Functor.Dual.
Include Functor.Identity.
Include Functor.Paths.
Include Functor.Prod.Core.
Include Functor.Sum.
Include Functor.Attributes.
Include Functor.Pointwise.Core.

(** We want to have the following as subdirectories/modules, not at top level.  Unfortunately, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
Require HoTT.Categories.Functor.Pointwise.

(** We don't want to make utf-8 notations the default, so we don't export them. *)
