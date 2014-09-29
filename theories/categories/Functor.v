(** * Functors *)
(** Since there are only notations in [Functor.Notations], we can just export those. *)
Require Export Functor.Notations.

(** ** Definition *)
Require Functor.Core.
(** ** Composition *)
Require Functor.Composition.Core.
(** ** Duals *)
Require Functor.Dual.
(** ** Identity *)
Require Functor.Identity.
(** ** Classification of path space *)
Require Functor.Paths.
(** ** Product functors *)
Require Functor.Prod.Core.
(** ** Coproduct functors *)
Require Functor.Sum.
(** ** Full, Faithful, Fully Faithful *)
Require Functor.Attributes.
(** ** Pointwise functors (functoriality of functor category construction) *)
Require Functor.Pointwise.Core.

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
Require Functor.Pointwise.

(** We don't want to make utf-8 notations the default, so we don't export them. *)
