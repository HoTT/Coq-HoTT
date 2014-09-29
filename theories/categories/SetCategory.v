(** * Category of sets *)
(** ** Definitoins of [set_cat] and [prop_cat] *)
Require SetCategory.Core.
(** ** Morphisms in the category of sets *)
Require SetCategory.Morphisms.
(** If there were a [SetCategory.Functors.Core], we'd [Include] it here. *)

Include SetCategory.Core.
Include SetCategory.Morphisms.

(** ** Functors to/from the category of sets *)
(** Since [Functors] is a separate sub-directory, we need to re-create the module structure.  Alas, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
Require SetCategory.Functors.
