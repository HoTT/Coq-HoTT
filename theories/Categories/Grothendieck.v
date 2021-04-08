(** * Grothendieck Construction *)
(** We want to have the following as subdirectories/modules, not at top level.  Unfortunately, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
(** ** of a functor to Set *)
Require HoTT.Categories.Grothendieck.ToSet.

(** ** of a pseudofunctor to Cat *)
Require HoTT.Categories.Grothendieck.PseudofunctorToCat.

(** ** of a functor to Cat *)
Require HoTT.Categories.Grothendieck.ToCat.
