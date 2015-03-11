(** * Grothendieck Construction of a functor to Set *)
(** We want to have the following as subdirectories/modules, not at top level.  Unfortunately, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
(** ** construction *)
Require Grothendieck.ToSet.Core.

(** ** classification of morphisms *)
Require Grothendieck.ToSet.Morphisms.

(** ** preservation of saturation *)
Require Grothendieck.ToSet.Univalent.

Include Grothendieck.ToSet.Core.
