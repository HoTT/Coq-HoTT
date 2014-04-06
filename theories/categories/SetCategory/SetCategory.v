(** * Category of sets *)
(** ** Definitoins of [set_cat] and [prop_cat] *)
Require SetCategory.Core.
(** ** Morphisms in the category of sets *)
Require SetCategory.Morphisms.

Include SetCategory.Core.
Include SetCategory.Morphisms.

(** ** Functors to/from the category of sets *)
(** We recreate the subdirectory structure by making a module for each subdirectory. *)
Module Functors.
  Require SetCategory.Functors.Functors.
  Include SetCategory.Functors.Functors.
End Functors.
