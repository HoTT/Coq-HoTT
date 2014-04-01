Require SetCategory.Core.
Require SetCategory.Morphisms.

Include SetCategory.Core.
Include SetCategory.Morphisms.

(** We recreate the subdirectory structure by making a module for each subdirectory. *)
Module Functors.
  Require SetCategory.Functors.Functors.
  Include SetCategory.Functors.Functors.
End Functors.
