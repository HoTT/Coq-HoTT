Require SetCategory.Core.

Include SetCategory.Core.

(** We recreate the subdirectory structure by making a module for each subdirectory. *)
Module Functors.
  Require SetCategory.Functors.Functors.
  Include SetCategory.Functors.Functors.
End Functors.
