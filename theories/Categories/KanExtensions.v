(** * Kan Extensions *)
(** ** Definitions *)
Require HoTT.Categories.KanExtensions.Core.
(** ** Kan Extensions assemble into functors *)
Require HoTT.Categories.KanExtensions.Functors.

Include KanExtensions.Core.
Include KanExtensions.Functors.
