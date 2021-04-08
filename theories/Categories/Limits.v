(** * Limits and Colimits *)
(** ** Definitions *)
Require HoTT.Categories.Limits.Core.
(** ** (co)limits assemble into functors *)
(** *** which are adjoints to Δ *)
Require HoTT.Categories.Limits.Functors.

Include Limits.Core.
Include Limits.Functors.
