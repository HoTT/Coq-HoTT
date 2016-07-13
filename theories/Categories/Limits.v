(** * Limits and Colimits *)
(** ** Definitions *)
Require Limits.Core.
(** ** (co)limits assemble into functors *)
(** *** which are adjoints to Δ *)
Require Limits.Functors.

Include Limits.Core.
Include Limits.Functors.
