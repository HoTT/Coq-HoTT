(** * Profunctors *)
Require Export Profunctor.Notations.

(** ** Definition *)
Require Profunctor.Core.
(** ** Identity Profunctor *)
Require Profunctor.Identity.
(** ** Representable Profunctors *)
Require Profunctor.Representable.

Include Profunctor.Core.
Include Profunctor.Representable.
Include Profunctor.Identity.
