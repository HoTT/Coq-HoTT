(** * Pseudofunctors *)
(** ** Definition *)
Require Pseudofunctor.Core.
(** ** Construction from a functor to cat *)
Require Pseudofunctor.FromFunctor.
(** ** Identity pseudofunctor *)
Require Pseudofunctor.Identity.

Include Pseudofunctor.Core.
Include Pseudofunctor.FromFunctor.
Include Pseudofunctor.Identity.
