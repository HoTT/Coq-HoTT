(** * Pseudofunctors *)
(** ** Definition *)
Require Pseudofunctor.Core.
(** ** Construction from a functor to cat *)
Require Pseudofunctor.FromFunctor.

Include Pseudofunctor.Core.
Include Pseudofunctor.FromFunctor.
