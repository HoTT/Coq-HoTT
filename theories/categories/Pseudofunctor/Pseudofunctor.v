(** * Pseudofunctors *)
(** ** Definition *)
Require Pseudofunctor.Core.
(** ** Helper lemmas for rewriting *)
Require Pseudofunctor.RewriteLaws.
(** ** Construction from a functor to cat *)
Require Pseudofunctor.FromFunctor.
(** ** Identity pseudofunctor *)
Require Pseudofunctor.Identity.

Include Pseudofunctor.Core.
Include Pseudofunctor.RewriteLaws.
Include Pseudofunctor.FromFunctor.
Include Pseudofunctor.Identity.
