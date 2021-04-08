(** * Pseudofunctors *)
(** ** Definition *)
Require HoTT.Categories.Pseudofunctor.Core.
(** ** Helper lemmas for rewriting *)
Require HoTT.Categories.Pseudofunctor.RewriteLaws.
(** ** Construction from a functor to cat *)
Require HoTT.Categories.Pseudofunctor.FromFunctor.
(** ** Identity pseudofunctor *)
Require HoTT.Categories.Pseudofunctor.Identity.

Include Pseudofunctor.Core.
Include Pseudofunctor.RewriteLaws.
Include Pseudofunctor.FromFunctor.
Include Pseudofunctor.Identity.
