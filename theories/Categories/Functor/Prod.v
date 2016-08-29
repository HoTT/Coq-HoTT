(** * Functors involving product categories, and their properties *)
(** ** Definitions of various functors *)
Require Functor.Prod.Core.
(** ** Universal property *)
Require Functor.Prod.Universal.
(** ** Functoriality *)
Require Functor.Prod.Functorial.

Include Functor.Prod.Core.
Include Functor.Prod.Universal.
Include Functor.Prod.Functorial.

Module Export FunctorProdNotations.
  Include Functor.Prod.Core.FunctorProdCoreNotations.
End FunctorProdNotations.
