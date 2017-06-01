(** * Notations for functors *)
Require Import Basics.Notations.
Require Functor.Composition.
Require Functor.Core.
Require Functor.Dual.
Require Functor.Identity.
Require Functor.Prod.
Require Functor.Sum.

Include Functor.Composition.FunctorCompositionNotations.
Include Functor.Core.FunctorCoreNotations.
Include Functor.Dual.FunctorDualNotations.
Include Functor.Identity.FunctorIdentityNotations.
Include Functor.Prod.FunctorProdNotations.
Include Functor.Sum.FunctorSumNotations.
