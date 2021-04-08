(** * Notations for functors *)
Require Import HoTT.Basics.Notations.
Require HoTT.Categories.Functor.Composition.
Require HoTT.Categories.Functor.Core.
Require HoTT.Categories.Functor.Dual.
Require HoTT.Categories.Functor.Identity.
Require HoTT.Categories.Functor.Prod.
Require HoTT.Categories.Functor.Sum.

Include Functor.Composition.FunctorCompositionNotations.
Include Functor.Core.FunctorCoreNotations.
Include Functor.Dual.FunctorDualNotations.
Include Functor.Identity.FunctorIdentityNotations.
Include Functor.Prod.FunctorProdNotations.
Include Functor.Sum.FunctorSumNotations.
