(** * Composition of functors *)
(** ** Definition of composition *)
Require Functor.Composition.Core.
(** ** Functoriality of composition *)
Require Functor.Composition.Functorial.
(** ** Laws about functor composition *)
Require Functor.Composition.Laws.

Include Functor.Composition.Core.
Include Functor.Composition.Functorial.
Include Functor.Composition.Laws.

Module Export FunctorCompositionNotations.
  Include Functor.Composition.Core.FunctorCompositionCoreNotations.
End FunctorCompositionNotations.
