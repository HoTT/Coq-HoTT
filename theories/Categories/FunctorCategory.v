(** * Functor category *)
(** Since there are only notations in [FunctorCategory.Notations], we can just export those. *)
Require Export FunctorCategory.Notations.

(** ** Definition *)
Require FunctorCategory.Core.
(** ** Morphisms in a functor category *)
Require FunctorCategory.Morphisms.
(** ** Functoriality of [(_ → _)] *)
Require FunctorCategory.Functorial.
(** ** Opposite functor [(C → D) → (Cᵒᵖ → Dᵒᵖ)ᵒᵖ] *)
Require FunctorCategory.Dual.

Include FunctorCategory.Core.
Include FunctorCategory.Morphisms.
Include FunctorCategory.Functorial.
Include FunctorCategory.Dual.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
