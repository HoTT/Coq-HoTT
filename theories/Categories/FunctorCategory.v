(** * Functor category *)
(** Since there are only notations in [FunctorCategory.Notations], we can just export those. *)
Require Export HoTT.Categories.FunctorCategory.Notations.

(** ** Definition *)
Require HoTT.Categories.FunctorCategory.Core.
(** ** Morphisms in a functor category *)
Require HoTT.Categories.FunctorCategory.Morphisms.
(** ** Functoriality of [(_ → _)] *)
Require HoTT.Categories.FunctorCategory.Functorial.
(** ** Opposite functor [(C → D) → (Cᵒᵖ → Dᵒᵖ)ᵒᵖ] *)
Require HoTT.Categories.FunctorCategory.Dual.

Include FunctorCategory.Core.
Include FunctorCategory.Morphisms.
Include FunctorCategory.Functorial.
Include FunctorCategory.Dual.
(** We don't want to make utf-8 notations the default, so we don't export them. *)
