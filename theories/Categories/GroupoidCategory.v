(** * Groupoids *)
(** ** Definition *)
Require HoTT.Categories.GroupoidCategory.Core.
(** ** Morphisms in a groupoid *)
Require HoTT.Categories.GroupoidCategory.Morphisms.
(** ** Propositional self-duality *)
Require HoTT.Categories.GroupoidCategory.Dual.

Include GroupoidCategory.Core.
Include GroupoidCategory.Core.GroupoidCategoryInternals.
Include GroupoidCategory.Morphisms.
Include GroupoidCategory.Dual.
