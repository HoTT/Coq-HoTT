(** * Groupoids *)
(** ** Definition *)
Require GroupoidCategory.Core.
(** ** Morphisms in a groupoid *)
Require GroupoidCategory.Morphisms.
(** ** Propositional self-duality *)
Require GroupoidCategory.Dual.

Include GroupoidCategory.Core.
Include GroupoidCategory.Core.GroupoidCategoryInternals.
Include GroupoidCategory.Morphisms.
Include GroupoidCategory.Dual.
