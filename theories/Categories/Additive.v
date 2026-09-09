(** * Additive categories and needed material *)
(** ** Zero objects in a category *)
Require Additive.ZeroObjects.
(** ** Biproducts in a category *)
Require Additive.Biproducts.
(** ** Semi-additive categories *)
Require Additive.SemiAdditive.
(** ** Additive categories *)
Require Additive.Additive.

Include Additive.ZeroObjects.
Include Additive.Biproducts.
Include Additive.SemiAdditive.
Include Additive.Additive.
