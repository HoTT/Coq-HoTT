(** * Wide subcategories *)
(** We reuse ∑-precategories; a wide subcategory has the same objects, and a ∑ type as its morphisms.  We make use of the fact that the extra component should be an hProp to not require as many proofs. *)
Require Import Category.Sigma.OnMorphisms.

Notation wide := sig_mor.
