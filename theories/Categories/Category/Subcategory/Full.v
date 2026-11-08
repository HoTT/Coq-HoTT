(** * Full Subcategories *)
(** We reuse the generalization given by ∑-precategories; a full subcategory has a sigma type as its objects. *)
Require Import Category.Sigma.OnObjects.

Abbreviation full := sig_obj.

Notation "{ x : A | P }" := (full A (fun x => P)) : category_scope.
