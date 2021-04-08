(** * Full Subcategories *)
(** We reuse the generalizion given by ∑-precategories; a full subcategory has a sigma type as its objects. *)
Require Import HoTT.Categories.Category.Sigma.OnObjects.

Notation full := sig_obj.

Notation "{ x : A | P }" := (full A (fun x => P)) : category_scope.
