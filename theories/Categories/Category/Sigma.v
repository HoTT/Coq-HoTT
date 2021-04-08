(** * ∑-precategories *)
(** These are a generalization of subcategories in the direction of the Grothendieck construction *)
Require HoTT.Categories.Category.Sigma.Core.
Require HoTT.Categories.Category.Sigma.OnMorphisms.
Require HoTT.Categories.Category.Sigma.OnObjects.
Require HoTT.Categories.Category.Sigma.Univalent.

Include Category.Sigma.Core.
Include Category.Sigma.OnMorphisms.
Include Category.Sigma.OnObjects.
Include Category.Sigma.Univalent.

Module CategorySigmaNotations.
  Include Category.Sigma.OnObjects.CategorySigmaOnObjectsNotations.
End CategorySigmaNotations.
