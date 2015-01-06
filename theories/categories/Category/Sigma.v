(** * ∑-precategories *)
(** These are a generalization of subcategories in the direction of the Grothendieck construction *)
Require Category.Sigma.Core.
Require Category.Sigma.OnMorphisms.
Require Category.Sigma.OnObjects.
Require Category.Sigma.Univalent.

Include Category.Sigma.Core.
Include Category.Sigma.OnMorphisms.
Include Category.Sigma.OnObjects.
Include Category.Sigma.Univalent.

Module CategorySigmaNotations.
  Include Category.Sigma.OnObjects.CategorySigmaOnObjectsNotations.
End CategorySigmaNotations.
