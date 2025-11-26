Require Import Basics.Overture.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat.

(** * Category of categories *)

(** TODO: make into a bicategory; define equivalences *)

(** ** Definition *)

(** A category is a [Type] together with a proof that it is a 1-category. *)
Record Category := {
  category_carrier :> Type;
  isgraph_category_carrier :: IsGraph category_carrier;
  is01cat_category_carrier :: Is01Cat category_carrier;
  is2graph_category_carrier :: Is2Graph category_carrier;
  is1cat_category_carrier :: Is1Cat category_carrier
}.

(** Morphisms of categories are given by functors. *)
Instance isgraph_cat : IsGraph Category
  := { Hom A B := Fun11 A B }.

(** 2-morphisms of categories are given by natural transformations. *)
Instance is2graph_cat : Is2Graph Category
  := fun A B => _.

(** 3-morphisms of categories are given by "wild modifications" - the underlying data of a modification, subject to no coherence conditions. *)
Instance is3graph_cat : Is3Graph Category
  := fun A B => _.
