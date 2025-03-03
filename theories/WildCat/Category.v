Require Import Basics.Overture.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat.

Record Category := {
    category_carrier :> Type;
    isgraph_category_carrier :: IsGraph category_carrier;
    is01cat_category_carrier :: Is01Cat category_carrier;
    is2graph_category_carrier :: Is2Graph category_carrier;
    is1cat_category_carrier :: Is1Cat category_carrier (* This can be seen as the "mixin" in the sense of packed classes. *)
  }.

Instance isgraph_Cat : IsGraph Category := { Hom A B := Fun11 A B }.

Instance Is2GraphCategory : Is2Graph Category := fun (A B : Category) => {|
    Hom (F G : Fun11 A B) := NatTrans F G
|}.

Instance is3graph_Cat : Is3Graph Category := fun (A B : Category) => _.
