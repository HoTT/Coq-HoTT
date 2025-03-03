Require Import Basics.Overture.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat.

Record Graph := {
    graph_carrier :> Type;
    isgraph_graph_carrier :: IsGraph graph_carrier
}.

Instance is0Graph_Graph : IsGraph Graph := {
  Hom A B := Fun01 A B
}.

Instance Is2GraphGraph : Is2Graph Graph :=
  fun A B => {| Hom F G := Transformation (fun01_F F) (fun01_F G)|}.

(** There is a (0,1)-category of graphs under composition. *)
Instance is01cat_Graph : Is01Cat Graph := {
    Id A := {| fun01_F := idmap; fun01_is0functor := _ |};
    cat_comp A B C G F :=
     {| fun01_F := compose G F ; fun01_is0functor := _ |}
}.