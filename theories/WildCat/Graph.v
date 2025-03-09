Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat.

(** * Category of graphs *)

(** ** Definition *)

(** A graph is a [Type] together with a relation [$->]. *)
Record Graph := {
  graph_carrier :> Type;
  isgraph_graph_carrier :: IsGraph graph_carrier
}.

(** ** Category of graphs *)

(** Morphisms of graphs are 0-coherent 1-functors, i.e., maps between the underlying types of the graphs together with an [fmap] functorial map taking arrows to appropriate arrows. This is known as a graph homomorphism. *)
Instance isgraph_graph : IsGraph Graph
  := { Hom A B := Fun01 A B }.

  (** A 2-cell between graph homomorphisms $[F G : A $-> B] is a wild [Transformation], i.e., a family of 1-cells [forall x, F x $-> G x] subject to no coherence conditions. When [A] and [B] have more structure (e.g., they are 1-categories or bicategories) a stronger notion of 2-cell is appropriate, such as a (possibly lax or oplax) transformation.*)
Instance is2graph_graph : Is2Graph Graph
  := fun A B => {| Hom F G := Transformation (fun01_F F) (fun01_F G) |}.

(** We have identity graph homomorphisms together with compositions of graph homomorphisms. *)
Instance is01cat_graph : Is01Cat Graph := {
  Id A := fun01_id;
  cat_comp A B C G F := fun01_compose G F
}.
