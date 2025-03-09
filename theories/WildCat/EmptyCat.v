Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.

(** Empty category *)

Instance isgraph_empty : IsGraph Empty.
Proof.
  by apply Build_IsGraph.
Defined.

Instance is01cat_empty : Is01Cat Empty.
Proof.
  srapply Build_Is01Cat; intros [].
Defined.

Instance is0gpd_empty : Is0Gpd Empty.
Proof.
  constructor; intros [].
Defined.

Instance is2graph_empty : Is2Graph Empty.
Proof.
  intros f g.
  by apply Build_IsGraph.
Defined.

Instance is1cat_empty : Is1Cat Empty.
Proof.
  snapply Build_Is1Cat; intros [].
Defined.
