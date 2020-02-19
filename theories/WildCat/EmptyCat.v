Require Import Basics.
Require Import WildCat.Core.

(** Empty category *)

Global Instance isgraph_empty : IsGraph Empty.
Proof.
  by apply Build_IsGraph.
Defined.

Global Instance is01cat_empty : Is01Cat Empty.
Proof.
  srapply Build_Is01Cat; intros [].
Defined.

Global Instance is0gpd_empty : Is0Gpd Empty.
Proof.
  constructor; intros [].
Defined.

Global Instance is1cat_empty : Is1Cat Empty.
Proof.
  snrapply Build_Is1Cat; intros [].
Defined.
