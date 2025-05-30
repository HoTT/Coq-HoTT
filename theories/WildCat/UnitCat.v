Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.

(** Unit category *)

Instance isgraph_unit : IsGraph Unit.
Proof.
  apply Build_IsGraph.
  intros; exact Unit.
Defined.

Instance is01cat_unit : Is01Cat Unit.
Proof.
  srapply Build_Is01Cat.
  all: intros; exact tt.
Defined.

Instance is0gpd_unit : Is0Gpd Unit.
Proof.
  constructor; intros; exact tt.
Defined.

Instance is2graph_unit : Is2Graph Unit
  := fun f g => isgraph_unit.

Instance is1cat_unit : Is1Cat Unit.
Proof.
  econstructor.
  1,2:econstructor.
  all:intros; exact tt.
Defined.
