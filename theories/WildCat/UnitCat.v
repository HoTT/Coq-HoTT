Require Import Basics.
Require Import WildCat.Core.

(** Unit category *)

Global Instance is01cat_unit : Is01Cat Unit.
Proof.
  srapply Build_Is01Cat.
  1: intros; exact Unit.
  all: intros; exact tt.
Defined.

Global Instance is0gpd_unit : Is0Gpd Unit.
Proof.
  constructor; intros; exact tt.
Defined.

Global Instance is1cat_unit : Is1Cat Unit.
Proof.
  econstructor.
  1,2:econstructor.
  all:intros; exact tt.
Defined.
