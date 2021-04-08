(* -*- mode: coq; mode: visual-line -*-  *)

Require Import HoTT.Basics.
Require Import HoTT.WildCat.Core.

(** ** Sum categories *)

Global Instance isgraph_sum A B `{IsGraph A} `{IsGraph B}
  : IsGraph (A + B).
Proof.
  econstructor.
  intros [a1 | b1] [a2 | b2].
  + exact (a1 $-> a2).
  + exact Empty.
  + exact Empty.
  + exact (b1 $-> b2).
Defined.

Global Instance is01cat_sum A B `{ Is01Cat A } `{ Is01Cat B}
  : Is01Cat (A + B).
Proof.
  srapply Build_Is01Cat.
  - intros [a | b]; cbn; apply Id.
  - intros [a | b] [a1 | b1] [a2 | b2];
    try contradiction; cbn; apply cat_comp.
Defined.

(* Note: [try contradiction] deals with empty cases. *)
Global Instance is1cat_sum A B `{ Is1Cat A } `{ Is1Cat B}
  : Is1Cat (A + B).
Proof.
  srapply Build_Is1Cat.
  - intros x y; apply Build_IsGraph.
    destruct x as [a1 | b1], y as [a2 | b2];
    try contradiction; cbn; apply Hom.
  - intros x y.
    srapply Build_Is01Cat;
    destruct x as [a1 | b1], y as [a2 | b2];
    try contradiction; cbn;
    (apply Id || intros a b c; apply cat_comp).
  - intros x y; srapply Build_Is0Gpd.
    destruct x as [a1 | b1], y as [a2 | b2];
    try contradiction; cbn; intros f g; apply gpd_rev.
  - intros x y z h; srapply Build_Is0Functor.
    intros f g p.
    destruct x as [a1 | b1], y as [a2 | b2], z as [a3 | b3];
    try contradiction; cbn in *; change (f $== g) in p; exact (h $@L p).
  - intros x y z h; srapply Build_Is0Functor.
    intros f g p.
    destruct x as [a1 | b1], y as [a2 | b2], z as [a3 | b3];
    try contradiction; cbn in *; change (f $== g) in p; exact (p $@R h).
  - intros [a1 | b1] [a2 | b2] [a3 | b3] [a4 | b4] f g h;
    try contradiction; cbn; apply cat_assoc.
  - intros [a1 | b1] [a2 | b2] f; try contradiction;
    cbn; apply cat_idl.
  - intros [a1 | b1] [a2 | b2] f; try contradiction;
    cbn; apply cat_idr.
Defined.
