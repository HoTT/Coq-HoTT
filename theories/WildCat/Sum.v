Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.

(** ** Sum categories *)

Instance isgraph_sum A B `{IsGraph A} `{IsGraph B}
  : IsGraph (A + B).
Proof.
  econstructor.
  intros [a1 | b1] [a2 | b2].
  + exact (a1 $-> a2).
  + exact Empty.
  + exact Empty.
  + exact (b1 $-> b2).
Defined.

Instance is01cat_sum A B `{ Is01Cat A } `{ Is01Cat B}
  : Is01Cat (A + B).
Proof.
  srapply Build_Is01Cat.
  - intros [a | b]; cbn; apply Id.
  - intros [a | b] [a1 | b1] [a2 | b2];
    try contradiction; cbn; exact cat_comp.
Defined.

Instance is2graph_sum A B `{Is2Graph A, Is2Graph B}
  : Is2Graph (A + B).
Proof.
  intros x y; apply Build_IsGraph.
  destruct x as [a1 | b1], y as [a2 | b2];
  try contradiction; cbn; exact Hom.
Defined.

(* Note: [try contradiction] deals with empty cases. *)
Instance is1cat_sum A B `{ Is1Cat A } `{ Is1Cat B}
  : Is1Cat (A + B).
Proof.
  snrapply Build_Is1Cat.
  - intros x y.
    srapply Build_Is01Cat; destruct x as [a1 | b1], y as [a2 | b2].
    2,3,6,7: contradiction.
    all: cbn.
    1,2: exact Id.
    1,2: intros a b c; exact cat_comp.
  - intros x y; srapply Build_Is0Gpd.
    destruct x as [a1 | b1], y as [a2 | b2].
    2,3: contradiction.
    all: cbn; intros f g; exact gpd_rev.
  - intros x y z h; srapply Build_Is0Functor.
    intros f g p.
    destruct x as [a1 | b1], y as [a2 | b2].
    2,3: contradiction.
    all: destruct z as [a3 | b3].
    2,3: contradiction.
    all: cbn in *; change (f $== g) in p; exact (h $@L p).
  - intros x y z h; srapply Build_Is0Functor.
    intros f g p.
    destruct x as [a1 | b1], y as [a2 | b2].
    2,3: contradiction.
    all: destruct z as [a3 | b3].
    2,3: contradiction.
    all: cbn in *; change (f $== g) in p; exact (p $@R h).
  - intros [a1 | b1] [a2 | b2].
    2,3: contradiction.
    all: intros [a3 | b3].
    2,3: contradiction.
    all: intros [a4 | b4].
    2-3: contradiction.
    all: intros f g h; cbn; apply cat_assoc.
  - intros [a1 | b1] [a2 | b2].
    2,3: contradiction.
    all: intros [a3 | b3].
    2,3: contradiction.
    all: intros [a4 | b4].
    2-3: contradiction.
    all: intros f g h; cbn; apply cat_assoc_opp.
  - intros [a1 | b1] [a2 | b2] f.
    2, 3: contradiction.
    all: cbn; apply cat_idl.
  - intros [a1 | b1] [a2 | b2] f.
    2, 3: contradiction.
    all: cbn; apply cat_idr.
Defined.
