Require Import Basics.Overture.
Require Import WildCat.Core.
Require Import Algebra.AbGroups.AbelianGroup Algebra.Rings.Ring.
Require Import canonical_names.

Require Import Algebra.Homological.Additive.

(** * Endomorphism Rings *)

Definition End {A : Type} `{IsAdditive A} (X : A) : Ring.
Proof.
  snrapply Build_Ring; repeat split.
  - exact (AbHom X X).
  - exact (fun f g => f $o g).
  - exact (Id _).
  - exact left_heterodistribute_hom.
  - exact right_heterodistribute_hom.
  - exact _.
  - intros f g h.
    apply path_hom.
    symmetry.
    nrapply cat_assoc.
  - intros f.
    apply path_hom.
    nrapply cat_idl.
  - intros g.
    apply path_hom.
    nrapply cat_idr.
Defined.
