From HoTT Require Import Basics TruncType.
From HoTT.Classes.interfaces Require Import canonical_names orders.
From HoTT.Analysis Require Import Dcpo.

(** With propositional resizing, the subsets of a type in universe [i], ordered by inclusion, form a dcpo at level [i+1], and typeclass search finds it. *)
Section Subsets.
  Universes i j.
  Constraint i < j.
  Context `{PropResizing} `{Univalence} (A : Type@{i}).

  Definition test_isdcpo_subsets
    : IsDcpo@{j} (relation_pointwise (fun _ : A => le_hprop@{i j}))
    := _.
End Subsets.
