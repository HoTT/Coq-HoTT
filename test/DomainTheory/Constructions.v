From HoTT Require Import Basics TruncType.
From HoTT.Classes.interfaces Require Import canonical_names orders.
From HoTT.DomainTheory Require Import Dcpo Constructions.

(** With propositional resizing, the subsets of a type in universe [i], ordered by inclusion, form a [v]-dcpo for every universe [v], and typeclass search finds it. *)
Section Subsets.
  Universes v i.
  Context `{PropResizing} `{Univalence} (A : Type@{i}).

  Definition test_isdcpo_subsets
    : IsDcpo@{v _ _ _} (relation_pointwise (fun _ : A => le_hprop@{i _}))
    := _.
End Subsets.

(** In particular, they form a dcpo whose index types live in the universe above [i]. *)
Section SubsetsSucc.
  Universes i j.
  Constraint i < j.
  Context `{PropResizing} `{Univalence} (A : Type@{i}).

  Definition test_isdcpo_subsets_succ
    : IsDcpo@{j _ _ _} (relation_pointwise (fun _ : A => le_hprop@{i _}))
    := _.
End SubsetsSucc.
