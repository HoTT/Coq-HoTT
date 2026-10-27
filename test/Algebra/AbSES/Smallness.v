From HoTT Require Import Basics.Overture Types.Universe.
From HoTT Require Import Algebra.AbGroups.AbelianGroup.
From HoTT Require Import Algebra.AbSES.Core Algebra.AbSES.Ext.
From HoTT Require Import Algebra.AbSES.Classification.

(** Typeclass search should show that [AbSES B A] and [Ext B A] are small in the universe of [B] and [A], not merely in some larger universe. *)

Section Smallness.
  Universe u.
  Context `{Univalence} {B A : AbGroup@{u}}.

  Definition test_issmall_abses : IsSmall@{u _} (AbSES B A) := _.

  Definition test_issmall_ext : IsSmall@{u _} (Ext B A) := _.
End Smallness.
