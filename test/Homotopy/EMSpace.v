From HoTT Require Import Basics Types Pointed.
From HoTT Require Import Homotopy.EMSpace Algebra.AbGroups.AbelianGroup.
From HoTT Require Import Truncations.Core Truncations.Connectedness.

(** Test that typeclass search finds [isconnected_em_succ]. *)

Local Open Scope trunc_scope.

Definition test_isconnected_em_succ `{Univalence} (G : AbGroup) (n := 1%nat)
  : IsConnected n.+1 (K' 3 G)
  := _.
