From HoTT Require Import Basics Types Pointed.
From HoTT Require Import Homotopy.EMSpace Algebra.AbGroups.AbelianGroup.
From HoTT Require Import Truncations.Core Truncations.Connectedness.

(** Typeclass search must find connectivity and truncatedness of Eilenberg-Mac Lane spaces at successor-shaped indices, such as those arising from hypotheses like [IsConnected n.+1 X], via [isconnected_em_succ] and [istrunc_em_succ]. *)

Local Open Scope trunc_scope.

Definition test_isconnected_em_succ `{Univalence} (G : AbGroup) (n := 1%nat)
  : IsConnected n.+1 (K' 3 G)
  := _.

Definition test_istrunc_em_succ `{Univalence} (G : AbGroup) (n := 1%nat)
  : IsTrunc n.+2 (K' 3 G)
  := _.
