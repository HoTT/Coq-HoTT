Require Import Basics.
Require Import Types.
Require Import HIT.Truncations.
Require Import Pointed.
Require Import abstract_algebra.
Require Import Spaces.Nat.
Require Import DProp.
(* In this file we define homotopy groups *)

Section HomotopyGroups.

  Context
    (n : nat)
    (X : Type)
   `{IsPointed X}.

  Definition Pi := Tr 0 (iterated_loops n X).

  (* We only have a group structure when 0 < n *)
  Context `{gt : 0 < n}.

  (* We explicitly give the operation here *)
  Global Instance PiOp : SgOp Pi.
  Proof.
    intros a b.
    strip_truncations.
    refine (tr _).
    destruct n, gt.
    exact (concat a b).
  Defined.

  Global Instance PiOp_assoc : Associative PiOp.
  Proof.
    intros x y z.
    strip_truncations.
    unfold PiOp; cbn.
    apply ap.
    destruct n, gt.
    refine (concat_pp_p _ _ _)^.
  Defined.

  Definition PiUnit : Pi.
  Proof.
    refine (tr _).
    destruct n, gt.
    exact idpath.
  Defined.

  Global Instance PiOp_leftId : LeftIdentity PiOp PiUnit.
  Proof.
    intro x.
    strip_truncations.
    unfold PiOp; cbn.
    apply ap.
    destruct n, gt.
    apply concat_1p.
  Defined.

  Global Instance PiOp_rightId : RightIdentity PiOp PiUnit.
  Proof.
    intro x.
    strip_truncations.
    unfold PiOp; cbn.
    apply ap.
    destruct n, gt.
    apply concat_p1.
  Defined.

  Definition PiInverse : Pi -> Pi.
  Proof.
    intro a.
    strip_truncations.
    refine (tr _).
    destruct n, gt.
    exact a^.
  Defined.

  Global Instance PiOp_leftInv : LeftInverse PiOp PiInverse PiUnit.
  Proof.
    intro x.
    strip_truncations.
    unfold PiOp; cbn.
    apply ap.
    destruct n, gt.
    apply concat_Vp.
  Defined.

  Global Instance PiOp_rightInv : RightInverse PiOp PiInverse PiUnit.
  Proof.
    intro x.
    strip_truncations.
    unfold PiOp; cbn.
    apply ap.
    destruct n, gt.
    apply concat_pV.
  Defined.

  Global Instance pi_is_Group : @Group Pi PiOp PiUnit PiInverse.
  Proof.
    repeat split; exact _.
  Defined.

End  HomotopyGroups.