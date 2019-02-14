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
  Definition PiOp : Pi -> Pi -> Pi.
  Proof.
    intros a b.
    strip_truncations.
    refine (tr _).
    destruct n, gt.
    exact (concat a b).
  Defined.

  Definition PiOp_assoc : forall x y z, PiOp x (PiOp y z) = PiOp (PiOp x y) z.
  Proof.
    intros x y z.
    strip_truncations.
    unfold PiOp; cbn.
    apply ap.
    destruct n, gt.
    refine ((concat_pp_p _ _ _)^).
  Defined.

  Definition PiUnit : Pi.
  Proof.
    refine (tr _).
    destruct n, gt.
    exact idpath.
  Defined.

  Definition PiOp_leftId : forall x, PiOp PiUnit x = x.
  Proof.
    intro x.
    strip_truncations.
    unfold PiOp; cbn.
    apply ap.
    destruct n, gt.
    apply concat_1p.
  Defined.

  Definition PiOp_rightId : forall x, PiOp x PiUnit = x.
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

  Definition PiOp_leftInv : forall x, PiOp (PiInverse x) x = PiUnit.
  Proof.
    intro x.
    strip_truncations.
    unfold PiOp; cbn.
    apply ap.
    destruct n, gt.
    apply concat_Vp.
  Defined.

  Definition PiOp_rightInv : forall x, PiOp x (PiInverse x) = PiUnit.
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
    repeat split.
    - exact _.
    - exact PiOp_assoc.
    - exact PiOp_leftId.
    - exact PiOp_rightId.
    - exact PiOp_leftInv.
    - exact PiOp_rightInv.
  Defined.

End  HomotopyGroups.