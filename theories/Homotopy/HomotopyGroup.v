Require Import Basics.
Require Import Types.
Require Import HIT.Truncations.
Require Import Pointed.
Require Import abstract_algebra.
Require Import Spaces.Nat.
Require Import UnivalenceAxiom.

Import TrM.

(* In this file we define homotopy groups *)

Definition Pi n (X : pType) := Tr 0 (iterated_loops n X).

Section PiGroup.

  Context
    (n : nat)
    (X : pType).

  Global Instance PiUnit : MonUnit (Pi n.+1 X).
  Proof.
    by apply tr.
  Defined.

  (* We explicitly give the operation here *)
  Global Instance PiOp : SgOp (Pi n.+1 X).
  Proof.
    intros a b; strip_truncations.
    exact (tr (a @ b)).
  Defined.

  Global Instance PiOp_assoc : Associative PiOp.
  Proof.
    intros x y z; strip_truncations; cbn.
    apply ap, concat_p_pp.
  Defined.

  Global Instance PiOp_leftId : LeftIdentity PiOp PiUnit.
  Proof.
    intro x; strip_truncations; cbn.
    apply ap, concat_1p.
  Defined.

  Global Instance PiOp_rightId : RightIdentity PiOp PiUnit.
  Proof.
    intro x; strip_truncations; cbn.
    apply ap, concat_p1.
  Defined.

  Global Instance PiInverse : Negate (Pi n.+1 X).
  Proof.
    intro; strip_truncations.
    by apply tr, Overture.inverse.
  Defined.

  Global Instance PiOp_leftInv : LeftInverse PiOp PiInverse PiUnit.
  Proof.
    intro x; strip_truncations; cbn.
    apply ap, concat_Vp.
  Defined.

  Global Instance PiOp_rightInv : RightInverse PiOp PiInverse PiUnit.
  Proof.
    intro x; strip_truncations; cbn.
    apply ap, concat_pV.
  Defined.

  Global Instance pi_is_Group : Group (Pi n.+1 X).
  Proof.
    repeat split; exact _.
  Defined.

End  PiGroup.

Global Instance piop_commutative n X : Commutative (PiOp n.+1 X).
Proof.
  intros x y; strip_truncations; cbn.
  apply ap, eckmann_hilton.
Defined.

Global Instance pi_is_AbGroup n X : AbGroup (Pi n.+2 X).
Proof.
  serapply Build_AbGroup.
Defined.

Section PiFunctor.

  Local Open Scope pointed_scope.

  Context
    {n : nat}
    {X Y : pType}
    (f : X ->* Y).

  Definition functor_pi : Pi n.+1 X -> Pi n.+1 Y.
  Proof.
    serapply Trunc_functor.
    serapply iterated_loops_functor.
    exact f.
  Defined.

  Global Instance functor_pi_homomorphism : MonoidPreserving functor_pi.
  Proof.
    apply Build_MonoidPreserving.
    + intros x y.
      strip_truncations.
      apply equiv_path_Tr, tr, loops_functor_pp.
    + apply equiv_path_Tr, tr; cbn.
      destruct n; hott_simpl.
  Defined.

End PiFunctor.

Local Open Scope pointed_scope.

(* Homotopy groups of product space *)
Lemma Pi_prod (X Y : pType) {n}
  : Pi n (X * Y) <~> Pi n X * Pi n Y.
Proof.
  unfold Pi.
  apply (equiv_compose' (equiv_O_prod_cmp _ _ _)).
  apply Trunc_functor_equiv.
  by refine (pequiv_compose _ (iterated_loops_prod _ _)).
Qed.





