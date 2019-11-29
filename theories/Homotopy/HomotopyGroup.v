Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Algebra.Group.
Require Import Truncations.
Require Import Spaces.Nat.

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

  Global Instance pi_is_Group : IsGroup (Pi n.+1 X).
  Proof.
    repeat split; exact _.
  Defined.

End  PiGroup.

Global Instance piop_commutative n X : Commutative (PiOp n.+1 X).
Proof.
  intros x y; strip_truncations; cbn.
  apply ap, eckmann_hilton.
Defined.

Global Instance pi_is_AbGroup n X : IsAbGroup (Pi n.+2 X).
Proof.
  serapply Build_IsAbGroup.
Defined.

Definition pi_loops n X : Pi n.+1 X <~> Pi n (loops X).
Proof.
  apply equiv_O_functor.
  apply pointed_equiv_equiv.
  apply unfold_iterated_loops'.
Defined.

Local Open Scope pointed_scope.

Definition functor_pi (n : nat) {X Y : pType} (f : X ->* Y)
  : Pi n.+1 X -> Pi n.+1 Y.
Proof.
  serapply Trunc_functor.
  serapply iterated_loops_functor.
  exact f.
Defined.

Global Instance functor_pi_homomorphism (n : nat) {X Y : pType} (f : X ->* Y)
  : IsMonoidPreserving (functor_pi n f).
Proof.
  apply Build_IsMonoidPreserving.
  + intros x y.
    strip_truncations.
    apply path_Tr, tr, loops_functor_pp.
  + apply path_Tr, tr; cbn.
    destruct n; hott_simpl.
Defined.

Definition functor_pi_homotopy (n : nat) {X Y : pType} {f g : X ->* Y}
           (h : f ==* g)
  : functor_pi n f == functor_pi n g.
Proof.
  intros x; apply O_functor_homotopy, iterated_loops_2functor; exact h.
Defined.

Definition functor_pi_loops (n : nat) {X Y : pType} (f : X ->* Y)
  : (pi_loops n.+1 Y) o (functor_pi n.+1 f)
    == (functor_pi n (loops_functor f)) o (pi_loops n.+1 X).
Proof.
  intros x.
  unfold pi_loops, functor_pi, equiv_O_functor, Trunc_functor.
  refine ((O_functor_compose 0 _ _ _)^ @ _).
  refine (_ @ (O_functor_compose 0 _ _ _)).
  apply O_functor_homotopy.
  exact (pointed_htpy (unfold_iterated_loops_functor n.+1 f)).
Defined.

(* Homotopy groups of product space *)
Lemma Pi_prod (X Y : pType) {n}
  : Pi n (X * Y) <~> Pi n X * Pi n Y.
Proof.
  unfold Pi.
  apply (equiv_compose' (equiv_O_prod_cmp _ _ _)).
  apply Trunc_functor_equiv.
  by refine (pequiv_compose _ (iterated_loops_prod _ _)).
Qed.

