Require Import Basics Types.
Require Import Algebra.CRing.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Algebra.Subgroup.
Require Import Algebra.QuotientGroup.
Require Import Colimits.Quotient.
Require Import Algebra.Congruence.


Local Open Scope mc_scope.

(** In this file we Ideals *)

(** An additive subgroup I of a ring R is an ideal when: *)
Class IsIdeal {R : CRing} (I : Subgroup R) := {
  (** Forall r : R and x : I, there exists an a : I, such that a = r * x inside R *)
  isideal : forall r x, exists a, issubgroup_incl a = r * issubgroup_incl x;
}.

Class Ideal (R : CRing) := {
  ideal_subgroup : Subgroup R;
  ideal_isideal : IsIdeal ideal_subgroup;
}.

Coercion ideal_subgroup : Ideal >-> Subgroup.
Global Existing Instances ideal_isideal.

Section QuotientRing.

  Context (R : CRing) (I : Ideal R).

  Instance plus_quotient_abgroup : Plus (QuotientAbGroup R I) := abgroup_sgop.

  Instance iscong_mult_incosetL
    : @IsCongruence R (cring_mult _) (@in_cosetL R I _).
  Proof.
    snrapply Build_IsCongruence.
    intros x x' y y' [i p] [j q].
    change (issubgroup_incl (H:=R) i = (- x) + x') in p.
    change (issubgroup_incl (H:=R) j = (- y) + y') in q.
    unfold in_cosetL, hfiber.
    change {m : I & issubgroup_incl (H:=R) m = - (x * y) + (x' * y')}.
    rewrite <- (left_identity (op:=(+)) (x' * y') : 0 + (x' * y') = x' * y').
    rewrite <- (right_inverse (op:=(+)) (x' * y) : (x' * y) - (x' * y) = 0).
    rewrite 2 simple_associativity.
    rewrite negate_mult_distr_l.
    rewrite <- simple_distribute_r.
    rewrite <- simple_associativity.
    rewrite negate_mult_distr_r.
    rewrite <- simple_distribute_l.
    rewrite <- p, <- q.
    pose (isideal x' j) as s; destruct s as [s s'].
    pose (isideal y i) as t; destruct t as [t t'].
    rewrite (commutativity _ y).
    rewrite <- s', <- t'.
    exists (sg_op t s).
    rapply grp_homo_op.
  Defined.

  Instance mult_quotient_abgroup : Mult (QuotientAbGroup R I).
  Proof.
    intro x.
    srapply Quotient_rec.
    { intro y; revert x.
      srapply Quotient_rec.
      { intro x.
        apply class_of.
        exact (x * y). }
      intros x x' p.
      apply qglue.
      by rapply iscong. }
    intros y y' q.
    revert x.
    srapply Quotient_ind_hprop.
    intro x.
    simpl.
    apply qglue.
    by rapply iscong.
  Defined.

  Instance zero_quotient_abgroup : Zero (QuotientAbGroup R I) := class_of _ zero.
  Instance one_quotient_abgroup : One (QuotientAbGroup R I) := class_of _ one.

  Instance isring_quotient_abgroup : IsRing (QuotientAbGroup R I).
  Proof.
    split.
    1: exact _.
    1: repeat split.
    1: exact _.
    (** Associativity follows from the underlying operation *)
    { intros x y.
      snrapply Quotient_ind_hprop; [exact _ | intro z; revert y].
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x ].
      unfold sg_op, mult_is_sg_op, mult_quotient_abgroup; simpl.
      apply ap.
      apply associativity. }
    (* Left and right identity follow from the underlying structure *)
    1,2: snrapply Quotient_ind_hprop; [exact _ | intro x].
    1-2: unfold sg_op, mult_is_sg_op, mult_quotient_abgroup; simpl.
    1-2: apply ap.
    1: apply left_identity.
    1: apply right_identity.
    (** Commutativity also follows *)
    { intros x.
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x].
      unfold sg_op, mult_is_sg_op, mult_quotient_abgroup; simpl.
      apply ap.
      apply commutativity. }
    (** Finally distributivity also follows *)
    { intros x y.
      snrapply Quotient_ind_hprop; [exact _ | intro z; revert y].
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x ].
      unfold sg_op, mult_is_sg_op, mult_quotient_abgroup,
        plus, mult, plus_quotient_abgroup; simpl.
      apply ap.
      apply simple_distribute_l. }
  Defined.

  Definition QuotientRing : CRing
    := Build_CRing (QuotientAbGroup R I) _ _ _ _ _ _.

End QuotientRing.