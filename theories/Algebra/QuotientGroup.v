Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext.
Require Import Algebra.Group.
Require Import Algebra.Subgroup.
Require Import Algebra.Congruence.
Require Import Colimits.Quotient.

(** * Quotient groups *)

Local Open Scope mc_mult_scope.

Section GroupCongruenceQuotient.

  Context {G : Group} {R : Relation G}
    `{is_mere_relation _ R} `{!IsCongruence R} (* Congruence just means respects op *)
    `{!Reflexive R} `{!Symmetric R} `{!Transitive R}.

  Definition CongruenceQuotient := G / R.

  Instance congquot_sgop : SgOp CongruenceQuotient.
  Proof.
    intros x.
    serapply Quotient_rec.
    { intro y; revert x.
      serapply Quotient_rec.
      { intros x.
        apply class_of.
        exact (x * y). }
      intros a b r.
      cbn.
      apply qglue.
      by apply iscong. }
    intros a b r.
    revert x.
    serapply Quotient_ind_hprop.
    intro x.
    apply qglue.
    by apply iscong.
  Defined.

  Instance congquot_mon_unit : MonUnit CongruenceQuotient.
  Proof.
    apply class_of, mon_unit.
  Defined.

  Instance congquot_negate : Negate CongruenceQuotient.
  Proof.
    serapply Quotient_functor.
    1: apply negate.
    intros x y p.
    rewrite <- (left_identity (-x)).
    destruct (left_inverse y).
    set (-y * y * -x).
    rewrite <- (right_identity (-y)).
    destruct (right_inverse x).
    unfold g; clear g.
    rewrite <- simple_associativity.
    apply iscong; try reflexivity.
    apply iscong; try reflexivity.
    by symmetry.
  Defined.

  Instance congquot_sgop_associative : Associative congquot_sgop.
  Proof.
    intros x y.
    serapply Quotient_ind_hprop; intro a; revert y.
    serapply Quotient_ind_hprop; intro b; revert x.
    serapply Quotient_ind_hprop; intro c.
    simpl; by rewrite associativity.
  Defined.

  Instance issemigroup_congquot : IsSemiGroup CongruenceQuotient := {}.

  Instance congquot_leftidentity
    : LeftIdentity congquot_sgop congquot_mon_unit.
  Proof.
    serapply Quotient_ind_hprop; intro x.
    by simpl; rewrite left_identity.
  Defined.

  Instance congquot_rightidentity
    : RightIdentity congquot_sgop congquot_mon_unit.
  Proof.
    serapply Quotient_ind_hprop; intro x.
    by simpl; rewrite right_identity.
  Defined.

  Instance ismonoid_quotientgroup : IsMonoid CongruenceQuotient := {}.

  Instance quotientgroup_leftinverse
    : LeftInverse congquot_sgop congquot_negate congquot_mon_unit.
  Proof.
    serapply Quotient_ind_hprop; intro x.
    by simpl; rewrite left_inverse.
  Defined.

  Instance quotientgroup_rightinverse
    : RightInverse congquot_sgop congquot_negate congquot_mon_unit.
  Proof.
    serapply Quotient_ind_hprop; intro x.
    by simpl; rewrite right_inverse.
  Defined.

  Global Instance isgroup_quotientgroup : IsGroup CongruenceQuotient := {}.

End GroupCongruenceQuotient.

(** Now we can define the quotient group by a normal subgroup. *)

Section QuotientGroup.

  Context (G : Group) (N : Subgroup G) `{!IsNormalSubgroup N}.

  Instance iscongruence_in_cosetL: IsCongruence in_cosetL.
  Proof.
    serapply Build_IsCongruence.
    intros; by apply in_cosetL_cong.
  Defined.

  Instance iscongruence_in_cosetR: IsCongruence in_cosetR.
  Proof.
    serapply Build_IsCongruence.
    intros; by apply in_cosetR_cong.
  Defined.

  (** Now we have to make a choice whether to pick the left or right cosets. Due to existing convention we shall pick left cosets but we note that we could equally have picked right. *)
  Definition QuotientGroup : Group.
  Proof.
    erapply (Build_Group (G / in_cosetL)).
    apply isgroup_quotientgroup.
  Defined.

End QuotientGroup.
