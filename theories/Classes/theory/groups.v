Require Import
  HoTT.Classes.interfaces.abstract_algebra.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C f g.

Section group_props.
  Context `{IsGroup G}.

  (** Group inverses are involutive *)
  Global Instance inverse_involutive : Involutive (^).
  Proof.
    intros x.
    transitivity (mon_unit * x).
    2: apply left_identity.
    transitivity ((x^^ *  x^) * x).
    2: apply (@ap _ _ (fun y => y * x)),
          left_inverse.
    transitivity (x^^ * (x^ * x)).
    2: apply associativity.
    transitivity (x^^ * mon_unit).
    2: apply ap, symmetry, left_inverse.
    apply symmetry, right_identity.
  Qed.

  Global Instance isinj_group_inverse : IsInjective (^).
  Proof.
    intros x y E.
    refine ((involutive x)^ @ _ @ involutive y).
    apply ap, E.
  Qed.

  Lemma inverse_mon_unit : mon_unit^ = mon_unit.
  Proof.
    change ((fun x => mon_unit^ = x) mon_unit).
    apply (transport _ (left_inverse mon_unit)).
    apply symmetry, right_identity.
  Qed.

  Global Instance group_cancelL : forall z : G, LeftCancellation (.*.) z.
  Proof.
    intros z x y E.
    rhs_V rapply left_identity.
    rhs_V rapply (ap (.* y) (left_inverse z)).
    rhs_V rapply simple_associativity.
    rhs_V rapply (ap (-z *.) E).
    symmetry.
    lhs rapply simple_associativity.
    lhs rapply (ap (.* x) (left_inverse z)).
    apply left_identity.
  Defined.

  Global Instance group_cancelR: forall z : G, RightCancellation (.*.) z.
  Proof.
    intros z x y E.
    rewrite <-(right_identity x).
    rewrite <-(right_inverse (unit:=mon_unit) z).
    rewrite associativity.
    rewrite E.
    rewrite <-(associativity y ), right_inverse, right_identity.
    reflexivity.
  Qed.

  Lemma inverse_sg_op x y : (x * y)^ = y^ * x^.
  Proof.
    rewrite <- (left_identity (-y * -x)).
    rewrite <- (left_inverse (unit:=mon_unit) (x * y)).
    rewrite <- simple_associativity.
    rewrite <- simple_associativity.
    rewrite (associativity y).
    rewrite right_inverse.
    rewrite (left_identity (-x)).
    rewrite right_inverse.
    apply symmetry, right_identity.
  Qed.

End group_props.

Section abgroup_props.
  Local Open Scope mc_add_scope.

  Lemma negate_sg_op_distr `{IsAbGroup G} x y : -(x + y) = -x + -y.
  Proof.
    path_via (-y + -x).
    - rapply inverse_sg_op.
    - apply commutativity.
  Qed.

  Local Close Scope mc_add_scope.
End abgroup_props.

Section groupmor_props.

  Context `{IsGroup A} `{IsGroup B} {f : A -> B} `{!IsMonoidPreserving f}.

  Lemma preserves_inverse x : f x^ = (f x)^.
  Proof.
    apply (left_cancellation (.*.) (f x)).
    rewrite <-preserves_sg_op.
    rewrite 2!right_inverse.
    apply preserves_mon_unit.
  Qed.

End groupmor_props.

Section from_another_sg.

  Context
    `{IsSemiGroup A} `{IsHSet B}
    `{Bop : SgOp B} (f : B -> A) `{!IsInjective f}
    (op_correct : forall x y, f (x * y) = f x * f y).

  Lemma projected_sg: IsSemiGroup B.
  Proof.
  split.
  - apply _.
  - repeat intro; apply (injective f).
    rewrite !op_correct. apply associativity.
  Qed.
End from_another_sg.

Section from_another_com.

  Context `{SgOp A} `{!Commutative (A:=A) sg_op} {B}
   `{Bop : SgOp B} (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x * y) = f x * f y).

  Lemma projected_comm : Commutative (A:=B) sg_op.
  Proof.
    intros x y.
    apply (injective f).
    rewrite 2!op_correct.
    apply commutativity.
  Qed.

End from_another_com.

Section from_another_com_sg.

  Context
    `{IsCommutativeSemiGroup A} `{IsHSet B}
    `{Bop : SgOp B} (f : B -> A) `{!IsInjective f}
    (op_correct : forall x y, f (x * y) = f x * f y).

  Lemma projected_com_sg : IsCommutativeSemiGroup B.
  Proof.
    split.
    - apply (projected_sg f);assumption.
    - apply (projected_comm f);assumption.
  Qed.

End from_another_com_sg.

Section from_another_monoid.

  Context `{IsMonoid A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x * y) = f x * f y) (unit_correct : f mon_unit = mon_unit).

  Lemma projected_monoid : IsMonoid B.
  Proof.
    split.
    - apply (projected_sg f). assumption.
    - repeat intro; apply (injective f).
      rewrite op_correct, unit_correct, left_identity.
      reflexivity.
    - repeat intro; apply (injective f).
      rewrite op_correct, unit_correct, right_identity.
      reflexivity.
  Qed.

End from_another_monoid.

Section from_another_com_monoid.

  Context
   `{IsCommutativeMonoid A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x * y) = f x * f y)
   (unit_correct : f mon_unit = mon_unit).

  Lemma projected_com_monoid : IsCommutativeMonoid B.
  Proof.
    split.
    - apply (projected_monoid f);assumption.
    - apply (projected_comm f);assumption.
  Qed.

End from_another_com_monoid.

Section from_another_group.

  Context
    `{isg : IsGroup A} `{IsHSet B}
    `{Bop : SgOp B} `{Bunit : MonUnit B} `{Binv : Inverse B}
    (f : B -> A) `{!IsInjective f}
    (op_correct : forall x y, f (x * y) = f x * f y)
    (unit_correct : f mon_unit = mon_unit)
    (inverse_correct : forall x, f x^ = (f x)^).

  Lemma projected_group : IsGroup B.
  Proof.
    split.
    - apply (projected_monoid f);assumption.
    - repeat intro; apply (injective f).
      rewrite op_correct, inverse_correct, unit_correct, left_inverse.
      apply reflexivity.
    - repeat intro; apply (injective f).
      rewrite op_correct, inverse_correct, unit_correct, right_inverse.
      reflexivity.
  Qed.

End from_another_group.

Section from_another_ab_group.
  Local Open Scope mc_add_scope.

  Context `{IsAbGroup A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B}
   (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x + y) = f x + f y)
   (unit_correct : f 0 = 0)
   (negate_correct : forall x, f (-x) = -f x).

  Lemma projected_ab_group : IsAbGroup B.
  Proof.
    split.
    - apply (projected_group f (isg:=abgroup_group _)); assumption.
    - apply (projected_comm f); assumption.
  Qed.

  Local Close Scope mc_add_scope.
End from_another_ab_group.
