Require Import
  HoTT.Classes.interfaces.abstract_algebra.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C f g.

Section group_props.
  Context `{IsGroup G}.

  (** Group inverses are involutive *)
  Global Instance negate_involutive : Involutive (-).
  Proof.
    intros x.
    transitivity (mon_unit * x).
    2: apply left_identity.
    transitivity ((- - x * - x) * x).
    2: apply (@ap _ _ (fun y => y * x)),
          left_inverse.
    transitivity (- - x * (- x * x)).
    2: apply associativity.
    transitivity (- - x * mon_unit).
    2: apply ap, symmetry, left_inverse.
    apply symmetry, right_identity.
  Qed.

  Global Instance isinj_group_negate : IsInjective (-).
  Proof.
    intros x y E.
    refine ((involutive x)^ @ _ @ involutive y).
    apply ap, E.
  Qed.

  Lemma negate_mon_unit : - mon_unit = mon_unit.
  Proof.
    change ((fun x => - mon_unit = x) mon_unit).
    apply (transport _ (left_inverse mon_unit)).
    apply symmetry, right_identity.
  Qed.

  Global Instance group_cancelL : forall z : G, LeftCancellation (.*.) z.
  Proof.
    intros z x y E.
    rewrite <- (left_identity x).
    rewrite <- (left_inverse (unit:=mon_unit) z).
    rewrite <- simple_associativity.
    rewrite E.
    rewrite simple_associativity, (left_inverse z), left_identity.
    reflexivity.
  Qed.

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

  Lemma negate_sg_op x y : - (x * y) = -y * -x.
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

  Lemma negate_sg_op_distr `{IsAbGroup G} x y : -(x * y) = -x * -y.
  Proof.
    path_via (-y * -x).
    - apply negate_sg_op.
    - apply commutativity.
  Qed.

End abgroup_props.

Section groupmor_props.

  Context `{IsGroup A} `{IsGroup B} {f : A -> B} `{!IsMonoidPreserving f}.

  Lemma preserves_negate x : f (-x) = -f x.
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
    `{IsGroup A} `{IsHSet B}
    `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B}
    (f : B -> A) `{!IsInjective f}
    (op_correct : forall x y, f (x * y) = f x * f y)
    (unit_correct : f mon_unit = mon_unit)
    (negate_correct : forall x, f (-x) = -f x).

  Lemma projected_group : IsGroup B.
  Proof.
    split.
    - apply (projected_monoid f);assumption.
    - repeat intro; apply (injective f).
      rewrite op_correct, negate_correct, unit_correct, left_inverse.
      apply reflexivity.
    - repeat intro; apply (injective f).
      rewrite op_correct, negate_correct, unit_correct, right_inverse.
      reflexivity.
  Qed.

End from_another_group.

Section from_another_ab_group.

  Context `{IsAbGroup A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B}
   (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x * y) = f x * f y)
   (unit_correct : f mon_unit = mon_unit)
   (negate_correct : forall x, f (-x) = -f x).

  Lemma projected_ab_group : IsAbGroup B.
  Proof.
    split.
    - apply (projected_group f);assumption.
    - apply (projected_comm f);assumption.
  Qed.

End from_another_ab_group.

Section compose_mor.

  Context
    `{SgOp A} `{MonUnit A}
    `{SgOp B} `{MonUnit B}
    `{SgOp C} `{MonUnit C}
    (f : A -> B) (g : B -> C).

  Global Instance id_sg_morphism : IsSemiGroupPreserving (@id A).
  Proof.
    split.
  Defined.

  Global Instance id_monoid_morphism : IsMonoidPreserving (@id A).
  Proof.
    split; split.
  Defined.

  (** Making these global instances causes typeclass loops.  Instead they are declared below as [Hint Extern]s that apply only when the goal has the specified form. *)
  Local Instance compose_sg_morphism : IsSemiGroupPreserving f -> IsSemiGroupPreserving g ->
    IsSemiGroupPreserving (g ∘ f).
  Proof.
    red; intros fp gp x y.
    unfold Compose.
    refine ((ap g _) @ _).
    - apply fp.
    - apply gp.
  Defined.

  Local Instance compose_monoid_morphism : IsMonoidPreserving f -> IsMonoidPreserving g ->
    IsMonoidPreserving (g ∘ f).
  Proof.
    intros;split.
    - apply _.
    - red;unfold Compose.
      etransitivity;[|apply preserves_mon_unit].
      apply ap,preserves_mon_unit.
  Defined.

  Local Instance invert_sg_morphism
    : forall `{!IsEquiv f}, IsSemiGroupPreserving f ->
      IsSemiGroupPreserving (f^-1).
  Proof.
    red; intros E fp x y.
    apply (equiv_inj f).
    refine (_ @ _ @ _ @ _)^.
    - apply fp.
    (* We could use [apply ap2; apply eisretr] here, but it is convenient
       to have things in terms of ap. *)
    - refine (ap (fun z => z * _) _); apply eisretr.
    - refine (ap (fun z => _ * z) _); apply eisretr.
    - symmetry; apply eisretr.
  Defined.

  Local Instance invert_monoid_morphism :
    forall `{!IsEquiv f}, IsMonoidPreserving f -> IsMonoidPreserving (f^-1).
  Proof.
    intros;split.
    - apply _.
    - apply (equiv_inj f).
      refine (_ @ _).
      + apply eisretr.
      + symmetry; apply preserves_mon_unit.
  Defined.

End compose_mor.

Hint Extern 4 (IsSemiGroupPreserving (_ ∘ _)) =>
  class_apply @compose_sg_morphism : typeclass_instances.
Hint Extern 4 (IsMonoidPreserving (_ ∘ _)) =>
  class_apply @compose_monoid_morphism : typeclass_instances.

Hint Extern 4 (IsSemiGroupPreserving (_ o _)) =>
  class_apply @compose_sg_morphism : typeclass_instances.
Hint Extern 4 (IsMonoidPreserving (_ o _)) =>
  class_apply @compose_monoid_morphism : typeclass_instances.

Hint Extern 4 (IsSemiGroupPreserving (_^-1)) =>
  class_apply @invert_sg_morphism : typeclass_instances.
Hint Extern 4 (IsMonoidPreserving (_^-1)) =>
  class_apply @invert_monoid_morphism : typeclass_instances.
