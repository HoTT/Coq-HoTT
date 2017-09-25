Require Import
  HoTT.Classes.interfaces.abstract_algebra.

Section group_props.
Context `{Group G}.

Global Instance negate_involutive: Involutive (-).
Proof.
intros x.
path_via (mon_unit & x).
path_via ((- - x & - x) & x).
path_via (- - x & (- x & x)).
path_via (- - x & mon_unit).
- apply symmetry. apply right_identity.
- apply ap. apply symmetry. apply left_inverse.
- apply associativity.
- apply (@ap _ _ (fun y => y & x)).
  apply left_inverse.
- apply left_identity.
Qed.

Global Instance: Injective (-).
Proof.
intros x y E.
rewrite <-(involutive x), <-(involutive y), E. reflexivity.
Qed.

Lemma negate_mon_unit : -mon_unit = mon_unit.
Proof.
change ((fun x => - mon_unit = x) mon_unit).
apply (transport _ (left_inverse mon_unit)).
rewrite right_identity. reflexivity.
Qed.

Global Instance: forall z : G, LeftCancellation (&) z.
Proof.
  intros z x y E.
  rewrite <-(left_identity x).
  rewrite <-(left_inverse (unit:=mon_unit) z).
  rewrite <-simple_associativity.
  rewrite E.
  rewrite simple_associativity, (left_inverse z), left_identity.
  reflexivity.
Qed.

Global Instance: forall z : G, RightCancellation (&) z.
Proof.
  intros z x y E.
  rewrite <-(right_identity x).
  rewrite <-(right_inverse (unit:=mon_unit) z).
  rewrite associativity.
  rewrite E.
  rewrite <-(associativity y ), right_inverse, right_identity.
  reflexivity.
Qed.

Lemma negate_sg_op x y : - (x & y) = -y & -x.
Proof.
rewrite <-(left_identity (-y & -x)).
rewrite <-(left_inverse (unit:=mon_unit) (x & y)).
rewrite <-(associativity (_:G)).
rewrite <-(associativity (_:G)).
rewrite (associativity y).
rewrite right_inverse.
rewrite (left_identity (-x)).
rewrite right_inverse.
apply symmetry, right_identity.
Qed.

End group_props.

Section abgroup_props.

Lemma negate_sg_op_distr `{AbGroup G} x y : -(x & y) = -x & -y.
Proof.
path_via (-y & -x).
apply negate_sg_op.
apply commutativity.
Qed.

End abgroup_props.

Section groupmor_props.

  Context `{Group A} `{Group B} {f : A -> B} `{!MonoidPreserving f}.

  Lemma preserves_negate x : f (-x) = -f x.
  Proof.
  apply (left_cancellation (&) (f x)).
  rewrite <-preserves_sg_op.
  rewrite 2!right_inverse.
  apply preserves_mon_unit.
  Qed.

End groupmor_props.

Section from_another_sg.
  Context `{SemiGroup A} `{IsHSet B}
   `{Bop : SgOp B} (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y).

  Lemma projected_sg: SemiGroup B.
  Proof.
  split.
  - apply _.
  - repeat intro; apply (injective f).
    rewrite !op_correct. apply associativity.
  Qed.
End from_another_sg.

Section from_another_com.

  Context `{SgOp A} `{!Commutative (A:=A) sg_op} {B}
   `{Bop : SgOp B} (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y).

  Lemma projected_comm : Commutative (A:=B) sg_op.
  Proof.
  intros x y.
  apply (injective f).
  rewrite 2!op_correct.
  apply commutativity.
  Qed.

End from_another_com.

Section from_another_com_sg.
  Context `{CommutativeSemiGroup A} `{IsHSet B}
   `{Bop : SgOp B} (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y).

  Lemma projected_com_sg: CommutativeSemiGroup B.
  Proof.
  split.
  - apply (projected_sg f);assumption.
  - apply (projected_comm f);assumption.
  Qed.
End from_another_com_sg.

Section from_another_monoid.
  Context `{Monoid A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit).

  Lemma projected_monoid: Monoid B.
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
  Context `{CommutativeMonoid A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y)
   (unit_correct : f mon_unit = mon_unit).

  Lemma projected_com_monoid: CommutativeMonoid B.
  Proof.
  split.
  - apply (projected_monoid f);assumption.
  - apply (projected_comm f);assumption.
  Qed.
End from_another_com_monoid.

Section from_another_group.
  Context `{Group A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B}
   (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y)
   (unit_correct : f mon_unit = mon_unit)
   (negate_correct : forall x, f (-x) = -f x).

  Lemma projected_group: Group B.
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
  Context `{AbGroup A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B}
   (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y)
   (unit_correct : f mon_unit = mon_unit)
   (negate_correct : forall x, f (-x) = -f x).

  Lemma projected_ab_group: AbGroup B.
  Proof.
  split.
  - apply (projected_group f);assumption.
  - apply (projected_comm f);assumption.
  Qed.
End from_another_ab_group.

Instance id_sg_morphism `{SemiGroup A}: SemiGroupPreserving (@id A).
Proof.
red. split.
Qed.

Instance id_monoid_morphism `{Monoid A}: MonoidPreserving (@id A).
Proof.
split;split.
Qed.

Section compose_mor.

  Context `{SgOp A} `{MonUnit A}
    `{SgOp B} `{MonUnit B}
    `{SgOp C} `{MonUnit C}
    (f : A -> B) (g : B -> C).

  Instance compose_sg_morphism : SemiGroupPreserving f -> SemiGroupPreserving g ->
    SemiGroupPreserving (g ∘ f).
  Proof.
  red;intros.
  unfold Compose.
  rewrite (preserves_sg_op x y).
  apply preserves_sg_op.
  Qed.

  Instance compose_monoid_morphism : MonoidPreserving f -> MonoidPreserving g ->
    MonoidPreserving (g ∘ f).
  Proof.
  intros;split.
  - apply _.
  - red;unfold Compose.
    etransitivity;[|apply preserves_mon_unit].
    apply ap,preserves_mon_unit.
  Qed.

  Instance invert_sg_morphism:
    forall `{!IsEquiv f}, SemiGroupPreserving f ->
      SemiGroupPreserving (f^-1).
  Proof.
  red;intros.
  apply (Paths.equiv_inj f).
  rewrite (preserves_sg_op (f:=f)).
  rewrite !eisretr.
  reflexivity.
  Qed.

  Instance invert_monoid_morphism :
    forall `{!IsEquiv f}, MonoidPreserving f -> MonoidPreserving (f^-1).
  Proof.
  intros;split.
  - apply _.
  - apply (Paths.equiv_inj f).
    rewrite eisretr.
    rewrite (preserves_mon_unit (f:=f)). reflexivity.
  Qed.

End compose_mor.

Hint Extern 4 (SemiGroupPreserving (_ ∘ _)) =>
  class_apply @compose_sg_morphism : typeclass_instances.
Hint Extern 4 (MonoidPreserving (_ ∘ _)) =>
  class_apply @compose_monoid_morphism : typeclass_instances.

Hint Extern 4 (SemiGroupPreserving (_^-1)) =>
  class_apply @invert_sg_morphism : typeclass_instances.
Hint Extern 4 (MonoidPreserving (_^-1)) =>
  class_apply @invert_monoid_morphism : typeclass_instances.
