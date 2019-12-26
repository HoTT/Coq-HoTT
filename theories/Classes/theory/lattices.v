Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.theory.groups.

Generalizable Variables A B C K L f.

Instance bounded_sl_is_sl `{IsBoundedSemiLattice L} : IsSemiLattice L.
Proof.
repeat (split; try apply _).
Qed.

Instance bounded_join_sl_is_join_sl `{IsBoundedJoinSemiLattice L} : IsJoinSemiLattice L.
Proof.
repeat (split; try apply _).
Qed.

Instance bounded_meet_sl_is_meet_sl `{IsBoundedMeetSemiLattice L} : IsMeetSemiLattice L.
Proof.
repeat (split; try apply _).
Qed.

Instance bounded_lattice_is_lattice `{IsBoundedLattice L} : IsLattice L.
Proof.
repeat split; apply _.
Qed.

Instance bounded_sl_mor_is_sl_mor `{H : IsBoundedJoinPreserving A B f}
  : IsJoinPreserving f.
Proof.
red;apply _.
Qed.

Lemma preserves_join `{IsJoinPreserving L K f} x y
  : f (x ⊔ y) = f x ⊔ f y.
Proof. apply preserves_sg_op. Qed.

Lemma preserves_bottom `{IsBoundedJoinPreserving L K f}
  : f ⊥ = ⊥.
Proof. apply preserves_mon_unit. Qed.

Lemma preserves_meet `{IsMeetPreserving L K f} x y :
  f (x ⊓ y) = f x ⊓ f y.
Proof. apply preserves_sg_op. Qed.

Section bounded_join_sl_props.
  Context `{IsBoundedJoinSemiLattice L}.

  Instance join_bottom_l: LeftIdentity (⊔) ⊥ := _.
  Instance join_bottom_r: RightIdentity (⊔) ⊥ := _.
End bounded_join_sl_props.

Section lattice_props.
  Context `{IsLattice L}.

  Definition meet_join_absorption x y : x ⊓ (x ⊔ y) = x := absorption x y.
  Definition join_meet_absorption x y : x ⊔ (x ⊓ y) = x := absorption x y.
End lattice_props.

Section distributive_lattice_props.
  Context `{IsDistributiveLattice L}.

  Instance join_meet_distr_l: LeftDistribute (⊔) (⊓).
  Proof. exact (join_meet_distr_l _). Qed.

  Global Instance join_meet_distr_r: RightDistribute (⊔) (⊓).
  Proof.
  intros x y z. rewrite !(commutativity _ z).
  apply distribute_l.
  Qed.

  Global Instance meet_join_distr_l: LeftDistribute (⊓) (⊔).
  Proof.
  intros x y z.
  rewrite (simple_distribute_l (f:=join)).
  rewrite (simple_distribute_r (f:=join)).
  rewrite (idempotency (⊔) x).
  rewrite (commutativity (f:=join) y x), meet_join_absorption.
  path_via ((x ⊓ (x ⊔ z)) ⊓ (y ⊔ z)).
  - rewrite (meet_join_absorption x z). reflexivity.
  - rewrite <-simple_associativity.
    rewrite <-distribute_r.
    reflexivity.
  Qed.

  Global Instance meet_join_distr_r: RightDistribute (⊓) (⊔).
  Proof.
  intros x y z. rewrite !(commutativity _ z).
  apply distribute_l.
  Qed.

  Lemma distribute_alt x y z
    : (x ⊓ y) ⊔ (x ⊓ z) ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) ⊓ (y ⊔ z).
  Proof.
  rewrite (distribute_r x y (x ⊓ z)), join_meet_absorption.
  rewrite (distribute_r _ _ (y ⊓ z)).
  rewrite (distribute_l x y z).
  rewrite (commutativity y (x ⊓ z)), <-(simple_associativity _ y).
  rewrite join_meet_absorption.
  rewrite (distribute_r x z y).
  rewrite (commutativity (f:=join) z y).
  rewrite (commutativity (x ⊔ y) (x ⊔ z)).
  rewrite simple_associativity, <-(simple_associativity (x ⊔ z)).
  rewrite (idempotency _ _).
  rewrite (commutativity (x ⊔ z) (x ⊔ y)).
  reflexivity.
  Qed.
End distributive_lattice_props.

Section lower_bounded_lattice.
  Context `{IsLattice L} `{Bottom L} `{!IsBoundedJoinSemiLattice L}.

  Global Instance meet_bottom_l: LeftAbsorb (⊓) ⊥.
  Proof.
  intros x. rewrite <-(join_bottom_l x), absorption.
  trivial.
  Qed.

  Global Instance meet_bottom_r: RightAbsorb (⊓) ⊥.
  Proof.
  intros x.
  rewrite (commutativity (f:=meet)), left_absorb.
  trivial.
  Qed.
End lower_bounded_lattice.

Section from_another_sl.
  Local Open Scope mc_add_scope.
  Context `{IsSemiLattice A} `{IsHSet B}
   `{Bop : SgOp B} (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x + y) = f x + f y).

  Lemma projected_sl: IsSemiLattice B.
  Proof.
  split.
  - apply (projected_com_sg f). assumption.
  - repeat intro; apply (injective f). rewrite !op_correct, (idempotency (+) _).
    reflexivity.
  Qed.
End from_another_sl.

Section from_another_bounded_sl.
  Local Open Scope mc_add_scope.
  Context `{IsBoundedSemiLattice A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x + y) = f x + f y)
   (unit_correct : f mon_unit = mon_unit).

  Lemma projected_bounded_sl: IsBoundedSemiLattice B.
  Proof.
  split.
  - apply (projected_com_monoid f);trivial.
  - repeat intro; apply (injective f).
    rewrite op_correct, (idempotency (+) _).
    trivial.
  Qed.
End from_another_bounded_sl.

Instance id_join_sl_morphism `{IsJoinSemiLattice A} : IsJoinPreserving (@id A)
  := {}.

Instance id_meet_sl_morphism `{IsMeetSemiLattice A} : IsMeetPreserving (@id A)
  := {}.

Instance id_bounded_join_sl_morphism `{IsBoundedJoinSemiLattice A}
  : IsBoundedJoinPreserving (@id A)
  := {}.

Instance id_lattice_morphism `{IsLattice A} : IsLatticePreserving (@id A)
  := {}.

Section morphism_composition.
  Context `{Join A} `{Meet A} `{Bottom A}
    `{Join B} `{Meet B} `{Bottom B}
    `{Join C} `{Meet C} `{Bottom C}
    (f : A -> B) (g : B -> C).

  Instance compose_join_sl_morphism:
    IsJoinPreserving f -> IsJoinPreserving g ->
    IsJoinPreserving (g ∘ f).
  Proof.
  red; apply _.
  Qed.

  Instance compose_meet_sl_morphism:
    IsMeetPreserving f -> IsMeetPreserving g ->
    IsMeetPreserving (g ∘ f).
  Proof.
  red;apply _.
  Qed.

  Instance compose_bounded_join_sl_morphism:
    IsBoundedJoinPreserving f -> IsBoundedJoinPreserving g ->
    IsBoundedJoinPreserving (g ∘ f).
  Proof.
  red; apply _.
  Qed.

  Instance compose_lattice_morphism:
    IsLatticePreserving f -> IsLatticePreserving g -> IsLatticePreserving (g ∘ f).
  Proof.
  split; apply _.
  Qed.

  Instance invert_join_sl_morphism:
    forall `{!IsEquiv f}, IsJoinPreserving f ->
    IsJoinPreserving (f^-1).
  Proof.
  red; apply _.
  Qed.

  Instance invert_meet_sl_morphism:
    forall `{!IsEquiv f}, IsMeetPreserving f ->
    IsMeetPreserving (f^-1).
  Proof.
  red; apply _.
  Qed.

  Instance invert_bounded_join_sl_morphism:
    forall `{!IsEquiv f}, IsBoundedJoinPreserving f ->
    IsBoundedJoinPreserving (f^-1).
  Proof.
  red; apply _.
  Qed.

  Instance invert_lattice_morphism:
    forall `{!IsEquiv f}, IsLatticePreserving f -> IsLatticePreserving (f^-1).
  Proof.
  split; apply _.
  Qed.
End morphism_composition.

Hint Extern 4 (IsJoinPreserving (_ ∘ _)) =>
  class_apply @compose_join_sl_morphism : typeclass_instances.
Hint Extern 4 (IsMeetPreserving (_ ∘ _)) =>
  class_apply @compose_meet_sl_morphism : typeclass_instances.
Hint Extern 4 (IsBoundedJoinPreserving (_ ∘ _)) =>
  class_apply @compose_bounded_join_sl_morphism : typeclass_instances.
Hint Extern 4 (IsLatticePreserving (_ ∘ _)) =>
  class_apply @compose_lattice_morphism : typeclass_instances.
Hint Extern 4 (IsJoinPreserving (_^-1)) =>
  class_apply @invert_join_sl_morphism : typeclass_instances.
Hint Extern 4 (IsMeetPreserving (_^-1)) =>
  class_apply @invert_meet_sl_morphism : typeclass_instances.
Hint Extern 4 (IsBoundedJoinPreserving (_^-1)) =>
  class_apply @invert_bounded_join_sl_morphism : typeclass_instances.
Hint Extern 4 (IsLatticePreserving (_^-1)) =>
  class_apply @invert_lattice_morphism : typeclass_instances.
