Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.theory.groups.

Instance bounded_sl_is_sl `{BoundedSemiLattice L} : SemiLattice L.
Proof.
repeat (split; try apply _).
Qed.

Instance bounded_join_sl_is_join_sl `{BoundedJoinSemiLattice L} : JoinSemiLattice L.
Proof.
repeat (split; try apply _).
Qed.

Instance bounded_sl_mor_is_sl_mor `{H : BoundedJoinPreserving A B f}
  : JoinPreserving f.
Proof.
red;apply _.
Qed.

Lemma preserves_join `{JoinPreserving L K f} x y
  : f (x ⊔ y) = f x ⊔ f y.
Proof. apply preserves_sg_op. Qed.

Lemma preserves_bottom `{BoundedJoinPreserving L K f}
  : f ⊥ = ⊥.
Proof. apply preserves_mon_unit. Qed.

Lemma preserves_meet `{MeetPreserving L K f} x y :
  f (x ⊓ y) = f x ⊓ f y.
Proof. apply preserves_sg_op. Qed.

Section bounded_join_sl_props.
  Context `{BoundedJoinSemiLattice L}.

  Instance join_bottom_l: LeftIdentity (⊔) ⊥ := _.
  Instance join_bottom_r: RightIdentity (⊔) ⊥ := _.
End bounded_join_sl_props.

Section lattice_props.
  Context `{Lattice L}.

  Definition meet_join_absorption x y : x ⊓ (x ⊔ y) = x := absorption x y.
  Definition join_meet_absorption x y : x ⊔ (x ⊓ y) = x := absorption x y.
End lattice_props.

Section distributive_lattice_props.
  Context `{DistributiveLattice L}.

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
  Context `{Lattice L} `{Bottom L} `{!BoundedJoinSemiLattice L}.

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
  Context `{SemiLattice A} `{IsHSet B}
   `{Bop : SgOp B} (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y).

  Lemma projected_sl: SemiLattice B.
  Proof.
  split.
  - apply (projected_com_sg f). assumption.
  - repeat intro; apply (injective f). rewrite !op_correct, (idempotency (&) _).
    reflexivity.
  Qed.
End from_another_sl.

Section from_another_bounded_sl.
  Context `{BoundedSemiLattice A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B -> A) `{!Injective f}
   (op_correct : forall x y, f (x & y) = f x & f y)
   (unit_correct : f mon_unit = mon_unit).

  Lemma projected_bounded_sl: BoundedSemiLattice B.
  Proof.
  split.
  - apply (projected_com_monoid f);trivial.
  - repeat intro; apply (injective f).
    rewrite op_correct, (idempotency (&) _).
    trivial.
  Qed.
End from_another_bounded_sl.

Instance id_join_sl_morphism `{JoinSemiLattice A} : JoinPreserving (@id A)
  := {}.

Instance id_meet_sl_morphism `{MeetSemiLattice A} : MeetPreserving (@id A)
  := {}.

Instance id_bounded_join_sl_morphism `{BoundedJoinSemiLattice A}
  : BoundedJoinPreserving (@id A)
  := {}.

Instance id_lattice_morphism `{Lattice A} : LatticePreserving (@id A)
  := {}.

Section morphism_composition.
  Context `{Join A} `{Meet A} `{Bottom A}
    `{Join B} `{Meet B} `{Bottom B}
    `{Join C} `{Meet C} `{Bottom C}
    (f : A -> B) (g : B -> C).

  Instance compose_join_sl_morphism:
    JoinPreserving f -> JoinPreserving g ->
    JoinPreserving (g ∘ f).
  Proof.
  red; apply _.
  Qed.

  Instance compose_meet_sl_morphism:
    MeetPreserving f -> MeetPreserving g ->
    MeetPreserving (g ∘ f).
  Proof.
  red;apply _.
  Qed.

  Instance compose_bounded_join_sl_morphism:
    BoundedJoinPreserving f -> BoundedJoinPreserving g ->
    BoundedJoinPreserving (g ∘ f).
  Proof.
  red; apply _.
  Qed.

  Instance compose_lattice_morphism:
    LatticePreserving f -> LatticePreserving g -> LatticePreserving (g ∘ f).
  Proof.
  split; apply _.
  Qed.

  Instance invert_join_sl_morphism:
    forall `{!IsEquiv f}, JoinPreserving f ->
    JoinPreserving (f^-1).
  Proof.
  red; apply _.
  Qed.

  Instance invert_meet_sl_morphism:
    forall `{!IsEquiv f}, MeetPreserving f ->
    MeetPreserving (f^-1).
  Proof.
  red; apply _.
  Qed.

  Instance invert_bounded_join_sl_morphism:
    forall `{!IsEquiv f}, BoundedJoinPreserving f ->
    BoundedJoinPreserving (f^-1).
  Proof.
  red; apply _.
  Qed.

  Instance invert_lattice_morphism:
    forall `{!IsEquiv f}, LatticePreserving f -> LatticePreserving (f^-1).
  Proof.
  split; apply _.
  Qed.
End morphism_composition.

Hint Extern 4 (JoinPreserving (_ ∘ _)) =>
  class_apply @compose_join_sl_morphism : typeclass_instances.
Hint Extern 4 (MeetPreserving (_ ∘ _)) =>
  class_apply @compose_meet_sl_morphism : typeclass_instances.
Hint Extern 4 (BoundedJoinPreserving (_ ∘ _)) =>
  class_apply @compose_bounded_join_sl_morphism : typeclass_instances.
Hint Extern 4 (LatticePreserving (_ ∘ _)) =>
  class_apply @compose_lattice_morphism : typeclass_instances.
Hint Extern 4 (JoinPreserving (_^-1)) =>
  class_apply @invert_join_sl_morphism : typeclass_instances.
Hint Extern 4 (MeetPreserving (_^-1)) =>
  class_apply @invert_meet_sl_morphism : typeclass_instances.
Hint Extern 4 (BoundedJoinPreserving (_^-1)) =>
  class_apply @invert_bounded_join_sl_morphism : typeclass_instances.
Hint Extern 4 (LatticePreserving (_^-1)) =>
  class_apply @invert_lattice_morphism : typeclass_instances.
