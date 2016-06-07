Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.theory.groups.

Instance bounded_sl_is_sl `{BoundedSemiLattice L} : SemiLattice L.
Proof.
repeat (split; try apply _).
Qed.

Instance bounded_join_sl_is_join_sl `{BoundedJoinSemiLattice L} : JoinSemiLattice L.
Proof.
repeat (split; try apply _).
Qed.

Instance bounded_sl_mor_is_sl_mor `{H : BoundedJoinSemiLattice_Morphism A B f}
  : JoinSemiLattice_Morphism f.
Proof.
destruct H. split; apply _.
Qed.

Lemma preserves_join `{JoinSemiLattice_Morphism L K f} x y
  : f (x ⊔ y) = f x ⊔ f y.
Proof preserves_sg_op x y.

Lemma preserves_bottom `{BoundedJoinSemiLattice_Morphism L K f}
  : f ⊥ = ⊥.
Proof (preserves_mon_unit (f:=f)).

Lemma preserves_meet `{MeetSemiLattice_Morphism L K f} x y :
  f (x ⊓ y) = f x ⊓ f y.
Proof preserves_sg_op x y.

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
  Proof join_meet_distr_l _.

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

  Lemma distribute_alt x y z : (x ⊓ y) ⊔ (x ⊓ z) ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) ⊓ (y ⊔ z).
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
  Context `{SemiLattice A}
   `{Bop : SgOp B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y).

  Lemma projected_sl: SemiLattice B.
  Proof.
  split.
  - apply (projected_com_sg f). assumption.
  - repeat intro; apply (injective f). rewrite !op_correct, (idempotency (&) _).
    reflexivity.
  Qed.
End from_another_sl.

Section from_another_bounded_sl.
  Context `{BoundedSemiLattice A}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y)
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

Instance id_join_sl_morphism `{JoinSemiLattice A} : JoinSemiLattice_Morphism (@id A)
  := {}.

Instance id_meet_sl_morphism `{MeetSemiLattice A} : MeetSemiLattice_Morphism (@id A)
  := {}.

Instance id_bounded_join_sl_morphism `{BoundedJoinSemiLattice A}
  : BoundedJoinSemiLattice_Morphism (@id A)
  := {}.

Instance id_lattice_morphism `{Lattice A} : Lattice_Morphism (@id A)
  := {}.

Section morphism_composition.
  Context `{Join A} `{Meet A} `{Bottom A}
    `{Join B} `{Meet B} `{Bottom B}
    `{Join C} `{Meet C} `{Bottom C}
    (f : A → B) (g : B → C).

  Instance compose_join_sl_morphism:
    JoinSemiLattice_Morphism f → JoinSemiLattice_Morphism g →
    JoinSemiLattice_Morphism (g ∘ f).
  Proof.
  split; try apply _.
  - apply join_slmor_a.
  - apply join_slmor_b.
  Qed.

  Instance compose_meet_sl_morphism:
    MeetSemiLattice_Morphism f → MeetSemiLattice_Morphism g →
    MeetSemiLattice_Morphism (g ∘ f).
  Proof.
  split; try apply _.
  - apply meet_slmor_a.
  - apply meet_slmor_b.
  Qed.

  Instance compose_bounded_join_sl_morphism:
    BoundedJoinSemiLattice_Morphism f → BoundedJoinSemiLattice_Morphism g →
    BoundedJoinSemiLattice_Morphism (g ∘ f).
  Proof.
  split; try apply _.
  - apply bounded_join_slmor_a.
  - apply bounded_join_slmor_b.
  Qed.

  Instance compose_lattice_morphism:
    Lattice_Morphism f → Lattice_Morphism g → Lattice_Morphism (g ∘ f).
  Proof.
  split; try apply _.
  - apply latticemor_a.
  - apply latticemor_b.
  Qed.

  Instance invert_join_sl_morphism:
    ∀ `{!Inverse f}, Bijective f → JoinSemiLattice_Morphism f →
    JoinSemiLattice_Morphism (f⁻¹).
  Proof.
  split; try apply _.
  - apply join_slmor_b.
  - apply join_slmor_a.
  Qed.

  Instance invert_meet_sl_morphism:
    ∀ `{!Inverse f}, Bijective f → MeetSemiLattice_Morphism f →
    MeetSemiLattice_Morphism (f⁻¹).
  Proof.
  split; try apply _.
  - apply meet_slmor_b.
  - apply meet_slmor_a.
  Qed.

  Instance invert_bounded_join_sl_morphism:
    ∀ `{!Inverse f}, Bijective f → BoundedJoinSemiLattice_Morphism f →
    BoundedJoinSemiLattice_Morphism (f⁻¹).
  Proof.
  split; try apply _.
  - apply bounded_join_slmor_b.
  - apply bounded_join_slmor_a.
  Qed.

  Instance invert_lattice_morphism:
    ∀ `{!Inverse f}, Bijective f → Lattice_Morphism f → Lattice_Morphism (f⁻¹).
  Proof.
  split; try apply _.
  - apply latticemor_b.
  - apply latticemor_a.
  Qed.
End morphism_composition.

Hint Extern 4 (JoinSemiLattice_Morphism (_ ∘ _)) =>
  class_apply @compose_join_sl_morphism : typeclass_instances.
Hint Extern 4 (MeetSemiLattice_Morphism (_ ∘ _)) =>
  class_apply @compose_meet_sl_morphism : typeclass_instances.
Hint Extern 4 (BoundedJoinSemiLattice_Morphism (_ ∘ _)) =>
  class_apply @compose_bounded_join_sl_morphism : typeclass_instances.
Hint Extern 4 (Lattice_Morphism (_ ∘ _)) =>
  class_apply @compose_lattice_morphism : typeclass_instances.
Hint Extern 4 (JoinSemiLattice_Morphism (_⁻¹)) =>
  class_apply @invert_join_sl_morphism : typeclass_instances.
Hint Extern 4 (MeetSemiLattice_Morphism (_⁻¹)) =>
  class_apply @invert_meet_sl_morphism : typeclass_instances.
Hint Extern 4 (BoundedJoinSemiLattice_Morphism (_⁻¹)) =>
  class_apply @invert_bounded_join_sl_morphism : typeclass_instances.
Hint Extern 4 (Lattice_Morphism (_⁻¹)) =>
  class_apply @invert_lattice_morphism : typeclass_instances.
