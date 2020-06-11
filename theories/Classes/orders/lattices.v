Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.orders.maps
  HoTT.Classes.orders.semirings
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.lattices.

Generalizable Variables K L f.

(*
We prove that the algebraic definition of a lattice corresponds to the
order theoretic one. Note that we do not make any of these instances global,
because that would cause loops.
*)
Section join_semilattice_order.
  Context `{JoinSemiLatticeOrder L}.

  Lemma join_ub_3_r x y z : z ≤ x ⊔ y ⊔ z.
  Proof.
  apply join_ub_r.
  Qed.

  Lemma join_ub_3_m x y z : y ≤ x ⊔ y ⊔ z.
  Proof.
  transitivity (x ⊔ y).
  - apply join_ub_r.
  - apply join_ub_l.
  Qed.

  Lemma join_ub_3_l x y z : x ≤ x ⊔ y ⊔ z.
  Proof.
  transitivity (x ⊔ y); apply join_ub_l.
  Qed.

  Lemma join_ub_3_assoc_l x y z : x ≤ x ⊔ (y ⊔ z).
  Proof.
  apply join_ub_l.
  Qed.

  Lemma join_ub_3_assoc_m x y z : y ≤ x ⊔ (y ⊔ z).
  Proof.
  transitivity (y ⊔ z).
  - apply join_ub_l.
  - apply join_ub_r.
  Qed.

  Lemma join_ub_3_assoc_r x y z : z ≤ x ⊔ (y ⊔ z).
  Proof.
  transitivity (y ⊔ z); apply join_ub_r.
  Qed.

  Instance join_sl_order_join_sl: IsJoinSemiLattice L.
  Proof.
  repeat split.
  - apply _.
  - intros x y z. apply (antisymmetry (≤)).
    + apply join_lub.
      * apply join_ub_3_l.
      * apply join_lub.
        ** apply join_ub_3_m.
        ** apply join_ub_3_r.
    + apply join_lub.
      * apply join_lub.
        ** apply join_ub_3_assoc_l.
        ** apply join_ub_3_assoc_m.
      * apply join_ub_3_assoc_r.
  - intros x y. apply (antisymmetry (≤)); apply join_lub;
    first [apply join_ub_l | apply join_ub_r].
  - intros x. red. apply (antisymmetry (≤)).
    + apply join_lub; apply reflexivity.
    + apply join_ub_l.
  Qed.

  Lemma join_le_compat_r x y z : z ≤ x -> z ≤ x ⊔ y.
  Proof.
  intros E. transitivity x.
  - trivial.
  - apply join_ub_l.
  Qed.

  Lemma join_le_compat_l x y z : z ≤ y -> z ≤ x ⊔ y.
  Proof.
  intros E. rewrite (commutativity (f:=join)).
  apply join_le_compat_r.
  trivial.
  Qed.

  Lemma join_l x y : y ≤ x -> x ⊔ y = x.
  Proof.
  intros E. apply (antisymmetry (≤)).
  - apply join_lub;trivial. apply reflexivity.
  - apply join_ub_l.
  Qed.

  Lemma join_r x y : x ≤ y -> x ⊔ y = y.
  Proof.
  intros E. rewrite (commutativity (f:=join)).
  apply join_l.
  trivial.
  Qed.

  Lemma join_sl_le_spec x y : x ≤ y <-> x ⊔ y = y.
  Proof.
  split; intros E.
  - apply join_r. trivial.
  - rewrite <-E. apply join_ub_l.
  Qed.

  Global Instance join_le_preserving_l : forall z, OrderPreserving (z ⊔).
  Proof.
  red;intros.
  apply join_lub.
  - apply join_ub_l.
  - apply join_le_compat_l. trivial.
  Qed.

  Global Instance join_le_preserving_r : forall z, OrderPreserving (⊔ z).
  Proof.
  intros. apply maps.order_preserving_flip.
  Qed.

  Lemma join_le_compat x₁ x₂ y₁ y₂ : x₁ ≤ x₂ -> y₁ ≤ y₂ -> x₁ ⊔ y₁ ≤ x₂ ⊔ y₂.
  Proof.
  intros E1 E2. transitivity (x₁ ⊔ y₂).
  - apply (order_preserving (x₁ ⊔)). trivial.
  - apply (order_preserving (⊔ y₂));trivial.
  Qed.

  Lemma join_le x y z : x ≤ z -> y ≤ z -> x ⊔ y ≤ z.
  Proof.
    apply join_lub.
  Qed.

  Section total_join.
  Context `{!TotalRelation le}.

  Lemma total_join_either `{!TotalRelation le} x y : join x y = x |_| join x y = y.
  Proof.
  destruct (total le x y) as [E|E].
  - right. apply join_r,E.
  - left. apply join_l,E.
  Qed.

  Definition max x y :=
    match total le x y with
    | inl _ => y
    | inr _ => x
    end.

  Lemma total_join_max x y : join x y = max x y.
  Proof.
  unfold max;destruct (total le x y) as [E|E].
  - apply join_r,E.
  - apply join_l,E.
  Qed.
  End total_join.

  Lemma join_idempotent x : x ⊔ x = x.
  Proof.
    assert (le1 : x ⊔ x ≤ x).
    {
      refine (join_lub _ _ _ _ _); apply reflexivity.
    }
    assert (le2 : x ≤ x ⊔ x).
    {
      refine (join_ub_l _ _).
    }
    refine (antisymmetry _ _ _ le1 le2).
  Qed.
End join_semilattice_order.

Section bounded_join_semilattice.
  Context `{JoinSemiLatticeOrder L} `{Bottom L} `{!IsBoundedJoinSemiLattice L}.

  Lemma above_bottom x : ⊥ ≤ x.
  Proof.
  apply join_sl_le_spec.
  rewrite left_identity.
  reflexivity.
  Qed.

  Lemma below_bottom x : x ≤ ⊥ -> x = ⊥.
  Proof.
  intros E.
  apply join_sl_le_spec in E. rewrite right_identity in E.
  trivial.
  Qed.
End bounded_join_semilattice.

Section meet_semilattice_order.
  Context `{MeetSemiLatticeOrder L}.

  Lemma meet_lb_3_r x y z : x ⊓ y ⊓ z ≤ z.
  Proof.
  apply meet_lb_r.
  Qed.

  Lemma meet_lb_3_m x y z : x ⊓ y ⊓ z ≤ y.
  Proof.
  transitivity (x ⊓ y).
  - apply meet_lb_l.
  - apply meet_lb_r.
  Qed.

  Lemma meet_lb_3_l x y z : x ⊓ y ⊓ z ≤ x.
  Proof.
  transitivity (x ⊓ y); apply meet_lb_l.
  Qed.

  Lemma meet_lb_3_assoc_l x y z : x ⊓ (y ⊓ z) ≤ x.
  Proof.
  apply meet_lb_l.
  Qed.

  Lemma meet_lb_3_assoc_m x y z : x ⊓ (y ⊓ z) ≤ y.
  Proof.
  transitivity (y ⊓ z).
  - apply meet_lb_r.
  - apply meet_lb_l.
  Qed.

  Lemma meet_lb_3_assoc_r x y z : x ⊓ (y ⊓ z) ≤ z.
  Proof.
  transitivity (y ⊓ z); apply meet_lb_r.
  Qed.

  Instance meet_sl_order_meet_sl: IsMeetSemiLattice L.
  Proof.
  repeat split.
  - apply _.
  - intros x y z. apply (antisymmetry (≤)).
    + apply meet_glb.
      * apply meet_glb.
        ** apply meet_lb_3_assoc_l.
        ** apply meet_lb_3_assoc_m.
      * apply meet_lb_3_assoc_r.
    + apply meet_glb.
      ** apply meet_lb_3_l.
      ** apply meet_glb.
         *** apply meet_lb_3_m.
         *** apply meet_lb_3_r.
  - intros x y. apply (antisymmetry (≤)); apply meet_glb;
    first [apply meet_lb_l | try apply meet_lb_r].
  - intros x. red. apply (antisymmetry (≤)).
    + apply meet_lb_l.
    + apply meet_glb;apply reflexivity.
  Qed.

  Lemma meet_le_compat_r x y z : x ≤ z -> x ⊓ y ≤ z.
  Proof.
  intros E. transitivity x.
  - apply meet_lb_l.
  - trivial.
  Qed.

  Lemma meet_le_compat_l x y z : y ≤ z -> x ⊓ y ≤ z.
  Proof.
  intros E. rewrite (commutativity (f:=meet)).
  apply meet_le_compat_r.
  trivial.
  Qed.

  Lemma meet_l x y : x ≤ y -> x ⊓ y = x.
  Proof.
  intros E. apply (antisymmetry (≤)).
  - apply meet_lb_l.
  - apply meet_glb; trivial. apply reflexivity.
  Qed.

  Lemma meet_r x y : y ≤ x -> x ⊓ y = y.
  Proof.
  intros E. rewrite (commutativity (f:=meet)). apply meet_l.
  trivial.
  Qed.

  Lemma meet_sl_le_spec x y : x ≤ y <-> x ⊓ y = x.
  Proof.
  split; intros E.
  - apply meet_l;trivial.
  - rewrite <-E. apply meet_lb_r.
  Qed.

  Global Instance: forall z, OrderPreserving (z ⊓).
  Proof.
  red;intros.
  apply meet_glb.
  - apply meet_lb_l.
  - apply  meet_le_compat_l. trivial.
  Qed.

  Global Instance: forall z, OrderPreserving (⊓ z).
  Proof.
  intros. apply maps.order_preserving_flip.
  Qed.

  Lemma meet_le_compat x₁ x₂ y₁ y₂ : x₁ ≤ x₂ -> y₁ ≤ y₂ -> x₁ ⊓ y₁ ≤ x₂ ⊓ y₂.
  Proof.
  intros E1 E2. transitivity (x₁ ⊓ y₂).
  - apply (order_preserving (x₁ ⊓)). trivial.
  - apply (order_preserving (⊓ y₂)). trivial.
  Qed.

  Lemma meet_le x y z : z ≤ x -> z ≤ y -> z ≤ x ⊓ y.
  Proof.
    apply meet_glb.
  Qed.

  Section total_meet.
  Context `{!TotalRelation le}.

  Lemma total_meet_either x y : meet x y = x |_| meet x y = y.
  Proof.
  destruct (total le x y) as [E|E].
  - left. apply meet_l,E.
  - right. apply meet_r,E.
  Qed.

  Definition min x y :=
    match total le x y with
    | inr _ => y
    | inl _ => x
    end.

  Lemma total_meet_min x y : meet x y = min x y.
  Proof.
  unfold min. destruct (total le x y) as [E|E].
  - apply meet_l,E.
  - apply meet_r,E.
  Qed.
  End total_meet.

  Lemma meet_idempotent x : x ⊓ x = x.
  Proof.
    assert (le1 : x ⊓ x ≤ x).
    {
      refine (meet_lb_l _ _).
    }
    assert (le2 : x ≤ x ⊓ x).
    {
      refine (meet_glb _ _ _ _ _); apply reflexivity.
    }
    refine (antisymmetry _ _ _ le1 le2).
  Qed.

End meet_semilattice_order.

Section lattice_order.
  Context `{LatticeOrder L}.

  Instance: IsJoinSemiLattice L := join_sl_order_join_sl.
  Instance: IsMeetSemiLattice L := meet_sl_order_meet_sl.

  Instance: Absorption (⊓) (⊔).
  Proof.
  intros x y. apply (antisymmetry (≤)).
  - apply meet_lb_l.
  - apply meet_le.
   + apply reflexivity.
   + apply join_ub_l.
  Qed.

  Instance: Absorption (⊔) (⊓).
  Proof.
  intros x y. apply (antisymmetry (≤)).
  - apply join_le.
    + apply reflexivity.
    + apply meet_lb_l.
  - apply join_ub_l.
  Qed.

  Instance lattice_order_lattice: IsLattice L := {}.

  Lemma meet_join_distr_l_le x y z : (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z).
  Proof.
  apply meet_le.
  - apply join_le; apply meet_lb_l.
  - apply join_le.
    + transitivity y.
      * apply meet_lb_r.
      * apply join_ub_l.
    + transitivity z.
      * apply meet_lb_r.
      * apply join_ub_r.
  Qed.

  Lemma join_meet_distr_l_le x y z : x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ (x ⊔ z).
  Proof.
  apply meet_le.
  - apply join_le.
    + apply join_ub_l.
    + transitivity y.
      * apply meet_lb_l.
      * apply join_ub_r.
  - apply join_le.
    + apply join_ub_l.
    + transitivity z.
      * apply meet_lb_r.
      * apply join_ub_r.
  Qed.
End lattice_order.

Definition default_join_sl_le `{IsJoinSemiLattice L} : Le L :=  fun x y => x ⊔ y = y.

Section join_sl_order_alt.
  Context `{IsJoinSemiLattice L} `{Le L} `{is_mere_relation L le}
    (le_correct : forall x y, x ≤ y <-> x ⊔ y = y).

  Lemma alt_Build_JoinSemiLatticeOrder : JoinSemiLatticeOrder (≤).
  Proof.
  repeat split.
  - apply _.
  - apply _.
  - intros x.
    apply le_correct. apply binary_idempotent.
  - intros x y z E1 E2.
    apply le_correct in E1;apply le_correct in E2;apply le_correct.
    rewrite <-E2, simple_associativity, E1. reflexivity.
  - intros x y E1 E2.
    apply le_correct in E1;apply le_correct in E2.
    rewrite <-E1, (commutativity (f:=join)).
    apply symmetry;trivial.
  - intros. apply le_correct.
    rewrite simple_associativity,binary_idempotent.
    reflexivity.
  - intros;apply le_correct.
    rewrite (commutativity (f:=join)).
    rewrite <-simple_associativity.
    rewrite (idempotency _ _).
    reflexivity.
  - intros x y z E1 E2.
    apply le_correct in E1;apply le_correct in E2;apply le_correct.
    rewrite <-simple_associativity, E2. trivial.
  Qed.
End join_sl_order_alt.

Definition default_meet_sl_le `{IsMeetSemiLattice L} : Le L :=  fun x y => x ⊓ y = x.

Section meet_sl_order_alt.
  Context `{IsMeetSemiLattice L} `{Le L} `{is_mere_relation L le}
    (le_correct : forall x y, x ≤ y <-> x ⊓ y = x).

  Lemma alt_Build_MeetSemiLatticeOrder : MeetSemiLatticeOrder (≤).
  Proof.
  repeat split.
  - apply _.
  - apply _.
  - intros ?. apply le_correct. apply (idempotency _ _).
  - intros ? ? ? E1 E2.
    apply le_correct in E1;apply le_correct in E2;apply le_correct.
    rewrite <-E1, <-simple_associativity, E2.
    reflexivity.
  - intros ? ? E1 E2.
    apply le_correct in E1;apply le_correct in E2.
    rewrite <-E2, (commutativity (f:=meet)).
    apply symmetry,E1.
  - intros ? ?. apply le_correct.
    rewrite (commutativity (f:=meet)), simple_associativity, (idempotency _ _).
    reflexivity.
  - intros ? ?. apply le_correct.
    rewrite <-simple_associativity, (idempotency _ _).
    reflexivity.
  - intros ? ? ? E1 E2.
    apply le_correct in E1;apply le_correct in E2;apply le_correct.
    rewrite associativity, E1.
    trivial.
  Qed.
End meet_sl_order_alt.

Section join_order_preserving.
  Context `{JoinSemiLatticeOrder L} `{JoinSemiLatticeOrder K} (f : L -> K)
    `{!IsJoinPreserving f}.

  Lemma join_sl_mor_preserving: OrderPreserving f.
  Proof.
  intros x y E.
  apply join_sl_le_spec in E. apply join_sl_le_spec.
  rewrite <-preserves_join.
  apply ap, E.
  Qed.

  Lemma join_sl_mor_reflecting `{!IsInjective f}: OrderReflecting f.
  Proof.
  intros x y E.
  apply join_sl_le_spec in E. apply join_sl_le_spec.
  rewrite <-preserves_join in E.
  apply (injective f). assumption.
  Qed.
End join_order_preserving.

Section meet_order_preserving.
  Context `{MeetSemiLatticeOrder L} `{MeetSemiLatticeOrder K} (f : L -> K)
    `{!IsMeetPreserving f}.

  Lemma meet_sl_mor_preserving: OrderPreserving f.
  Proof.
  intros x y E.
  apply meet_sl_le_spec in E. apply meet_sl_le_spec.
  rewrite <-preserves_meet.
  apply ap, E.
  Qed.

  Lemma meet_sl_mor_reflecting `{!IsInjective f}: OrderReflecting f.
  Proof.
  intros x y E.
  apply meet_sl_le_spec in E. apply meet_sl_le_spec.
  rewrite <-preserves_meet in E.
  apply (injective f). assumption.
  Qed.
End meet_order_preserving.

Section order_preserving_join_sl_mor.
  Context `{JoinSemiLatticeOrder L} `{JoinSemiLatticeOrder K}
    `{!TotalOrder (_ : Le L)} `{!TotalOrder (_ : Le K)}
    `{!OrderPreserving (f : L -> K)}.

  Lemma order_preserving_join_sl_mor: IsJoinPreserving f.
  Proof.
  intros x y. case (total (≤) x y); intros E.
  - change (f (join x y) = join (f x) (f y)).
    rewrite (join_r _ _ E),join_r;trivial.
    apply (order_preserving _). trivial.
  - change (f (join x y) = join (f x) (f y)).
    rewrite 2!join_l; trivial. apply (order_preserving _). trivial.
  Qed.
End order_preserving_join_sl_mor.

Section order_preserving_meet_sl_mor.
  Context `{MeetSemiLatticeOrder L} `{MeetSemiLatticeOrder K}
    `{!TotalOrder (_ : Le L)} `{!TotalOrder (_ : Le K)}
    `{!OrderPreserving (f : L -> K)}.

  Lemma order_preserving_meet_sl_mor: IsSemiGroupPreserving f.
  Proof.
  intros x y. case (total (≤) x y); intros E.
  - change (f (meet x y) = meet (f x) (f y)).
    rewrite 2!meet_l;trivial.
    apply (order_preserving _). trivial.
  - change (f (meet x y) = meet (f x) (f y)).
    rewrite 2!meet_r; trivial.
    apply (order_preserving _). trivial.
  Qed.
End order_preserving_meet_sl_mor.

Section strict_ordered_field.

  Generalizable Variables Lle Llt Lmeet Ljoin Lapart.
  Context `{@LatticeOrder L Lle Lmeet Ljoin}.
  Context `{@FullPseudoOrder L Lapart Lle Llt}.

  Lemma join_lt_l_l x y z : z < x -> z < x ⊔ y.
  Proof.
    intros ltzx.
    refine (lt_le_trans z x _ _ _); try assumption.
    apply join_ub_l.
  Qed.

  Lemma join_lt_l_r x y z : z < y -> z < x ⊔ y.
  Proof.
    intros ltzy.
    refine (lt_le_trans z y _ _ _); try assumption.
    apply join_ub_r.
  Qed.

  Lemma join_lt_r x y z : x < z -> y < z -> x ⊔ y < z.
  Proof.
    intros ltxz ltyz.
    set (disj := cotransitive ltxz (x ⊔ y)).
    refine (Trunc_rec _ disj); intros [ltxxy|ltxyz].
    - set (disj' := cotransitive ltyz (x ⊔ y)).
      refine (Trunc_rec _ disj'); intros [ltyxy|ltxyz].
      + assert (ineqx : ~ x ⊔ y = x).
        {
          apply lt_ne_flip; assumption.
        }
        assert (nleyx : ~ y ≤ x)
          by exact (not_contrapositive (join_l x y) ineqx).
        assert (lexy : x ≤ y).
        {
          apply le_iff_not_lt_flip.
          intros ltyx.
          refine (nleyx (lt_le _ _ _)).
        }
        assert (ineqy : ~ x ⊔ y = y).
        {
          apply lt_ne_flip; assumption.
        }
        assert (nlexy : ~ x ≤ y)
          by exact (not_contrapositive (join_r x y) ineqy).
        assert (leyx : y ≤ x).
        {
          apply le_iff_not_lt_flip.
          intros ltxy.
          refine (nlexy (lt_le _ _ _)).
        }
        assert (eqxy : x = y)
          by refine (antisymmetry _ _ _ lexy leyx).
        rewrite <- eqxy in ineqx.
        destruct (ineqx (join_idempotent x)).
      + assumption.
    - assumption.
  Qed.

  Lemma meet_lt_r_l x y z : x < z -> x  ⊓ y < z.
  Proof.
    intros ltxz.
    refine (le_lt_trans _ x _ _ _); try assumption.
    apply meet_lb_l.
  Qed.

  Lemma meet_lt_r_r x y z : y < z -> x  ⊓ y < z.
  Proof.
    intros ltyz.
    refine (le_lt_trans _ y _ _ _); try assumption.
    apply meet_lb_r.
  Qed.

  Lemma meet_lt_l x y z : x < y -> x < z -> x < y ⊓ z.
  Proof.
    intros ltxy ltxz.
    set (disj := cotransitive ltxy (y ⊓ z)).
    refine (Trunc_rec _ disj); intros [ltxyy|ltyzy].
    - assumption.
    - set (disj' := cotransitive ltxz (y ⊓ z)).
      refine (Trunc_rec _ disj'); intros [ltxyz|ltyzz].
      + assumption.
      + assert (ineqy : ~ y ⊓ z = y).
        {
          apply lt_ne; assumption.
        }
        assert (nleyz : ~ y ≤ z)
          by exact (not_contrapositive (meet_l y z) ineqy).
        assert (lezy : z ≤ y).
        {
          apply le_iff_not_lt_flip.
          intros ltzy.
          refine (nleyz (lt_le _ _ _)).
        }
        assert (ineqz : ~ y ⊓ z = z).
        {
          apply lt_ne; assumption.
        }
        assert (nlezy : ~ z ≤ y)
          by exact (not_contrapositive (meet_r y z) ineqz).
        assert (leyz : y ≤ z).
        {
          apply le_iff_not_lt_flip.
          intros ltzy.
          refine (nlezy (lt_le _ _ _)).
        }
        assert (eqyz : y = z)
          by refine (antisymmetry _ _ _ leyz lezy).
        rewrite <- eqyz in ineqy.
        destruct (ineqy (meet_idempotent y)).
  Qed.


End strict_ordered_field.
