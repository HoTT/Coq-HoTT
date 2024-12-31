Require Import
  HoTT.Basics.Decidable.
Require Import
  HoTT.Classes.interfaces.orders
  HoTT.Classes.implementations.peano_naturals
  HoTT.Classes.theory.rings
  HoTT.Classes.isomorphisms.rings.
Require Export
  HoTT.Classes.interfaces.naturals.

Generalizable Variables A N R SR f.

(* This grabs a coercion. *)
Import SemiRings.

Lemma to_semiring_unique `{Naturals N} `{IsSemiCRing SR} (f: N -> SR)
  `{!IsSemiRingPreserving f} x
  : f x = naturals_to_semiring N SR x.
Proof.
symmetry. apply naturals_initial.
Qed.

Lemma to_semiring_unique_alt `{Naturals N} `{IsSemiCRing SR} (f g: N -> SR)
  `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving g} x
  : f x = g x.
Proof.
rewrite (to_semiring_unique f), (to_semiring_unique g);reflexivity.
Qed.

Lemma to_semiring_involutive N `{Naturals N} N2 `{Naturals N2} x :
  naturals_to_semiring N2 N (naturals_to_semiring N N2 x) = x.
Proof.
change (Compose (naturals_to_semiring N2 N) (naturals_to_semiring N N2) x = id x).
apply to_semiring_unique_alt;apply _.
Qed.

Lemma morphisms_involutive `{Naturals N} `{IsSemiCRing R} (f : R -> N) (g : N -> R)
  `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving g} x : f (g x) = x.
Proof. exact (to_semiring_unique_alt (f ∘ g) id _). Qed.

Lemma to_semiring_twice `{Naturals N} `{IsSemiCRing R1} `{IsSemiCRing R2}
  (f : R1 -> R2) (g : N -> R1) (h : N -> R2)
  `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving g} `{!IsSemiRingPreserving h} x
  : f (g x) = h x.
Proof. exact (to_semiring_unique_alt (f ∘ g) h _). Qed.

Lemma to_semiring_self `{Naturals N} (f : N -> N) `{!IsSemiRingPreserving f} x
  : f x = x.
Proof. exact (to_semiring_unique_alt f id _). Qed.

Lemma to_semiring_injective `{Naturals N} `{IsSemiCRing A}
   (f: A -> N) (g: N -> A) `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving g}
   : IsInjective g.
Proof.
intros x y E.
change (id x = id y).
rewrite <-(to_semiring_twice f g id x), <-(to_semiring_twice f g id y).
apply ap,E.
Qed.

Global Instance naturals_to_naturals_injective `{Naturals N} `{Naturals N2}
  (f: N -> N2) `{!IsSemiRingPreserving f}
  : IsInjective f | 15.
Proof. exact (to_semiring_injective (naturals_to_semiring N2 N) _). Qed.

Section retract_is_nat.
  Context `{Naturals N} `{IsSemiCRing SR}
    {SRap : Apart SR} {SRle SRlt} `{!FullPseudoSemiRingOrder (A:=SR) SRle SRlt}.
  Context (f : N -> SR) `{!IsEquiv f}
    `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving (f^-1)}.

  (* If we make this an instance, instance resolution will loop *)
  Definition retract_is_nat_to_sr : NaturalsToSemiRing SR
    := fun R _ _ _ _ _ => naturals_to_semiring N R ∘ f^-1.

  Section for_another_semirings.
    Context `{IsSemiCRing R}.

    Instance: IsSemiRingPreserving (naturals_to_semiring N R ∘ f^-1) := {}.

    Context (h :  SR -> R) `{!IsSemiRingPreserving h}.

    Lemma same_morphism x : (naturals_to_semiring N R ∘ f^-1) x = h x.
    Proof.
    transitivity ((h ∘ (f ∘ f^-1)) x).
    - symmetry. apply (to_semiring_unique (h ∘ f)).
    - unfold Compose. apply ap, eisretr.
    Qed.
  End for_another_semirings.

  (* If we make this an instance, instance resolution will loop *)
  Lemma retract_is_nat : Naturals SR (U:=retract_is_nat_to_sr).
  Proof.
  split;try apply _.
  - unfold naturals_to_semiring, retract_is_nat_to_sr. apply _.
  - intros;apply same_morphism;apply _.
  Qed.
End retract_is_nat.

Section nat_to_nat_iso.

Context `{Naturals N1} `{Naturals N2}.

Global Instance nat_to_nat_equiv : IsEquiv (naturals_to_semiring N1 N2).
Proof.
apply Equivalences.isequiv_adjointify with (naturals_to_semiring N2 N1);
red;apply (to_semiring_involutive _ _).
Defined.

End nat_to_nat_iso.

Section contents.
Universe U.

(* {U U} because we do forall n : N, {id} n = nat_to_sr N N n *)
Context `{Funext} `{Univalence} {N : Type@{U} } `{Naturals@{U U U U U U U U} N}.

Lemma from_nat_stmt  (N':Type@{U}) `{Naturals@{U U U U U U U U} N'}
  : forall (P : SemiRings.Operations -> Type),
  P (SemiRings.BuildOperations N') -> P (SemiRings.BuildOperations N).
Proof.
apply SemiRings.iso_leibnitz with (naturals_to_semiring N' N);apply _.
Qed.

Section borrowed_from_nat.

  Lemma induction
    : forall (P: N -> Type),
    P 0 -> (forall n, P n -> P (1 + n)) -> forall n, P n.
  Proof.
  pose (Q := fun s : SemiRings.Operations =>
    forall P : s -> Type, P 0 -> (forall n, P n -> P (1 + n)) -> forall n, P n).
  change (Q (SemiRings.BuildOperations N)).
  apply (from_nat_stmt nat).
  unfold Q;clear Q.
  simpl.
  exact nat_induction.
  Qed.

  Lemma case : forall x : N, x = 0 |_| exists y : N, (x = 1 + y).
  Proof.
  refine (from_nat_stmt nat
    (fun s => forall x : s, x = 0 |_| exists y : s, x = 1 + y) _).
  simpl. intros [|x];eauto.
  Qed.

  Global Instance: Biinduction N.
  Proof.
  hnf. intros P E0 ES.
  apply induction;trivial.
  apply ES.
  Qed.

  Global Instance nat_plus_cancel_l : forall z : N, LeftCancellation (+) z.
  Proof.
  refine (from_nat_stmt@{i U}
    nat (fun s => forall z : s, LeftCancellation plus z) _).
  simpl. first [exact nat_plus_cancel_l@{U i}|exact nat_plus_cancel_l@{U}].
  Qed.

  Global Instance: forall z : N, RightCancellation (+) z.
  Proof. intro. apply (right_cancel_from_left (+)). Qed.

  Global Instance: forall z : N, PropHolds (z <> 0) -> LeftCancellation (.*.) z.
  Proof.
  refine (from_nat_stmt nat (fun s =>
    forall z : s, PropHolds (z <> 0) -> LeftCancellation mult z) _).
  simpl. apply nat_mult_cancel_l.
  Qed.

  Global Instance: forall z : N, PropHolds (z <> 0) -> RightCancellation (.*.) z.
  Proof. intros ? ?. apply (right_cancel_from_left (.*.)). Qed.

  Instance nat_nontrivial: PropHolds ((1:N) <> 0).
  Proof.
  refine (from_nat_stmt nat (fun s => PropHolds ((1:s) <> 0)) _).
  apply _.
  Qed.

  Instance nat_nontrivial_apart `{Apart N} `{!TrivialApart N} :
    PropHolds ((1:N) ≶ 0).
  Proof. apply apartness.ne_apart. solve_propholds. Qed.

  Lemma zero_sum : forall (x y : N), x + y = 0 -> x = 0 /\ y = 0.
  Proof.
  refine (from_nat_stmt nat
    (fun s => forall x y : s, x + y = 0 -> x = 0 /\ y = 0) _).
  simpl. apply plus_eq_zero.
  Qed.

  Lemma one_sum : forall (x y : N), x + y = 1 -> (x = 1 /\ y = 0) |_| (x = 0 /\ y = 1).
  Proof.
  refine (from_nat_stmt nat (fun s =>
    forall (x y : s), x + y = 1 -> (x = 1 /\ y = 0) |_| (x = 0 /\ y = 1)) _).
  simpl.
  intros [|x] [|y];auto.
  - intros E. rewrite add_S_l,add_0_r in E.
    apply S_inj in E. rewrite E.
    auto.
  - intros E.
    rewrite add_S_l,add_S_r in E.
    apply S_inj in E. destruct (S_neq_0 _ E).
  Qed.

  Global Instance: ZeroProduct N.
  Proof.
  refine (from_nat_stmt nat (fun s => ZeroProduct s) _).
  simpl. red. apply mult_eq_zero.
  Qed.
End borrowed_from_nat.

Lemma nat_1_plus_ne_0 x : 1 + x <> 0.
Proof.
intro E. destruct (zero_sum 1 x E). apply nat_nontrivial. trivial.
Qed.

Global Instance slow_naturals_dec : DecidablePaths N.
Proof.
apply decidablepaths_equiv with nat (naturals_to_semiring nat N);apply _.
Qed.

Section with_a_ring.
  Context `{IsCRing R} `{!IsSemiRingPreserving (f : N -> R)} `{!IsInjective f}.

  Lemma to_ring_zero_sum x y :
    -f x = f y -> x = 0 /\ y = 0.
  Proof.
  intros E. apply zero_sum, (injective f).
  rewrite rings.preserves_0, rings.preserves_plus, <-E.
  apply plus_negate_r.
  Qed.

  Lemma negate_to_ring x y :
    -f x = f y -> f x = f y.
  Proof.
  intros E. destruct (to_ring_zero_sum x y E) as [E2 E3].
  rewrite E2, E3. reflexivity.
  Qed.
End with_a_ring.
End contents.

(* Due to bug #2528 *)
#[export]
Hint Extern 6 (PropHolds (1 <> 0)) =>
  eapply @nat_nontrivial : typeclass_instances.
#[export]
Hint Extern 6 (PropHolds (1 ≶ 0)) =>
  eapply @nat_nontrivial_apart : typeclass_instances.
