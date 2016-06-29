Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.Basics.Trunc.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.implementations.field_of_fractions
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields.

Global Instance slow_rat_dec `{Rationals Q} : DecidablePaths Q | 10.
Proof.
intros x y.
destruct (decide (rationals_to_frac Q (NatPair.Z nat) x =
  rationals_to_frac Q (NatPair.Z nat) y)) as [E|E];[left|right].
- apply (injective (rationals_to_frac Q (NatPair.Z nat))).
  trivial.
- intros E';apply E,ap,E'.
Qed.

Section another_integers.
  Context `{Rationals Q} `{Integers Z}.
(*   Add Ring Z : (stdlib_ring_theory Z). *)

  Notation ZtoQ := (integers_to_ring Z Q).
  Notation QtoFrac := (rationals_to_frac Q Z).

  Lemma rationals_decompose `{!SemiRingPreserving (f : Z → Q)} (x : Q) :
    merely (∃ num, ∃ den, den ≠ 0 ∧ x = f num / f den).
  Proof.
  assert (Eq : exists q, q = QtoFrac x);[econstructor;split|].
  destruct Eq as [q Eq].
  revert q x Eq.
  apply (FracField.F_ind (fun q => forall x, _ -> _)).
  intros [n d Ed] x Eq.
  apply tr. exists n, d.
  split;trivial.
  apply (injective QtoFrac).
  path_via (FracField.class
    {| Frac.num := n; Frac.den := d; Frac.den_ne_0 := Ed |}).
  rewrite preserves_mult, preserves_dec_recip.
  change (QtoFrac (f n)) with ((compose QtoFrac f) n);
  change (QtoFrac (f d)) with ((compose QtoFrac f) d).
  rewrite 2!(to_ring_unique_alt (QtoFrac ∘ f) (cast Z (FracField.F Z))).
  apply FracField.mult_num_den.
  Qed.

  Global Instance integers_to_rationals_injective `{!SemiRingPreserving (f: Z → Q)}
    : Injective f.
  Proof.
  intros x y E.
  apply (injective (integers_to_ring Z Q)).
  rewrite <-2!(to_ring_unique f). trivial.
  Qed.

  Lemma to_frac_inverse_respects : ∀ x y : Frac.Frac Z,
    Frac.equiv x y
    → ZtoQ (Frac.num x) / ZtoQ (Frac.den x)
      ≡ ZtoQ (Frac.num y) / ZtoQ (Frac.den y).
  Proof.
  intros [na da Ea] [nb db Eb] E.
  red in E;simpl in E.
  simpl.
  apply (injective QtoFrac).
  rewrite 2!(preserves_mult (f:=QtoFrac)),2!(preserves_dec_recip (f:=QtoFrac)).
  change ((QtoFrac ∘ ZtoQ) na / (QtoFrac ∘ ZtoQ) da =
    (QtoFrac ∘ ZtoQ) nb / (QtoFrac ∘ ZtoQ) db).
  rewrite !(to_ring_unique_alt (QtoFrac ∘ ZtoQ) (cast Z (FracField.F Z))).
  apply FracField.path.
  unfold Frac.dec_rec;simpl.
  destruct (decide_rel paths da 0) as [E1|E1];[destruct Ea;trivial|clear Ea].
  destruct (decide_rel paths db 0) as [E2|E2];[destruct Eb;trivial|clear Eb].
  red;simpl.
  rewrite !mult_1_r,!mult_1_l. trivial.
  Qed.

  Context `{f : Q → FracField.F Z} `{!SemiRingPreserving f}.

  Global Instance to_frac_inverse: Inverse f
    := FracField.F_rec _ to_frac_inverse_respects.

  Global Instance: Surjective f.
  Proof.
  red;apply path_forall. red.
  apply (FracField.F_ind _).
  intros [n d Ed].
  unfold compose,id,inverse;simpl.
  rewrite (preserves_mult (f:=f)),(preserves_dec_recip (f:=f)).
  change (f (ZtoQ n) / f (ZtoQ d)) with ((f ∘ ZtoQ) n / (f ∘ ZtoQ) d).
  rewrite !(to_ring_unique_alt (f ∘ ZtoQ) (cast Z (FracField.F Z))).
  symmetry. apply FracField.mult_num_den.
  Qed.

  (* Making this instance global results in loops *)
  Instance to_frac_bijective: Bijective f := {}.
  Global Instance to_frac_inverse_bijective : Bijective (f⁻¹) := _.
  Global Instance to_frac_inverse_morphism : SemiRingPreserving (f⁻¹) := {}.
End another_integers.

Lemma to_frac_unique `{Rationals Q} `{Integers Z} (f g : Q → FracField.F Z)
  `{!SemiRingPreserving f} `{!SemiRingPreserving g} :
  ∀ x, f x = g x.
Proof.
intros x.
apply (injective (g⁻¹)).
change (f⁻¹ (f ⁻¹ ⁻¹ x) = g⁻¹ (g⁻¹ ⁻¹ x)).
rewrite 2!(jections.surjective_applied _). trivial.
Qed.

Section rat_to_rat.
  Context Q1 Q2 `{Rationals Q1} `{Rationals Q2}.

  Definition rationals_to_rationals : Q1 -> Q2
    := (rationals_to_frac Q2 (NatPair.Z nat))⁻¹ ∘
    rationals_to_frac Q1 (NatPair.Z nat).
End rat_to_rat.
Hint Unfold rationals_to_rationals : typeclass_instances.

Section another_rationals.
  Context `{Rationals Q1} `{Rationals Q2}.

  Local Existing Instance to_frac_bijective.

  Global Instance: SemiRingPreserving (rationals_to_rationals Q1 Q2) := _.
  Global Instance: Bijective (rationals_to_rationals Q1 Q2) := _.
  Global Instance: Bijective (rationals_to_rationals Q2 Q1) := _.

  Instance: Bijective (rationals_to_frac Q1 (NatPair.Z nat)) := {}.

  Lemma to_rationals_involutive:
    ∀ x, rationals_to_rationals Q2 Q1 (rationals_to_rationals Q1 Q2 x) = x.
  Proof.
  intros x.
  unfold rationals_to_rationals, compose.
  rewrite (jections.surjective_applied _).
  apply (jections.bijective_applied _).
  Qed.

  Lemma to_rationals_unique (f : Q1 → Q2) `{!SemiRingPreserving f} :
    ∀ x, f x = rationals_to_rationals Q1 Q2 x.
  Proof.
  intros x.
  apply (injective (rationals_to_rationals Q2 Q1)).
  rewrite to_rationals_involutive.
  change ((rationals_to_frac Q1 (NatPair.Z nat)⁻¹)
    ((rationals_to_frac Q2 (NatPair.Z nat) ∘ f) x) = x).
  rewrite (to_frac_unique (rationals_to_frac Q2 (NatPair.Z nat) ∘ f)
    (rationals_to_frac Q1 (NatPair.Z nat))).
  apply (jections.bijective_applied _).
  Qed.
End another_rationals.

Lemma to_rationals_unique_alt `{Rationals Q1} `{Rationals Q2} (f g : Q1 → Q2)
  `{!SemiRingPreserving f} `{!SemiRingPreserving g} :
  ∀ x, f x = g x.
Proof.
intros x.
rewrite (to_rationals_unique f), (to_rationals_unique g).
trivial.
Qed.

Lemma morphisms_involutive `{Rationals Q1} `{Rationals Q2} (f : Q1 → Q2)
  (g : Q2 → Q1) `{!SemiRingPreserving f} `{!SemiRingPreserving g} :
  ∀ x, f (g x) = x.
Proof.
intros x.
rewrite (to_rationals_unique f), (to_rationals_unique g).
apply to_rationals_involutive.
Qed.

Global Instance injective_nats `{Rationals Q} `{Naturals N}
  `{!SemiRingPreserving (f : N → Q)} : Injective f.
Proof.
intros x y E.
apply (injective (naturals_to_semiring N (NatPair.Z nat))).
apply rationals_embed_ints.
rewrite 2!(naturals.to_semiring_unique_alt f
  (integers_to_ring (NatPair.Z nat) Q ∘ naturals_to_semiring N (NatPair.Z nat)))
  in E.
trivial.
Qed.

Section isomorphic_image_is_rationals.
  Context `{Rationals Q} `{DecField F}.
  Context (f : Q → F) `{!Inverse f} `{!Bijective f} `{!SemiRingPreserving f}.

  Instance iso_to_frac: RationalsToFrac F := λ Z _ _ _ _ _ _ _,
    rationals_to_frac Q Z ∘ f⁻¹.
  Hint Unfold iso_to_frac: typeclass_instances.

  Instance: Bijective (f⁻¹) := _.
  Instance: SemiRingPreserving (f⁻¹) := {}.

  Lemma iso_is_rationals: Rationals F.
  Proof.
  esplit;unfold rationals_to_frac;try apply _.
  intros;intros x y E.
  apply (injective (f ∘ integers_to_ring Z Q)).
  rewrite 2!(to_ring_unique (f ∘ integers_to_ring Z Q)).
  trivial.
  Qed.
End isomorphic_image_is_rationals.

Section alt_Build_Rationals.
  Context `{DecField F} `{Integers Z} (F_to_fracZ : F → FracField.F Z)
    `{!SemiRingPreserving F_to_fracZ} `{!Injective F_to_fracZ}.
  Context (Z_to_F : Z → F) `{!SemiRingPreserving Z_to_F} `{!Injective Z_to_F}.

  Lemma alt_to_frac_respects `{Integers B} : ∀ x y : Frac.Frac Z, Frac.equiv x y →
    FracField.class
    {|
    Frac.num := integers_to_ring Z B (Frac.num x);
    Frac.den := integers_to_ring Z B (Frac.den x);
    Frac.den_ne_0 := injective_ne_0 (Frac.den x) (Frac.den_ne_0 x) |}
  ≡ FracField.class
    {|
    Frac.num := integers_to_ring Z B (Frac.num y);
    Frac.den := integers_to_ring Z B (Frac.den y);
    Frac.den_ne_0 := injective_ne_0 (Frac.den y) (Frac.den_ne_0 y) |}.
  Proof.
  intros [na da Ea] [nb db Eb] E.
  red in E;simpl in E;simpl.
  apply FracField.path;red;simpl.
  rewrite <-2!preserves_mult. apply ap,E.
  Qed.

  Instance alt_to_frac: RationalsToFrac F.
  Proof.
  red. intros B ??????? x.
  eapply (FracField.F_rec (R:=Z)).
  - exact alt_to_frac_respects.
  - exact (F_to_fracZ x).
  Defined.

  Instance: ∀ `{Integers B}, SemiRingPreserving (rationals_to_frac F B).
  Proof.
  intros. unfold rationals_to_frac,alt_to_frac.
  repeat split;red.
  - intros.
    rewrite (preserves_plus (f:=F_to_fracZ)).
    generalize (F_to_fracZ x),(F_to_fracZ y);clear x y.
    apply (FracField.F_ind2 _).
    intros. simpl. apply FracField.path.
    red;simpl.
    repeat (rewrite <-(preserves_mult (f:=integers_to_ring Z B))
      || rewrite <-(preserves_plus (f:=integers_to_ring Z B))).
    split.
  - rewrite (preserves_0 (f:=F_to_fracZ)).
    simpl. apply FracField.path.
    red;simpl. rewrite (preserves_0 (f:=integers_to_ring Z B)).
    rewrite 2!mult_0_l;split.
  - intros;rewrite (preserves_mult (f:=F_to_fracZ)).
    generalize (F_to_fracZ x),(F_to_fracZ y);clear x y.
    apply (FracField.F_ind2 _).
    intros. simpl. apply FracField.path.
    red;simpl.
    repeat (rewrite <-(preserves_mult (f:=integers_to_ring Z B))
      || rewrite <-(preserves_plus (f:=integers_to_ring Z B))).
    split.
  - rewrite (preserves_1 (f:=F_to_fracZ)).
    simpl;apply FracField.path.
    red;simpl. rewrite mult_1_l,mult_1_r;split.
  Qed.

  Instance: ∀ `{Integers B}, Injective (rationals_to_frac F B).
  Proof.
  intros;intros x y E.
  unfold rationals_to_frac,alt_to_frac in E.
  destruct (quotient.quotient_surjective _ (F_to_fracZ x)) as [Ex _].
  apply (merely_destruct Ex);clear Ex;intros [X Ex].
  destruct (quotient.quotient_surjective _ (F_to_fracZ y)) as [Ey _].
  apply (merely_destruct Ey);clear Ey;intros [Y Ey].
  apply (injective F_to_fracZ).
  rewrite <-Ex,<-Ey in E;simpl in E;rewrite <-Ex,<-Ey.
  clear x y Ex Ey.
  apply FracField.classes_eq_related in E;red in E;simpl in E.
  rewrite <-2!preserves_mult in E.
  apply (injective (integers_to_ring Z B)) in E.
  apply FracField.path. exact E.
  Qed.

  Instance: ∀ `{Integers B}, Injective (integers_to_ring B F).
  Proof.
  intros;intros x y E.
  apply (injective (Z_to_F ∘ integers_to_ring B Z)).
  rewrite 2!(to_ring_unique (Z_to_F ∘ integers_to_ring B Z)).
  trivial.
  Qed.

  Lemma alt_Build_Rationals: Rationals F.
  Proof. esplit; intros; apply _. Qed.
End alt_Build_Rationals.
