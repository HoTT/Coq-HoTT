Require Import HoTT.Basics.Decidable HoTT.Types.Bool.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.theory.jections.

Section contents.
Context `{IsApart A}.

Lemma apart_ne x y : PropHolds (x ≶ y) → PropHolds (x ≠ y).
Proof.
unfold PropHolds.
intros ap e;revert ap.
apply tight_apart. assumption.
Qed.

Global Instance: ∀ x y : A, Stable (x = y).
Proof.
  intros x y. unfold Stable, DN.
  intros dn. apply tight_apart.
  intros ap. apply dn.
  apply apart_ne. assumption.
Qed.
End contents.

(* Due to bug #2528 *)
Hint Extern 3 (PropHolds (_ ≠ _)) => eapply @apart_ne : typeclass_instances.

Lemma projected_strong_setoid `{IsApart B} `{Apart A} `{is_mere_relation A apart}
  (f: A → B)
  (eq_correct : ∀ x y, x = y ↔ f x = f y)
  (apart_correct : ∀ x y, x ≶ y ↔ f x ≶ f y)
    : IsApart A.
Proof.
split.
- apply _.
- intros x y ap. apply apart_correct, symmetry, apart_correct.
  assumption.
- intros x y ap z.
  apply apart_correct in ap.
  destruct (cotransitive ap (f z));[left|right];apply apart_correct;assumption.
- intros x y;split.
  + intros nap. apply eq_correct. apply tight_apart.
    intros ap. apply nap. apply apart_correct;assumption.
  + intros e ap. apply apart_correct in ap;revert ap.
    apply tight_apart. apply eq_correct;assumption.
Qed.

Instance sg_apart_mere `{IsApart A} (P : A -> Type) : is_mere_relation (sig P) apart.
Proof.
intros. unfold apart,sig_apart. apply _.
Qed.

Instance sig_strong_setoid `{IsApart A} (P: A → Type) `{forall x, IsHProp (P x)}
  : IsApart (sig P).
Proof.
apply (projected_strong_setoid (@proj1_sig _ P)).
- intros. split;apply Sigma.equiv_path_sigma_hprop.
- intros;apply reflexivity.
Qed.

Section morphisms.
  Context `{Apart A} `{Apart B} `{Apart C}.

  Existing Instance strong_mor_a.
  Existing Instance strong_mor_b.

  Global Instance strong_injective_injective `{!StrongInjective (f : A → B)} :
    Injective f.
  Proof.
  pose proof (strong_injective_mor f).
  split.
  intros ? ? e.
  apply tight_apart. intros ap.
  apply tight_apart in e. apply e.
  apply strong_injective;auto.
  Qed.

  (* If a morphism satisfies the binary strong extensionality property, it is
    strongly extensional in both coordinates. *)
  Global Instance strong_setoid_morphism_1 `{!StrongBinaryMorphism (f : A → B → C)} :
    ∀ z, StrongMorphism (f z).
  Proof.
  pose proof (strong_binary_mor_a f).
  pose proof (strong_binary_mor_b f).
  pose proof (strong_binary_mor_c f).
  intros z.
  split; try apply _.
  intros x y E.
  destruct (strong_binary_extensionality f z x z y); trivial.
  destruct (irreflexivity (≶) z). assumption.
  Qed.

  Global Instance strong_setoid_morphism_unary_2 `{!StrongBinaryMorphism (f : A → B → C)} :
    ∀ z, StrongMorphism (λ x, f x z).
  Proof.
  pose proof (strong_binary_mor_a f).
  pose proof (strong_binary_mor_b f).
  pose proof (strong_binary_mor_c f).
  intros z.
  split; try apply _.
  intros x y E.
  destruct (strong_binary_extensionality f x z y z); trivial.
  destruct (irreflexivity (≶) z);assumption.
  Qed.

  (* Conversely, if a morphism is strongly extensional in both coordinates, it
    satisfies the binary strong extensionality property. We don't make this an
    instance in order to avoid loops. *)
  Lemma strong_binary_setoid_morphism_both_coordinates
    `{!IsApart A} `{!IsApart B} `{!IsApart C} {f : A → B → C}
    `{∀ z, StrongMorphism (f z)} `{∀ z, StrongMorphism (λ x, f x z)}
     : StrongBinaryMorphism f.
  Proof.
  split; try apply _.
  intros x₁ y₁ x₂ y₂ E.
  destruct (cotransitive E (f x₂ y₁)).
  - left. apply (strong_extensionality (λ x, f x y₁));trivial.
  - right. apply (strong_extensionality (f x₂));trivial.
  Qed.

End morphisms.

Section more_morphisms.
  Context `{IsApart A} `{IsApart B}.

  Lemma strong_binary_setoid_morphism_commutative {f : A → A → B} `{!Commutative f}
    `{∀ z, StrongMorphism (f z)} : StrongBinaryMorphism f.
  Proof.
  apply @strong_binary_setoid_morphism_both_coordinates;try apply _.
  split; try apply _.
  intros x y.
  rewrite !(commutativity _ z).
  apply (strong_extensionality (f z)).
  Qed.
End more_morphisms.

Section default_apart.
  Context `{DecidablePaths A}.

  Instance default_apart : Apart A | 20
    := fun x y =>
      match decide (x = y) with
      | inl _ => false
      | inr _ => true
      end = true.
  Typeclasses Opaque default_apart.

  Global Instance default_apart_trivial : TrivialApart A (Aap:=default_apart).
  Proof.
  split.
  - unfold apart,default_apart. apply _.
  - intros x y;unfold apart,default_apart;split.
    + intros E. destruct (decide (x=y)).
      * destruct (false_ne_true E).
      * trivial.
    + intros E;destruct (decide (x=y)) as [e|_].
      * destruct (E e).
      * split.
  Qed.

End default_apart.

(* In case we have a decidable setoid, we can construct a strong setoid. Again
  we do not make this an instance as it will cause loops *)
Section dec_setoid.
  Context `{TrivialApart A} `{DecidablePaths A}.

  (* Not Global in order to avoid loops *)
  Instance ne_apart x y : PropHolds (x ≠ y) → PropHolds (x ≶ y).
  Proof.
  intros ap. apply trivial_apart.
  assumption.
  Qed.

  Instance dec_strong_setoid: IsApart A.
  Proof.
  split.
  - apply _.
  - intros x y ne.
    apply trivial_apart. apply trivial_apart in ne.
    intros e;apply ne,symmetry,e.
  - hnf. intros x y ne z.
    apply trivial_apart in ne.
    destruct (decide (x=z)) as [e|ne'];[destruct (decide (z=y)) as [e'|ne']|].
    + destruct ne. path_via z.
    + right. apply trivial_apart. assumption.
    + left.  apply trivial_apart. assumption.
  - intros x y;split.
    + intros nap.
      destruct (decide (x=y));auto.
      destruct nap. apply trivial_apart;trivial.
    + intros e.
      intros nap. apply trivial_apart in nap. auto.
  Qed.
End dec_setoid.

(* And a similar result for morphisms *)
Section dec_setoid_morphisms.
  Context `{IsApart A} `{!TrivialApart A} `{IsApart B}.

  Instance dec_strong_morphism (f : A → B) :
    StrongMorphism f.
  Proof.
  split; try apply _.
  intros x y E. apply trivial_apart.
  intros e.
  apply tight_apart in E;auto.
  Qed.

  Context `{!TrivialApart B}.

  Instance dec_strong_injective (f : A → B) `{!Injective f} :
    StrongInjective f.
  Proof.
  split; try apply _.
  intros x y.
  intros ap.
  apply trivial_apart in ap. apply trivial_apart. intros e.
  apply ap. apply (injective f). assumption.
  Qed.

  Context `{IsApart C}.

  Instance dec_strong_binary_morphism (f : A → B → C) :
    StrongBinaryMorphism f.
  Proof.
  split;try apply _.
  intros x1 y1 x2 y2 hap.
  destruct (cotransitive hap (f x2 y1)) as [h|h].
  - left. apply trivial_apart.
    intros e.
    apply tight_apart in h;auto.
    exact (ap (fun x => f x y1) e).
  - right. apply trivial_apart.
    intros e.
    apply tight_apart in h;auto.
  Qed.
End dec_setoid_morphisms.
