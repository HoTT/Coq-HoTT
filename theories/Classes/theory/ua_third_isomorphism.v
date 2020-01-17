(** This file proves the third isomorphism theorem,
    [isomorphic_third_isomorphism]. *)
Require Import
  HoTT.Types.Universe
  HoTT.HIT.quotient
  HoTT.UnivalenceImpliesFunext
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.theory.ua_quotient_algebra
  HoTT.Classes.theory.ua_isomorphic
  HoTT.Classes.theory.ua_first_isomorphism.

Import algebra_notations quotient_algebra_notations isomorphic_notations.

(** This section defines the quotient [cong_quotient] of two
    congruences [Φ] and [Ψ], where [Ψ] is a subcongruence of [Φ].
    It is shown that [cong_quotient] is a congruence. *)

Section cong_quotient.
  Context
    `{Univalence}
    {σ : Signature} {A : Algebra σ}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
    (Ψ : ∀ s, Relation (A s)) `{!IsCongruence A Ψ}
    (subrel : ∀ (s : Sort σ) (x y : A s), Ψ s x y → Φ s x y).

  Definition cong_quotient (_ : ∀ s x y, Ψ s x y → Φ s x y)
    (s : Sort σ) (a b : (A/Ψ) s)
    := ∀ (x y : A s), in_class (Ψ s) a x → in_class (Ψ s) b y → Φ s x y.

  Global Instance equivalence_relation_quotient (s : Sort σ)
    : EquivRel (cong_quotient subrel s).
  Proof.
    constructor.
    - refine (quotient_ind_prop (Ψ s) _ _). intros x y z P Q.
      apply subrel.
      by transitivity x.
    - refine (quotient_ind_prop (Ψ s) _ _). intro x1.
      refine (quotient_ind_prop (Ψ s) _ _). intros x2 C y1 y2 P Q.
      symmetry.
      by apply C.
    - refine (quotient_ind_prop (Ψ s) _ _). intro x1.
      refine (quotient_ind_prop (Ψ s) _ _). intro x2.
      refine (quotient_ind_prop (Ψ s) _ _). intros x3 C D y1 y2 P Q.
      transitivity x2.
      + exact (C y1 x2 P (EquivRel_Reflexive x2)).
      + exact (D x2 y2 (EquivRel_Reflexive x2) Q).
  Defined.

  Lemma for_all_relation_quotient {w : list (Sort σ)} (a b : FamilyProd A w)
    : for_all_2_family_prod (A/Ψ) (A/Ψ) (cong_quotient subrel)
        (map_family_prod (λ s, class_of (Ψ s)) a)
        (map_family_prod (λ s, class_of (Ψ s)) b) →
      for_all_2_family_prod A A Φ a b.
  Proof.
    intro F. induction w; cbn in *.
    - constructor.
    - destruct a as [x a], b as [y b], F as [Q F].
      split.
      + apply Q; cbn; reflexivity.
      + by apply IHw.
  Qed.

  Global Instance ops_compatible_quotient
    : OpsCompatible (A/Ψ) (cong_quotient subrel).
  Proof.
    intros u.
    refine (quotient_ind_prop_family_prod A Ψ _ _). intro a.
    refine (quotient_ind_prop_family_prod A Ψ _ _). intro b.
    (* It should not be necessary to provide the explicit types: *)
    destruct (compute_op_quotient A Ψ u a
              : ap_operation (u^^A / Ψ)
                 (map_family_prod (λ s, class_of (Ψ s)) _) = _)^.
    destruct (compute_op_quotient A Ψ u b
              : ap_operation (u^^A / Ψ)
                 (map_family_prod (λ s, class_of (Ψ s)) _) = _)^.
    intros R x y P Q.
    apply subrel in P.
    apply subrel in Q.
    transitivity (ap_operation (u^^A) a).
    - by symmetry.
    - transitivity (ap_operation (u^^A) b); try assumption.
      apply (ops_compatible A Φ u).
      by apply for_all_relation_quotient.
  Defined.

  Global Instance is_congruence_quotient
    : IsCongruence (A/Ψ) (cong_quotient subrel)
    := BuildIsCongruence (A/Ψ) (cong_quotient subrel).

End cong_quotient.

Section third_isomorphism.
  Context
    `{Univalence}
    {σ : Signature} {A : Algebra σ}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
    (Ψ : ∀ s, Relation (A s)) `{!IsCongruence A Ψ}
    (subrel : ∀ (s : Sort σ) (x y : A s), Ψ s x y → Φ s x y).

  Lemma third_surjecton_well_def (s : Sort σ)
    (x y : A s) (P : Ψ s x y)
    : class_of (Φ s) x = class_of (Φ s) y.
  Proof.
    apply related_classes_eq. exact (subrel s x y P).
  Defined.

  Definition def_third_surjection (s : Sort σ) : (A/Ψ) s → (A/Φ) s
    := quotient_rec (Ψ s) (class_of (Φ s)) (third_surjecton_well_def s).

  Lemma oppreserving_third_surjection {w : SymbolType σ} (f : Operation A w)
    : ∀ (α : Operation (A/Φ) w) (Qα : ComputeOpQuotient A Φ f α)
        (β : Operation (A/Ψ) w) (Qβ : ComputeOpQuotient A Ψ f β),
      OpPreserving def_third_surjection β α.
  Proof.
    induction w.
    - refine (quotient_ind_prop (Φ t) _ _). intros α Qα.
      refine (quotient_ind_prop (Ψ t) _ _). intros β Qβ.
      apply related_classes_eq.
      transitivity f.
      + apply subrel. apply (classes_eq_related (Ψ t)). exact (Qβ tt).
      + apply (classes_eq_related (Φ t)). symmetry. exact (Qα tt).
    - intros α Qα β Qβ.
      refine (quotient_ind_prop (Ψ t) _ _).
      intro x.
      exact (IHw (f x) (α (class_of (Φ t) x)) (λ a, Qα (x,a))
               (β (class_of (Ψ t) x)) (λ a, Qβ (x,a))).
  Defined.

 Global Instance is_homomorphism_third_surjection
    : IsHomomorphism def_third_surjection.
  Proof.
    intro u.
    eapply oppreserving_third_surjection; apply compute_op_quotient.
  Defined.

  Definition hom_third_surjection : Homomorphism (A/Ψ) (A/Φ)
    := BuildHomomorphism def_third_surjection.

  Global Instance surjection_third_surjection (s : Sort σ)
    : IsSurjection (hom_third_surjection s).
  Proof.
    apply BuildIsSurjection.
    refine (quotient_ind_prop (Φ s) _ _).
    intro x.
    apply tr.
    by exists (class_of (Ψ s) x).
  Qed.

  Local Notation Θ := (cong_quotient Φ Ψ subrel).

  Lemma path_quotient_algebras_third_surjection
    : A/Ψ / cong_ker hom_third_surjection = A/Ψ / Θ.
  Proof.
    apply path_quotient_algebra_iff. intros s x y.
    split; generalize dependent y; generalize dependent x;
           refine (quotient_ind_prop (Ψ s) _ _); intro x;
           refine (quotient_ind_prop (Ψ s) _ _); intro y.
    - intros K x' y' Cx Cy.
      apply subrel in Cx. apply subrel in Cy.
      apply (classes_eq_related (Φ s)) in K.
      transitivity x.
      + by symmetry.
      + by transitivity y.
    - intro T.
      apply related_classes_eq.
      exact (T x y (EquivRel_Reflexive x) (EquivRel_Reflexive y)).
  Defined.

  Definition hom_third_isomorphism : Homomorphism (A/Ψ/Θ) (A/Φ)
    := transport (λ X, Homomorphism X (A/Φ))
          path_quotient_algebras_third_surjection
          (hom_first_isomorphism_surjection hom_third_surjection).

  Theorem is_isomorphism_third_isomorphism
    : IsIsomorphism hom_third_isomorphism.
  Proof.
    unfold hom_third_isomorphism.
    destruct path_quotient_algebras_third_surjection.
    exact _.
  Qed.

  Global Existing Instance is_isomorphism_third_isomorphism.

  (** The third isomorphism theorem. *)

  Corollary isomorphic_third_isomorphism : A/Ψ/Θ ≅ A/Φ.
  Proof.
    exact (BuildIsomorphic hom_third_isomorphism).
  Defined.

  Corollary id_third_isomorphism : A/Ψ/Θ = A/Φ.
  Proof.
    exact (id_isomorphic isomorphic_third_isomorphism).
  Defined.
End third_isomorphism.
