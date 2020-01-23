(** The second isomorphism theorem [isomorphic_second_isomorphism]. *)

Require Import
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.HSet
  HoTT.HIT.quotient
  HoTT.UnivalenceImpliesFunext
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.theory.ua_isomorphic
  HoTT.Classes.theory.ua_subalgebra
  HoTT.Classes.theory.ua_quotient_algebra.

Import
  algebra_notations
  quotient_algebra_notations
  subalgebra_notations
  isomorphic_notations.

Local Notation i := (hom_inc_subalgebra _ _).

(** This section defines [cong_trace] and proves that it is a
    congruence, the restriction of a congruence to a subalgebra. *)

Section cong_trace.
  Context
    {σ : Signature} {A : Algebra σ}
    (P : ∀ s, A s → Type) `{!IsSubalgebraPredicate A P}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

  Definition cong_trace (s : Sort σ) (x : (A&P) s) (y : (A&P) s)
    := Φ s (i s x) (i s y).

  Global Instance equiv_rel_trace_congruence (s : Sort σ)
    : EquivRel (cong_trace s).
  Proof.
    unfold cong_trace.
    constructor.
    - intros [y Y]. reflexivity.
    - intros [y1 Y1] [y2 Y2] S. by symmetry.
    - intros [y1 Y1] [y2 Y2] [y3 Y3] S T. by transitivity y2.
  Qed.

  Lemma for_all_2_family_prod_trace_congruence {w : SymbolType σ}
    (a b : FamilyProd (A&P) (dom_symboltype w))
    (R : for_all_2_family_prod (A&P) (A&P) cong_trace a b)
    : for_all_2_family_prod A A Φ
        (map_family_prod i a) (map_family_prod i b).
  Proof with try assumption.
    induction w...
    destruct a as [x a], b as [y b], R as [C R].
    split...
    apply IHw...
  Qed.

  Global Instance ops_compatible_trace_trace
    : OpsCompatible (A&P) cong_trace.
  Proof.
    intros u a b R.
    refine (transport (λ X, Φ _ X _)
              (path_homomorphism_ap_operation i u a)^ _).
    refine (transport (λ X, Φ _ _ X)
              (path_homomorphism_ap_operation i u b)^ _).
    apply (ops_compatible_cong A Φ).
    exact (for_all_2_family_prod_trace_congruence a b R).
  Qed.

  Global Instance is_congruence_trace : IsCongruence (A&P) cong_trace.
  Proof.
    apply (@BuildIsCongruence _ (A&P) cong_trace);
      [intros; apply (is_mere_relation_cong A Φ) | exact _ ..].
  Qed.
End cong_trace.

(** The following section defines the [is_subalgebra_class] subalgebra
    predicate, which induces a subalgebra of [A/Φ]. *)

Section is_subalgebra_class.
  Context `{Univalence}
    {σ : Signature} {A : Algebra σ}
    (P : ∀ s, A s → Type) `{!IsSubalgebraPredicate A P}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

  Definition is_subalgebra_class (s : Sort σ) (x : (A/Φ) s) : hProp
    := hexists (λ (y : (A&P) s), in_class (Φ s) x (i s y)).

  Lemma op_closed_subalgebra_is_subalgebra_class {w : SymbolType σ}
    (γ : Operation (A/Φ) w)
    (α : Operation A w)
    (Q : ComputeOpQuotient A Φ α γ)
    (C : ClosedUnderOp A P α)
    : ClosedUnderOp (A/Φ) is_subalgebra_class γ.
  Proof.
    induction w.
    - specialize (Q tt). apply tr.
      exists (α; C).
      cbn in Q. destruct Q^.
      exact (EquivRel_Reflexive α).
    - refine (quotient_ind_prop (Φ t) _ _). intro x.
      refine (Trunc_rec _).
      intros [y R].
      apply (IHw (γ (class_of (Φ t) x)) (α (i t y))).
      + intro a.
        destruct (related_classes_eq (Φ t) R)^.
        apply (Q (i t y,a)).
      + apply C. exact y.2.
  Qed.

  Definition is_closed_under_ops_is_subalgebra_class
    : IsClosedUnderOps (A/Φ) is_subalgebra_class.
  Proof.
    intro u.
    eapply op_closed_subalgebra_is_subalgebra_class.
    - apply compute_op_quotient.
    - apply is_closed_under_ops_subalgebra_predicate. exact _.
  Qed.

  Global Instance is_subalgebra_predicate_is_subalgebra_class
    : IsSubalgebraPredicate (A/Φ) is_subalgebra_class.
  Proof.
    apply BuildIsSubalgebraPredicate.
    apply is_closed_under_ops_is_subalgebra_class.
  Qed.
End is_subalgebra_class.

(** The next section proves the second isomorphism theorem,

    <<
      (A&P) / (cong_trace P Φ) ≅ (A/Φ) & (is_subalgebra_class P Φ).
    >>
*)

(* There is an alternative proof using the first isomorphism theorem,
   but the direct proof below seems simpler in HoTT. *)

Section second_isomorphism.
  Context `{Univalence}
    {σ : Signature} (A : Algebra σ)
    (P : ∀ s, A s → Type) `{!IsSubalgebraPredicate A P}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

  Local Notation Ψ := (cong_trace P Φ).

  Local Notation Q := (is_subalgebra_class P Φ).

  Definition def_second_isomorphism (s : Sort σ)
    : ((A&P) / Ψ) s → ((A/Φ) & Q) s
    := quotient_rec (Ψ s)
        (λ (x : (A&P) s),
         (class_of (Φ s) (i s x); tr (x; EquivRel_Reflexive x)))
        (λ (x y : (A&P) s) (T : Ψ s x y),
         path_sigma_hprop (class_of (Φ s) (i s x); _)
           (class_of (Φ s) (i s y); _) (related_classes_eq (Φ s) T)).

  Lemma oppreserving_second_isomorphism {w : SymbolType σ}
    (α : Operation A w) (γ : Operation (A/Φ) w)
    (ζ : Operation ((A&P) / Ψ) w) (CA : ClosedUnderOp (A/Φ) Q γ)
    (CB : ClosedUnderOp A P α) (QA : ComputeOpQuotient A Φ α γ)
    (QB : ComputeOpQuotient (A&P) Ψ (op_subalgebra A P α CB) ζ)
    : OpPreserving def_second_isomorphism ζ (op_subalgebra (A/Φ) Q γ CA).
  Proof.
    unfold ComputeOpQuotient in *.
    induction w; cbn in *.
    - apply path_sigma_hprop.
      cbn. destruct (QB tt)^, (QA tt)^.
      by apply related_classes_eq.
    - refine (quotient_ind_prop (Ψ t) _ _). intro x.
      apply (IHw (α (i t x)) (γ (class_of (Φ t) (i t x)))
              (ζ (class_of (Ψ t) x))
              (CA (class_of (Φ t) (i t x)) (tr (x; _)))
              (CB (i t x) x.2)).
      + intro a. exact (QA (i t x, a)).
      + intro a. exact (QB (x, a)).
  Defined.

  Global Instance is_homomorphism_second_isomorphism
    : IsHomomorphism def_second_isomorphism.
  Proof.
    intro u.
    eapply oppreserving_second_isomorphism.
    - apply (compute_op_quotient A).
    - apply (compute_op_quotient (A&P)).
  Defined.

  Definition hom_second_isomorphism
    : Homomorphism ((A&P) / Ψ) ((A/Φ) & Q)
    := BuildHomomorphism def_second_isomorphism.

  Global Instance embedding_second_isomorphism (s : Sort σ)
    : IsEmbedding (hom_second_isomorphism s).
  Proof.
    apply isembedding_isinj_hset.
    refine (quotient_ind_prop (Ψ s) _ _). intro x.
    refine (quotient_ind_prop (Ψ s) _ _). intros y p.
    apply related_classes_eq.
    exact (classes_eq_related (Φ s) (i s x) (i s y) (p..1)).
  Qed.

  Global Instance surjection_second_isomorphism (s : Sort σ)
    : IsSurjection (hom_second_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    intros [y S].
    generalize dependent S.
    generalize dependent y.
    refine (quotient_ind_prop (Φ s) _ _). intros y S.
    refine (Trunc_rec _ S). intros [y' S']. apply tr.
    exists (class_of _ y').
    apply path_sigma_hprop.
    by apply related_classes_eq.
  Qed.

  Theorem is_isomorphism_second_isomorphism
    : IsIsomorphism hom_second_isomorphism.
  Proof.
    intro s. apply isequiv_surj_emb; exact _.
  Qed.

  Global Existing Instance is_isomorphism_second_isomorphism.

  Theorem isomorphic_second_isomorphism : (A&P) / Ψ ≅ (A/Φ) & Q.
  Proof.
    exact (BuildIsomorphic def_second_isomorphism).
  Defined.

  Corollary id_second_isomorphism : (A&P) / Ψ = (A/Φ) & Q.
  Proof.
    exact (id_isomorphic isomorphic_second_isomorphism).
  Defined.
End second_isomorphism.
