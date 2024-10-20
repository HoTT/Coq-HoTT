(** This file defines the kernel of a homomorphism [cong_ker], the
    image of a homomorphism [in_image_hom], and it proves the first
    isomorphism theorem [isomorphic_first_isomorphism]. The first
    identification theorem [id_first_isomorphism] follows. *)

Require Import
  Basics.Notations
  HSet
  Colimits.Quotient
  Classes.interfaces.canonical_names
  Classes.theory.ua_isomorphic
  Classes.theory.ua_subalgebra
  Classes.theory.ua_quotient_algebra.

Import
  algebra_notations
  quotient_algebra_notations
  subalgebra_notations
  isomorphic_notations.

(** The following section defines the kernel of a homomorphism
    [cong_ker], and shows that it is a congruence.*)

Section cong_ker.
  Context
    {σ : Signature} {A B : Algebra σ} `{IsHSetAlgebra B}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f}.

  Definition cong_ker (s : Sort σ) : Relation (A s)
    := λ (x y : A s), f s x = f s y.

(* Leave the following results about [cong_ker] opaque because they
   are h-props. *)

  Global Instance equiv_rel_ker (s : Sort σ)
    : EquivRel (cong_ker s).
  Proof.
    repeat constructor.
    - intros x y. exact inverse.
    - intros x y z. exact concat.
  Qed.

  Lemma path_ap_operation_ker_related {w : SymbolType σ}
    (β : Operation B w) (a b : FamilyProd A (dom_symboltype w))
    (R : for_all_2_family_prod A A cong_ker a b)
    : ap_operation β (map_family_prod f a)
      = ap_operation β (map_family_prod f b).
  Proof.
    induction w.
    - reflexivity.
    - destruct a as [x a], b as [y b], R as [r R].
      cbn. destruct r. by apply IHw.
  Qed.

  Global Instance ops_compatible_ker : OpsCompatible A cong_ker.
  Proof.
    intros u a b R.
    unfold cong_ker.
    destruct (path_homomorphism_ap_operation f u a)^.
    destruct (path_homomorphism_ap_operation f u b)^.
    by apply path_ap_operation_ker_related.
  Qed.

  Global Instance is_congruence_ker : IsCongruence A cong_ker
    := BuildIsCongruence A cong_ker.

End cong_ker.

(** The next section defines an "in image predicate", [in_image_hom].
    It gives rise to the homomorphic image of a homomorphism. *)

Section in_image_hom.
  Context
    `{Funext} {σ : Signature} {A B : Algebra σ}
    (f : ∀ s, A s → B s) {hom : IsHomomorphism f}.

  Definition in_image_hom (s : Sort σ) (y : B s) : HProp
    := merely (hfiber (f s) y).

  Lemma closed_under_op_in_image_hom {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) (P : OpPreserving f α β)
    : ClosedUnderOp B in_image_hom β.
  Proof.
    induction w.
    - exact (tr (α; P)).
    - intro y.
      refine (Trunc_rec _). intros [x p].
      apply (IHw (α x)).
      by destruct p.
  Qed.

  Lemma is_closed_under_ops_in_image_hom
    : IsClosedUnderOps B in_image_hom.
  Proof.
    intro u. eapply closed_under_op_in_image_hom, hom.
  Qed.

  Global Instance is_subalgebra_predicate_in_image_hom
    : IsSubalgebraPredicate B in_image_hom
    := BuildIsSubalgebraPredicate is_closed_under_ops_in_image_hom.
End in_image_hom.

(** The folowing section proves the first isomorphism theorem,
    [isomorphic_first_isomorphism] and the first identification
    theorem [id_first_isomorphism]. *)

Section first_isomorphism.
  Context
    `{Univalence} {σ} {A B : Algebra σ} `{IsHSetAlgebra B}
    (f : ∀ s, A s → B s) {hom : IsHomomorphism f}.

(** The homomorphism [def_first_isomorphism] is informally given by

<<
      def_first_isomorphism s (class_of _ x) := f s x.
>>
*)

  Definition def_first_isomorphism (s : Sort σ)
    : (A / cong_ker f) s → (B && in_image_hom f) s.
  Proof.
    refine (Quotient_rec (cong_ker f s) _ (λ x, (f s x; tr (x; idpath))) _).
    intros x y p.
    by apply path_sigma_hprop.
  Defined.

  Lemma oppreserving_first_isomorphism {w : SymbolType σ}
    (α : Operation A w)
    (β : Operation B w)
    (γ : Operation (A / cong_ker f) w)
    (C : ClosedUnderOp B (in_image_hom f) β)
    (P : OpPreserving f α β)
    (G : ComputeOpQuotient A (cong_ker f) α γ)
    : OpPreserving def_first_isomorphism γ
        (op_subalgebra B (in_image_hom f) β C).
  Proof.
    induction w.
    - apply path_sigma_hprop.
      generalize dependent γ.
      refine (Quotient_ind_hprop (cong_ker f t) _ _). intros x G.
      destruct P.
      apply (related_quotient_paths (cong_ker f t) _ _ (G tt)).
    - refine (Quotient_ind_hprop (cong_ker f t) _ _). intro x.
      apply (IHw (α x) (β (f t x)) (γ (class_of _ x))).
      + exact (P x).
      + intro a. exact (G (x,a)).
  Qed.

(* Leave [is_homomorphism_first_isomorphism] opaque because
   [IsHomomorphism] is an hprop when [B] is a set algebra. *)

  Global Instance is_homomorphism_first_isomorphism
    : IsHomomorphism def_first_isomorphism.
  Proof.
    intro u. apply (oppreserving_first_isomorphism u.#A).
    - apply hom.
    - apply compute_op_quotient.
  Qed.

  Definition hom_first_isomorphism
    : Homomorphism (A / cong_ker f) (B && in_image_hom f)
    := BuildHomomorphism def_first_isomorphism.

  Global Instance embedding_first_isomorphism (s : Sort σ)
    : IsEmbedding (hom_first_isomorphism s).
  Proof.
    apply isembedding_isinj_hset.
    refine (Quotient_ind_hprop (cong_ker f s) _ _). intro x.
    refine (Quotient_ind_hprop (cong_ker f s) _ _). intros y p.
    apply qglue.
    exact (p..1).
  Qed.

  Global Instance surjection_first_isomorphism (s : Sort σ)
    : IsSurjection (hom_first_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    intros [x M].
    refine (Trunc_rec _ M). intros [y Y].
    apply tr.
    exists (class_of _ y).
    by apply path_sigma_hprop.
  Qed.

  Global Instance is_isomorphism_first_isomorphism
    : IsIsomorphism hom_first_isomorphism.
  Proof.
    intro s. apply isequiv_surj_emb; exact _.
  Qed.

  Theorem isomorphic_first_isomorphism
    : A / cong_ker f ≅ B && in_image_hom f.
  Proof.
    exact (BuildIsomorphic def_first_isomorphism).
  Defined.

(* The first identification theorem [id_first_isomorphism] is an
   h-prop, so we can leave it opaque. *)

  Corollary id_first_isomorphism : A / cong_ker f = B && in_image_hom f.
  Proof.
    exact (id_isomorphic isomorphic_first_isomorphism).
  Qed.
End first_isomorphism.

(** The next section gives a specialization of the first isomorphism
    theorem, where the homomorphism is surjective. *)

Section first_isomorphism_surjection.
  Context
    `{Univalence} {σ} {A B : Algebra σ} `{IsHSetAlgebra B}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f} {S : ∀ s, IsSurjection (f s)}.

  Global Instance is_isomorphism_inc_first_isomorphism_surjection
    : IsIsomorphism (hom_inc_subalgebra B (in_image_hom f)).
  Proof.
    apply is_isomorphism_inc_improper_subalgebra.
    intros s x; cbn.
    apply center, S.
  Qed.

(** The homomorphism [hom_first_isomorphism_surjection] is the
    composition of two isomorphisms, so it is an isomorphism. *)

  Definition hom_first_isomorphism_surjection
    : Homomorphism (A / cong_ker f) B
    := hom_compose
          (hom_inc_subalgebra B (in_image_hom f))
          (hom_first_isomorphism f).

  Theorem isomorphic_first_isomorphism_surjection : A / cong_ker f ≅ B.
  Proof.
    exact (BuildIsomorphic hom_first_isomorphism_surjection).
  Defined.

  Corollary id_first_isomorphism_surjection : (A / cong_ker f) = B.
  Proof.
    exact (id_isomorphic isomorphic_first_isomorphism_surjection).
  Qed.
End first_isomorphism_surjection.

(** The next section specializes the first isomorphism theorem to the
    case where the homomorphism is injective. It proves that an
    injective homomorphism is an isomorphism between its domain
    and its image. *)

Section first_isomorphism_inj.
  Context
    `{Univalence} {σ} {A B : Algebra σ} `{IsHSetAlgebra B}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f} (inj : ∀ s, IsInjective (f s)).

  Global Instance is_isomorphism_quotient_first_isomorphism_inj
    : IsIsomorphism (hom_quotient (cong_ker f)).
  Proof.
    apply is_isomorphism_quotient. intros s x y p. apply inj, p.
  Qed.

(** The homomorphism [hom_first_isomorphism_inj] is the
    composition of two isomorphisms, so it is an isomorphism. *)

  Definition hom_first_isomorphism_inj
    : Homomorphism A (B && in_image_hom f)
    := hom_compose
          (hom_first_isomorphism f)
          (hom_quotient (cong_ker f)).

  Definition isomorphic_first_isomorphism_inj : A ≅ B && in_image_hom f
    := BuildIsomorphic hom_first_isomorphism_inj.

  Definition id_first_isomorphism_inj : A = B && in_image_hom f
    := id_isomorphic isomorphic_first_isomorphism_inj.

End first_isomorphism_inj.
