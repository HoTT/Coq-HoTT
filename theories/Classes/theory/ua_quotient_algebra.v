Require Export HoTT.Classes.interfaces.ua_congruence.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HProp
  HoTT.HSet
  HoTT.HIT.quotient
  HoTT.Truncations
  HoTT.UnivalenceImpliesFunext
  HoTT.Classes.implementations.list
  HoTT.Classes.theory.ua_homomorphism.

Import algebra_notations ne_list.notations.

Section quotient_algebra.
  Context
    `{Funext} {σ : Signature} (A : Algebra σ)
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

(** The quotient algebra carriers is the family of set-quotients
    induced by [Φ]. *)

  Definition carriers_quotient_algebra : Carriers σ
    := λ s, quotient (Φ s).

(** Specialization of [quotient_ind_prop]. Suppose
    [P : FamilyProd carriers_quotient_algebra w → Type] and
    [∀ a, IsHProp (P a)]. To show that [P a] holds for all [a :
    FamilyProd carriers_quotient_algebra w], it is sufficient to show
    that [P (class_of _ x1, ..., class_of _ xn, tt)] holds for all
    [(x1, ..., xn, tt) : FamilyProd A w]. *)

  Fixpoint quotient_ind_prop_family_prod {w : list (Sort σ)}
    : ∀ (P : FamilyProd carriers_quotient_algebra w → Type)
        `{!∀ a, IsHProp (P a)}
        (dclass : ∀ x, P (map_family_prod (λ s, class_of (Φ s)) x))
        (a : FamilyProd carriers_quotient_algebra w), P a
    := match w with
       | nil => λ P _ dclass 'tt, dclass tt
       | s :: w' => λ P _ dclass a,
         quotient_ind_prop (Φ s) (λ a, ∀ b, P (a,b))
           (λ a, quotient_ind_prop_family_prod
                  (λ c, P (class_of (Φ s) a, c)) (λ c, dclass (a, c)))
           (fst a) (snd a)
       end.

(** Let [f : Operation A w], [g : Operation carriers_quotient_algebra w].
    If [g] is the quotient algebra operation induced by [f], then we want
    [ComputeOpQuotient f g] to hold, since then

    <<
      β (class_of _ a1, class_of _ a2, ..., class_of _ an)
      = class_of _ (α (a1, a2, ..., an)),
    >>

    where [α] is the uncurried [f] operation and [β] is the uncurried
    [g] operation. *)

  Definition ComputeOpQuotient {w : SymbolType σ}
    (f : Operation A w) (g : Operation carriers_quotient_algebra w)
    := ∀ (a : FamilyProd A (dom_symboltype w)),
         ap_operation g (map_family_prod (λ s, class_of (Φ s)) a)
         = class_of (Φ (cod_symboltype w)) (ap_operation f a).

  Local Notation QuotOp w :=
    (∀ (f : Operation A w),
     OpCompatible A Φ f →
     ∃ g : Operation carriers_quotient_algebra w,
     ComputeOpQuotient f g) (only parsing).

  Local Notation op_qalg_cons q f P x :=
    (q _ (f x) (op_compatible_cons Φ _ _ f x P)).1 (only parsing).

  Lemma op_quotient_algebra_well_def
    (q : ∀ (w : SymbolType σ), QuotOp w)
    (s : Sort σ) (w : SymbolType σ) (f : Operation A (s ::: w))
    (P : OpCompatible A Φ f) (x y : A s) (C : Φ s x y)
    : op_qalg_cons q f P x = op_qalg_cons q f P y.
  Proof.
    apply (@path_forall_ap_operation _ σ).
    apply quotient_ind_prop_family_prod; try exact _.
    intro a.
    destruct (q _ _ (op_compatible_cons Φ s w f x P)) as [g1 P1].
    destruct (q _ _ (op_compatible_cons Φ s w f y P)) as [g2 P2].
    refine ((P1 a) @ _ @ (P2 a)^).
    apply related_classes_eq.
    exact (P (x,a) (y,a) (C, reflexive_for_all_2_family_prod A Φ a)).
  Defined.

(* Given an operation [f : A s1 → A s2 → ... A sn → A t] and a witness
   [C : OpCompatible A Φ f], then [op_quotient_algebra f C] is a
   dependent pair with first component an operation [g : Q s1 → Q s2
   → ... Q sn → Q t], where [Q := carriers_quotient_algebra], and
   second component a proof of [ComputeOpQuotient f g]. The first
   component [g] is the quotient algebra operation corresponding to [f].
   The second component proof of [ComputeOpQuotient f g] is passed to
   the [op_quotient_algebra_well_def] lemma, which is used to show that
   the quotient algebra operation [g] is well defined, i.e. that

   <<
    Φ s1 x1 y1 ∧ Φ s2 x2 y2 ∧ ... ∧ Φ sn xn yn
   >>

   implies

   <<
    g (class_of _ x1) (class_of _ x2) ... (class_of _ xn)
    = g (class_of _ y1) (class_of _ y2) ... (class_of _ yn).
   >>
*)

  Fixpoint op_quotient_algebra {w : SymbolType σ} : QuotOp w.
  Proof. refine (
      match w return QuotOp w with
      | [:s:] => λ (f : A s) P, (class_of (Φ s) f; λ a, idpath)
      | s ::: w' => λ (f : A s → Operation A w') P,
        (quotient_rec (Φ s)
          (λ (x : A s), op_qalg_cons op_quotient_algebra f P x)
          (op_quotient_algebra_well_def op_quotient_algebra s w' f P)
        ; _)
      end
    ).
    intros [x a].
    apply (op_quotient_algebra w' (f x) (op_compatible_cons Φ s w' f x P)).
  Defined.

  Definition ops_quotient_algebra (u : Symbol σ)
    : Operation carriers_quotient_algebra (σ u)
    := (op_quotient_algebra (u^^A) (ops_compatible_cong A Φ u)).1.

(** Definition of quotient algebra. See Lemma [compute_op_quotient]
    below for the computation rule of quotient algebra operations. *)

  Definition QuotientAlgebra : Algebra σ
    := BuildAlgebra carriers_quotient_algebra ops_quotient_algebra.

(** The quotient algebra carriers are always sets. *)

  Global Instance hset_quotient_algebra
    : IsHSetAlgebra QuotientAlgebra.
  Proof.
    intro s. exact _.
  Qed.

(** The following lemma gives the computation rule for the quotient
    algebra operations. It says that for
    [(a1, a2, ..., an) : A s1 * A s2 * ... * A sn],

    <<
      β (class_of _ a1, class_of _ a2, ..., class_of _ an)
      = class_of _ (α (a1, a2, ..., an))
    >>

    where [α] is the uncurried [u^^A] operation and [β] is the
    uncurried [u^^QuotientAlgebra] operation. *)

  Lemma compute_op_quotient (u : Symbol σ)
    : ComputeOpQuotient (u^^A) (u^^QuotientAlgebra).
  Proof.
    apply op_quotient_algebra.
  Defined.
End quotient_algebra.

Module quotient_algebra_notations.
  Global Notation "A / Φ" := (QuotientAlgebra A Φ)
                             (at level 40, left associativity)
                             : Algebra_scope.
End quotient_algebra_notations.

Import quotient_algebra_notations.

(** The next section shows that A/Φ = A/Ψ whenever
    [Φ s x y <-> Ψ s x y] for all [s], [x], [y]. *)

Section path_quotient_algebra.
  Context
    {σ : Signature} (A : Algebra σ)
    (Φ : ∀ s, Relation (A s)) {CΦ : IsCongruence A Φ}
    (Ψ : ∀ s, Relation (A s)) {CΨ : IsCongruence A Ψ}.

  Lemma path_quotient_algebra `{Funext} (p : Φ = Ψ) : A/Φ = A/Ψ.
  Proof.
    by destruct p, (path_ishprop CΦ CΨ).
  Defined.

  Lemma path_quotient_algebra_iff `{Univalence}
    (R : ∀ s x y, Φ s x y <-> Ψ s x y)
    : A/Φ = A/Ψ.
  Proof.
    apply path_quotient_algebra.
    funext s x y.
    refine (path_universe_uncurried _).
    apply equiv_iff_hprop; apply R.
  Defined.
End path_quotient_algebra.

(** The following section defines the quotient homomorphism
    [hom_quotient : Homomorphism A (A/Φ)]. *)

Section hom_quotient.
  Context
    `{Funext} {σ} {A : Algebra σ}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

  Definition def_hom_quotient : ∀ (s : Sort σ), A s → (A/Φ) s :=
    λ s x, class_of (Φ s) x.

  Lemma oppreserving_quotient `{Funext} (w : SymbolType σ)
      (g : Operation (A/Φ) w) (α : Operation A w)
      (G : ComputeOpQuotient A Φ α g)
      : OpPreserving def_hom_quotient α g.
  Proof.
    unfold ComputeOpQuotient in G.
    induction w; cbn in *.
    - by destruct (G tt)^.
    - intro x. apply IHw. intro a. apply (G (x,a)).
  Defined.

  Global Instance is_homomorphism_quotient `{Funext}
    : IsHomomorphism def_hom_quotient.
  Proof.
    intro u. apply oppreserving_quotient, compute_op_quotient.
  Defined.

  Definition hom_quotient : Homomorphism A (A/Φ)
    := BuildHomomorphism def_hom_quotient.

  Global Instance surjection_quotient
    : ∀ s, IsSurjection (hom_quotient s).
  Proof.
    intro s. apply quotient_surjective.
  Qed.
End hom_quotient.

(** If [Φ s x y] implies [x = y], then homomorphism [hom_quotient Φ]
    is an isomorphism. *)

Global Instance is_isomorphism_quotient `{Univalence}
  {σ : Signature} {A : Algebra σ} (Φ : ∀ s, Relation (A s))
  `{!IsCongruence A Φ} (P : ∀ s x y, Φ s x y → x = y)
  : IsIsomorphism (hom_quotient Φ).
Proof.
  intro s.
  apply isequiv_surj_emb; [exact _ |].
  apply isembedding_isinj_hset.
  intros x y p.
  by apply P, (classes_eq_related (Φ s)).
Qed.

(** This section develops the universal mapping property
    [ump_quotient_algebra] of the quotient algebra. *)

Section ump_quotient_algebra.
  Context
    `{Univalence} {σ} {A B : Algebra σ} `{!IsHSetAlgebra B}
    (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}.

(** In the nested section below we show that if [f : Homomorphism A B]
    maps elements related by [Φ] to equal elements, there is a
    [Homomorphism (A/Φ) B] out of the quotient algebra satisfying
    [compute_quotient_algebra_mapout] below. *)

  Section quotient_algebra_mapout.
    Context
      (f : Homomorphism A B)
      (R : ∀ s (x y : A s), Φ s x y → f s x = f s y).

    Definition def_hom_quotient_algebra_mapout
      : ∀ (s : Sort σ), (A/Φ) s → B s
      := λ s, (quotient_ump (Φ s) (BuildhSet (B s)))^-1 (f s; R s).

    Lemma oppreserving_quotient_algebra_mapout {w : SymbolType σ}
      (g : Operation (A/Φ) w) (α : Operation A w) (β : Operation B w)
      (G : ComputeOpQuotient A Φ α g) (P : OpPreserving f α β)
      : OpPreserving def_hom_quotient_algebra_mapout g β.
    Proof.
      unfold ComputeOpQuotient in G.
      induction w; cbn in *.
      - destruct (G tt)^. apply P.
      - refine (quotient_ind_prop (Φ t) _ _). intro x.
        apply (IHw (g (class_of (Φ t) x)) (α x) (β (f t x))).
        + intro a. apply (G (x,a)).
        + apply P.
    Defined.

    Global Instance is_homomorphism_quotient_algebra_mapout
      : IsHomomorphism def_hom_quotient_algebra_mapout.
    Proof.
      intro u.
      eapply oppreserving_quotient_algebra_mapout.
      - apply compute_op_quotient.
      - apply f.
    Defined.

    Definition hom_quotient_algebra_mapout
      : Homomorphism (A/Φ) B
      := BuildHomomorphism def_hom_quotient_algebra_mapout.

(** The computation rule for [hom_quotient_algebra_mapout] is

    <<
      hom_quotient_algebra_mapout s (class_of (Φ s) x) = f s x.
    >>
*)

    Lemma compute_quotient_algebra_mapout
      : ∀ (s : Sort σ) (x : A s),
        hom_quotient_algebra_mapout s (class_of (Φ s) x) = f s x.
    Proof.
      reflexivity.
    Defined.

  End quotient_algebra_mapout.

  Definition hom_quotient_algebra_mapin (g : Homomorphism (A/Φ) B)
    : Homomorphism A B
    := hom_compose g (hom_quotient Φ).

  Lemma ump_quotient_algebra_lr :
    {f : Homomorphism A B | ∀ s (x y : A s), Φ s x y → f s x = f s y}
    → Homomorphism (A/Φ) B.
  Proof.
    intros [f P]. exists (hom_quotient_algebra_mapout f P). exact _.
  Defined.

  Lemma ump_quotient_algebra_rl :
    Homomorphism (A/Φ) B →
    {f : Homomorphism A B | ∀ s (x y : A s), Φ s x y → f s x = f s y}.
  Proof.
    intro g.
    exists (hom_quotient_algebra_mapin g).
    intros s x y E.
    exact (transport (λ z, g s (class_of (Φ s) x) = g s z)
            (related_classes_eq (Φ s) E) idpath).
  Defined.

(** The universal mapping property of the quotient algebra. For each
    homomorphism [f : Homomorphism A B], mapping elements related by
    [Φ] to equal elements, there is a unique homomorphism
    [g : Homomorphism (A/Φ) B] satisfying

    <<
      f = hom_compose g (hom_quotient Φ).
    >>
*)

  Lemma ump_quotient_algebra
    : {f : Homomorphism A B | ∀ s (x y : A s), Φ s x y → f s x = f s y}
     <~>
      Homomorphism (A/Φ) B.
  Proof.
    apply (equiv_adjointify
             ump_quotient_algebra_lr ump_quotient_algebra_rl).
    - intro G.
      apply path_hset_homomorphism.
      funext s.
      exact (eissect (quotient_ump (Φ s) _) (G s)).
    - intro F.
      apply path_sigma_hprop.
      by apply path_hset_homomorphism.
  Defined.
End ump_quotient_algebra.
