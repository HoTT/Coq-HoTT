(** * Definitions and theorems about {iso,epi,mono,}morphisms in a precategory *)
Require Import Category.Core Functor.Core.
Require Import HoTT.Tactics Types.Record Trunc HProp Types.Sigma Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Definition of isomorphism *)
Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) :=
  {
    morphism_inverse : morphism C d s;
    left_inverse : morphism_inverse o m = identity _;
    right_inverse : m o morphism_inverse = identity _
  }.

Arguments morphism_inverse {C s d} m {_}.

Local Notation "m ^-1" := (morphism_inverse m) : morphism_scope.

Hint Resolve left_inverse right_inverse : category morphism.
Hint Rewrite @left_inverse @right_inverse : category.
Hint Rewrite @left_inverse @right_inverse : morphism.

Class Isomorphic {C : PreCategory} s d :=
  {
    morphism_isomorphic : morphism C s d;
    isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic
  }.

(*Coercion Build_Isomorphic : IsIsomorphism >-> Isomorphic.*)
Coercion morphism_isomorphic : Isomorphic >-> morphism.
Coercion isisomorphism_isomorphic : Isomorphic >-> IsIsomorphism.

Local Infix "<~=~>" := Isomorphic : category_scope.

Global Existing Instance isisomorphism_isomorphic.

(** ** Theorems about isomorphisms *)
Section iso_contr.
  Variable C : PreCategory.



  Variables s d : C.

  Local Notation IsIsomorphism_sig_T m :=
    { inverse : morphism C d s
    | { _ : inverse o m = identity _
      | m o inverse = identity _ } } (only parsing).

  Section IsIsomorphism.
    Variable m : morphism C s d.

    (** *** The inverse of a morphism is unique *)
    Lemma inverse_unique (m_inv0 m_inv1 : morphism C d s)
          (left_inverse_0 : m_inv0 o m = identity _)
          (right_inverse_1 : m o m_inv1 = identity _)
    : m_inv0 = m_inv1.
    Proof.
      transitivity (m_inv0 o m o m_inv1);
      try solve [ by (rewrite -> ?associativity; rewrite_hyp;
                      autorewrite with morphism)
                | by (rewrite <- ?associativity; rewrite_hyp;
                      autorewrite with morphism) ].
    Qed.

    (** *** Equivalence between the record and sigma versions of [IsIsomorphism] *)
    Lemma issig_isisomorphism
    : IsIsomorphism_sig_T m <~> IsIsomorphism m.
    Proof.
      issig (@Build_IsIsomorphism _ _ _ m)
            (@morphism_inverse _ _ _ m)
            (@left_inverse _ _ _ m)
            (@right_inverse _ _ _ m).
    Defined.

    (** *** Being an isomorphism is a mere proposition *)
    Global Instance trunc_isisomorphism : IsHProp (IsIsomorphism m).
    Proof.
      eapply trunc_equiv'; [ exact issig_isisomorphism | ].
      apply hprop_allpath.
      intros [x [? ?]] [y [? ?]].
      let H := fresh in
      assert (H : x = y) by (apply inverse_unique; assumption);
        destruct H.
      repeat match goal with
               | _ => progress simpl
               | _ => exact (center _)
               | _ => (exists idpath)
               | _ => apply path_sigma_uncurried
             end.
    Qed.
  End IsIsomorphism.

  Local Notation Isomorphic_sig_T :=
    { m : morphism C s d
    | IsIsomorphism m } (only parsing).

  (** *** Equivalence between record and sigma versions of [Isomorphic] *)
  Lemma issig_isomorphic
  : Isomorphic_sig_T <~> Isomorphic s d.
  Proof.
    issig (@Build_Isomorphic C s d)
          (@morphism_isomorphic C s d)
          (@isisomorphism_isomorphic C s d).
  Defined.

  Local Notation Isomorphic_full_sig_T :=
    { m : morphism C s d
    | IsIsomorphism_sig_T m } (only parsing).

  (** *** Equivalence between record and fully sigma versions of [Isomorphic] *)
  Definition issig_full_isomorphic
  : Isomorphic_full_sig_T <~> Isomorphic s d
    := (issig_isomorphic oE equiv_functor_sigma_id issig_isisomorphism).

  (** *** Isomorphisms form an hSet *)
  Global Instance trunc_Isomorphic : IsHSet (Isomorphic s d).
  Proof.
    eapply trunc_equiv'; [ exact issig_isomorphic | ].
    typeclasses eauto.
  Qed.

  (** *** Equality between isomorphisms is determined by equality between their forward components *)
  Definition path_isomorphic (i j : Isomorphic s d)
  : @morphism_isomorphic _ _ _ i = @morphism_isomorphic _ _ _ j
    -> i = j.
  Proof.
    destruct i, j; simpl.
    intro; path_induction.
    f_ap.
    exact (center _).
  Defined.

  (** *** Relations between [path_isomorphic], [ap morphism_inverse], and [ap morphism_isomorphic] *)
  Definition ap_morphism_isomorphic_path_isomorphic (i j : Isomorphic s d) p
  : ap (@morphism_isomorphic _ _ _) (path_isomorphic i j p) = p.
  Proof.
    unfold path_isomorphic.
    destruct i, j.
    path_induction_hammer.
  Qed.

  Definition ap_morphism_inverse_path_isomorphic (i j : Isomorphic s d) p q
  : ap (fun e : Isomorphic s d => e^-1)%morphism (path_isomorphic i j p) = q.
  Proof.
    apply path_ishprop.
  Qed.

  (** *** Equality between isomorphisms is equivalent to by equality between their forward components *)
  Global Instance isequiv_path_isomorphic
  : IsEquiv (path_isomorphic i j).
  Proof.
    intros.
    apply (isequiv_adjointify
             (path_isomorphic i j)
             (ap (@morphism_isomorphic _ _ _)));
      intro; [ destruct i | destruct i, j ];
      path_induction_hammer.
  Defined.
End iso_contr.

Section iso_equiv_relation.
  Variable C : PreCategory.

  (** *** The identity is an isomorphism *)
  Global Instance isisomorphism_identity (x : C) : IsIsomorphism (identity x)
    := {| morphism_inverse := identity x;
          left_inverse := left_identity C x x (identity x);
          right_inverse := right_identity C x x (identity x) |}.

  (** *** Inverses of isomorphisms are isomorphisms *)
  Definition isisomorphism_inverse `(@IsIsomorphism C x y m) : IsIsomorphism m^-1
    := {| morphism_inverse := m;
          left_inverse := right_inverse;
          right_inverse := left_inverse |}.

  Local Ltac iso_comp_t inv_lemma :=
    etransitivity; [ | apply inv_lemma ];
    instantiate;
    first [ rewrite -> ?associativity; apply ap
          | rewrite <- ?associativity; apply ap ];
    first [ rewrite -> ?associativity; rewrite inv_lemma
          | rewrite <- ?associativity; rewrite inv_lemma ];
    auto with morphism.

  (** *** Composition of isomorphisms gives an isomorphism *)
  Global Instance isisomorphism_compose `(@IsIsomorphism C y z m0) `(@IsIsomorphism C x y m1)
  : IsIsomorphism (m0 o m1).
  Proof.
    exists (m1^-1 o m0^-1);
    [ abstract iso_comp_t @left_inverse
    | abstract iso_comp_t @right_inverse ].
  Defined.

  Hint Immediate isisomorphism_inverse : typeclass_instances.

  (** *** Being isomorphic is a reflexive relation *)
  Global Instance isomorphic_refl : Reflexive (@Isomorphic C)
    := fun x : C => {| morphism_isomorphic := identity x |}.

  (** *** Being isomorphic is a symmetric relation *)
  Global Instance isomorphic_sym : Symmetric (@Isomorphic C)
    := fun x y X => {| morphism_isomorphic := X^-1 |}.

  (** *** Being isomorphic is a transitive relation *)
  Global Instance isomorphic_trans : Transitive (@Isomorphic C)
    := fun x y z X Y => {| morphism_isomorphic := @morphism_isomorphic _ _ _ Y o @morphism_isomorphic _ _ _ X |}.

  (** *** Equality gives rise to isomorphism *)
  Definition idtoiso (x y : C) (H : x = y) : Isomorphic x y
    := match H in (_ = y0) return (x <~=~> y0) with
         | 1%path => reflexivity x
       end.
End iso_equiv_relation.

Hint Immediate isisomorphism_inverse : typeclass_instances.

(** ** Epimorphisms and Monomorphisms *)
(** Quoting Wikipedia:

    In category theory, an epimorphism (also called an epic morphism
    or, colloquially, an epi) is a morphism [f : X → Y] which is
    right-cancellative in the sense that, for all morphisms [g, g' : Y
    → Z], [g ∘ f = g' ∘ f → g = g']

    Epimorphisms are analogues of surjective functions, but they are
    not exactly the same. The dual of an epimorphism is a monomorphism
    (i.e. an epimorphism in a category [C] is a monomorphism in the
    dual category [Cᵒᵖ]).  *)

Class IsEpimorphism {C} {x y} (m : morphism C x y) :=
  is_epimorphism : forall z (m1 m2 : morphism C y z),
                     m1 o m = m2 o m
                     -> m1 = m2.
Class IsMonomorphism {C} {x y} (m : morphism C x y) :=
  is_monomorphism : forall z (m1 m2 : morphism C z x),
                      m o m1 = m o m2
                      -> m1 = m2.

(** We make [IsEpimorphism] and [IsMonomorphism] transparent to
    typeclass search so that we can infer things like [IsHProp]
    automatically. *)
Typeclasses Transparent IsEpimorphism IsMonomorphism.

Record Epimorphism {C} x y :=
  {
    Epimorphism_morphism :> morphism C x y;
    Epimorphism_IsEpimorphism :> IsEpimorphism Epimorphism_morphism
  }.

Record Monomorphism {C} x y :=
  {
    Monomorphism_morphism :> morphism C x y;
    Monomorphism_IsMonomorphism :> IsMonomorphism Monomorphism_morphism
  }.

Global Existing Instances Epimorphism_IsEpimorphism Monomorphism_IsMonomorphism.

Local Notation "x ->> y" := (Epimorphism x y).
Local Notation "x (-> y" := (Monomorphism x y).

Class IsSectionOf C x y (s : morphism C x y) (r : morphism C y x)
  := is_sect_morphism : r o s = identity _.

Arguments IsSectionOf [C x y] s r.

Section EpiMono.
  Variable C : PreCategory.

  Section properties.
    (** *** The identity is an epimorphism *)
    Global Instance isepimorphism_identity (x : C)
    : IsEpimorphism (identity x).
    Proof.
      repeat intro; autorewrite with morphism in *; trivial.
    Qed.

    (** *** The identity is a monomorphism *)
    Global Instance ismonomorphism_identity (x : C)
    : IsMonomorphism (identity x).
    Proof.
      repeat intro; autorewrite with morphism in *; trivial.
    Qed.

    (** *** Composition of epimorphisms gives an epimorphism *)
    Global Instance isepimorphism_compose s d d' m0 m1
    : IsEpimorphism m0
      -> IsEpimorphism m1
      -> IsEpimorphism (@compose C s d d' m0 m1).
    Proof.
      repeat intro.
      rewrite <- !associativity in *.
      apply_hyp.
    Qed.

    (** *** Composition of monomorphisms gives a monomorphism *)
    Global Instance ismonomorphism_compose s d d' m0 m1
    : IsMonomorphism m0
      -> IsMonomorphism m1
      -> IsMonomorphism (@compose C s d d' m0 m1).
    Proof.
      repeat intro.
      rewrite !associativity in *.
      apply_hyp.
    Qed.
  End properties.

  (** *** Existence of {epi,mono}morphisms are a preorder *)
  Section equiv.
    Global Instance reflexive_epimorphism : Reflexive (@Epimorphism C)
      := fun x => Build_Epimorphism (isepimorphism_identity x).

    Global Instance reflexive_monomorphism : Reflexive (@Monomorphism C)
      := fun x => Build_Monomorphism (ismonomorphism_identity x).

    Global Instance transitive_epimorphism : Transitive (@Epimorphism C)
      := fun _ _ _ m0 m1 => Build_Epimorphism (isepimorphism_compose m1 m0).

    Global Instance transitive_monomorphism : Transitive (@Monomorphism C)
      := fun _ _ _ m0 m1 => Build_Monomorphism (ismonomorphism_compose m1 m0).
  End equiv.

  Section sect.
    Local Ltac epi_mono_sect_t :=
      let t :=
          (solve [ autorewrite with morphism;
                   reflexivity
                 | rewrite_hyp;
                   autorewrite with morphism;
                   reflexivity ]) in
      first [ rewrite -> ?associativity; t
            | rewrite <- ?associativity; t].

    (** *** Retractions are epimorphisms *)
    Global Instance isepimorphism_retr `(@IsSectionOf C x y s r)
    : IsEpimorphism r | 1000.
    Proof.
      (intros ? m1 m2 ?).
      unfold IsSectionOf in *.
      transitivity ((m1 o r) o s);
        [ | transitivity ((m2 o r) o s) ];
        epi_mono_sect_t.
    Qed.

    (** *** Sections are monomorphisms *)
    Global Instance ismonomorphism_sect `(@IsSectionOf C x y s r)
    : IsMonomorphism s | 1000.
    Proof.
      (intros ? m1 m2 ?).
      transitivity (r o (s o m1));
        [ | transitivity (r o (s o m2)) ];
        epi_mono_sect_t.
    Qed.

    (** *** Isomorphisms are both sections and retractions *)
    Global Instance issect_isisomorphism `(@IsIsomorphism C x y m)
    : IsSectionOf m m^-1 | 1000
      := left_inverse.

    Global Instance isretr_isisomorphism `(@IsIsomorphism C x y m)
    : IsSectionOf m^-1 m | 1000
      := right_inverse.
  End sect.

  (** *** Isomorphisms are therefore epimorphisms and monomorphisms *)
  Section iso.
    Global Instance isepimorphism_isisomorphism `(@IsIsomorphism C s d m)
    : IsEpimorphism m | 1000
      := _.
    Global Instance ismonomorphism_isisomorphism `(@IsIsomorphism C s d m)
    : IsMonomorphism m | 1000
      := _.
  End iso.
End EpiMono.

Hint Immediate @isepimorphism_identity @ismonomorphism_identity @ismonomorphism_compose @isepimorphism_compose : category morphism.

(** ** Lemmas about [idtoiso] *)
Section iso_lemmas.
  Local Ltac idtoiso_t :=
    path_induction; simpl; autorewrite with morphism; reflexivity.

  (** *** [transport]ing across an equality of morphisms is the same as conjugating with [idtoiso] *)
  Lemma idtoiso_of_transport (C D : PreCategory) s d
        (m1 m2 : morphism C s d)
        (p : m1 = m2)
        (s' d' : morphism C s d -> D) u
  : @transport _ (fun m => morphism D (s' m) (d' m)) _ _ p u
    = idtoiso _ (ap d' p) o u o (idtoiso _ (ap s' p))^-1.
  Proof. idtoiso_t. Qed.

  (** *** [idtoiso] respects inverse *)
  Lemma idtoiso_inv (C : PreCategory) (s d : C) (p : s = d)
  : (idtoiso _ p)^-1 = idtoiso _ (p^)%path.
  Proof.
    path_induction; reflexivity.
  Defined.

  (** *** [idtoiso] respects composition *)
  Lemma idtoiso_comp (C : PreCategory) (s d d' : C)
        (m1 : d = d') (m2 : s = d)
  : idtoiso _ m1 o idtoiso _ m2 = idtoiso _ (m2 @ m1)%path.
  Proof. idtoiso_t. Qed.

  (** These are useful when tactics are too slow and [rewrite] doesn't
      work. *)
  Lemma idtoiso_comp3 (C : PreCategory) (s d d' d'' : C)
        (m0 : d' = d'') (m1 : d = d') (m2 : s = d)
  : idtoiso _ m0 o (idtoiso _ m1 o idtoiso _ m2) = idtoiso _ ((m2 @ m1) @ m0)%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp3' (C : PreCategory) (s d d' d'' : C)
        (m0 : d' = d'') (m1 : d = d') (m2 : s = d)
  : (idtoiso _ m0 o idtoiso _ m1) o idtoiso _ m2 = idtoiso _ (m2 @ (m1 @ m0))%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp4 (C : PreCategory) (s d d' d'' d''' : C)
        (m0 : d'' = d''') (m1 : d' = d'') (m2 : d = d') (m3 : s = d)
  : idtoiso _ m0 o (idtoiso _ m1 o (idtoiso _ m2 o idtoiso _ m3)) = idtoiso _ (((m3 @ m2) @ m1) @ m0)%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp4' (C : PreCategory) (s d d' d'' d''' : C)
        (m0 : d'' = d''') (m1 : d' = d'') (m2 : d = d') (m3 : s = d)
  : ((idtoiso _ m0 o idtoiso _ m1) o idtoiso _ m2) o idtoiso _ m3 = idtoiso _ (m3 @ (m2 @ (m1 @ m0)))%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp5 (C : PreCategory) (s d d' d'' d''' d'''' : C)
        (m0 : d''' = d'''') (m1 : d'' = d''') (m2 : d' = d'') (m3 : d = d') (m4 : s = d)
  : idtoiso _ m0 o (idtoiso _ m1 o (idtoiso _ m2 o (idtoiso _ m3 o idtoiso _ m4)))
    = idtoiso _ ((((m4 @ m3) @ m2) @ m1) @ m0)%path.
  Proof. idtoiso_t. Qed.

  Lemma idtoiso_comp5' (C : PreCategory) (s d d' d'' d''' d'''' : C)
        (m0 : d''' = d'''') (m1 : d'' = d''') (m2 : d' = d'') (m3 : d = d') (m4 : s = d)
  : (((idtoiso _ m0 o idtoiso _ m1) o idtoiso _ m2) o idtoiso _ m3) o idtoiso _ m4
    = idtoiso _ (m4 @ (m3 @ (m2 @ (m1 @ m0))))%path.
  Proof. idtoiso_t. Qed.

  (** *** [idtoiso] respects application of functors on morphisms and objects *)
  Lemma idtoiso_functor (C D : PreCategory) (s d : C) (m : s = d)
        (F : Functor C D)
  : F _1 (idtoiso _ m) = idtoiso _ (ap (object_of F) m).
  Proof.
    path_induction; simpl; apply identity_of.
  Defined.

  (** *** Functors preserve isomorphisms *)
  Global Instance iso_functor C D (F : Functor C D) `(@IsIsomorphism C s d m)
  : IsIsomorphism (F _1 m).
  Proof.
    refine ({| morphism_inverse := F _1 m^-1 |}).
    - abstract (rewrite <- composition_of, ?left_inverse, ?right_inverse, identity_of; reflexivity).
    - abstract (rewrite <- composition_of, ?left_inverse, ?right_inverse, identity_of; reflexivity).
  Defined.
End iso_lemmas.

Hint Extern 1 (@IsIsomorphism _ _ _ (@morphism_of ?C ?D ?F ?s ?d ?m))
=> apply (@iso_functor C D F s d m) : typeclass_instances.

Hint Rewrite idtoiso_of_transport idtoiso_inv idtoiso_comp idtoiso_functor.

(** ** Lemmas about how to move isomorphisms around equalities, following [HoTT.PathGroupoids] *)
Section iso_concat_lemmas.
  Variable C : PreCategory.

  Local Ltac iso_concat_t' :=
    intros;
    repeat match goal with
             | [ H : ?x = ?y |- _ ] => atomic y; induction H
             | [ H : ?x = ?y |- _ ] => atomic x; symmetry in H; induction H
           end;
    repeat first [ done
                 | rewrite -> ?associativity;
                   progress rewrite ?left_identity, ?right_identity, ?left_inverse, ?right_inverse
                 | rewrite <- ?associativity;
                   progress rewrite ?left_identity, ?right_identity, ?left_inverse, ?right_inverse
                 | rewrite -> ?associativity; progress f_ap; []
                 | rewrite <- ?associativity; progress f_ap; [] ].

  Local Ltac iso_concat_t_id_fin :=
    match goal with
      | [ |- context[@identity ?C ?x] ]
        => generalize dependent (identity x)
    end;
    iso_concat_t'.

  Local Ltac iso_concat_t_id lem :=
    first [ solve [
                etransitivity; [ | eapply lem ];
                iso_concat_t_id_fin
              ]
          | solve [
                etransitivity; [ symmetry; eapply lem | ];
                iso_concat_t_id_fin
          ] ].

  Local Ltac iso_concat_t :=
    iso_concat_t';
    try first [ solve [ iso_concat_t_id @left_identity ]
              | solve [ iso_concat_t_id @right_identity ] ].

  Definition iso_compose_pV `(@IsIsomorphism C x y p)
  : p o p^-1 = identity _
    := right_inverse.
  Definition iso_compose_Vp `(@IsIsomorphism C x y p)
  : p^-1 o p = identity _
    := left_inverse.

  Definition iso_compose_V_pp `(@IsIsomorphism C y z p) `(q : morphism C x y)
  : p^-1 o (p o q) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_p_Vp `(@IsIsomorphism C x z p) `(q : morphism C y z)
  : p o (p^-1 o q) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_pp_V `(p : morphism C y z) `(@IsIsomorphism C x y q)
  : (p o q) o q^-1 = p.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_pV_p `(p : morphism C x z) `(@IsIsomorphism C x y q)
  : (p o q^-1) o q = p.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_pp `(@IsIsomorphism C y z p) `(@IsIsomorphism C x y q)
  : (p o q)^-1 = q^-1 o p^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_Vp `(@IsIsomorphism C y z p) `(@IsIsomorphism C x z q)
  : (p^-1 o q)^-1 = q^-1 o p.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_pV `(@IsIsomorphism C x y p) `(@IsIsomorphism C x z q)
  : (p o q^-1)^-1 = q o p^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_VV `(@IsIsomorphism C x y p) `(@IsIsomorphism C y z q)
  : (p^-1 o q^-1)^-1 = q o p.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_Mp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C y z r)
  : p = (r^-1 o q) -> (r o p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_pM `(@IsIsomorphism C x y p) `(q : morphism C x z) `(r : morphism C y z)
  : r = (q o p^-1) -> (r o p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_Vp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C z y r)
  : p = (r o q) -> (r^-1 o p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_pV `(@IsIsomorphism C x y p) `(q : morphism C y z) `(r : morphism C x z)
  : r = (q o p) -> (r o p^-1) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_Mp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C y z r)
  : (r^-1 o q) = p -> q = (r o p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_pM `(@IsIsomorphism C x y p) `(q : morphism C x z) `(r : morphism C y z)
  : (q o p^-1) = r -> q = (r o p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_Vp `(p : morphism C x y) `(q : morphism C x z) `(@IsIsomorphism C _ _ r)
  : (r o q) = p -> q = (r^-1 o p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_pV `(@IsIsomorphism C x y p) `(q : morphism C y z) r
  : (q o p) = r -> q = (r o p^-1).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_1M `(p : morphism C x y) `(@IsIsomorphism C x y q)
  : p o q^-1 = identity _ -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_M1 `(p : morphism C x y) `(@IsIsomorphism C x y q)
  : q^-1 o p = identity _ -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_1V `(p : morphism C x y) `(@IsIsomorphism C y x q)
  : p o q = identity _ -> p = q^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_V1 `(p : morphism C x y) `(@IsIsomorphism C y x q)
  : q o p = identity _ -> p = q^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_M1 `(@IsIsomorphism C x y p) q
  : identity _ = p^-1 o q -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_1M `(@IsIsomorphism C x y p) q
  : identity _ = q o p^-1 -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_1V `(@IsIsomorphism C x y p) q
  : identity _ = q o p -> p^-1 = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_V1 `(@IsIsomorphism C x y p) q
  : identity _ = p o q -> p^-1 = q.
  Proof. iso_concat_t. Qed.
End iso_concat_lemmas.

(** ** Tactics for moving inverses around *)
Ltac iso_move_inverse' :=
  match goal with
    | [ |- _^-1 o _ = _ ] => apply iso_moveR_Vp
    | [ |- _ = _^-1 o _ ] => apply iso_moveL_Vp
    | [ |- _ o _^-1 = _ ] => apply iso_moveR_pV
    | [ |- _ = _ o _^-1 ] => apply iso_moveL_pV
    | [ |- _ o (_ o _^-1) = _ ] => rewrite <- associativity
    | [ |- _ = _ o (_ o _^-1) ] => rewrite <- associativity
    | [ |- (_^-1 o _) o _ = _ ] => rewrite -> associativity
    | [ |- _ = (_^-1 o _) o _ ] => rewrite -> associativity
  end.

Ltac iso_move_inverse := progress repeat iso_move_inverse'.

(** ** Tactics for collapsing [p ∘ p⁻¹] and [p⁻¹ ∘ p] *)
(** Now the tactics for collapsing [p ∘ p⁻¹] (and [p⁻¹ ∘ p]) in the
    middle of a chain of compositions of isomorphisms. *)

Ltac iso_collapse_inverse_left' :=
  first [ apply ap
        | progress rewrite ?iso_compose_p_Vp, ?iso_compose_V_pp ].

Ltac iso_collapse_inverse_left :=
  rewrite -> ?Category.Core.associativity;
  progress repeat iso_collapse_inverse_left'.

Ltac iso_collapse_inverse_right' :=
  first [ apply ap10; apply ap
        | progress rewrite ?iso_compose_pV_p, ?iso_compose_pp_V ].

Ltac iso_collapse_inverse_right :=
  rewrite <- ?Category.Core.associativity;
  progress repeat iso_collapse_inverse_right'.

Ltac iso_collapse_inverse :=
  progress repeat first [ iso_collapse_inverse_left
                        | iso_collapse_inverse_right ].

Section associativity_composition.
  Variable C : PreCategory.
  Variables x0 x1 x2 x3 x4 : C.

  (** This lemma is helpful for backwards reasoning. *)
  Lemma compose4associativity_helper
    (a : morphism C x3 x4) (b : morphism C x2 x3)
    (c : morphism C x1 x2) (d : morphism C x0 x1)
  : a o b o c o d = (a o ((b o c) o d)).
  Proof.
    rewrite !associativity; reflexivity.
  Qed.
End associativity_composition.

Module Export CategoryMorphismsNotations.
  Notation "m ^-1" := (morphism_inverse m) : morphism_scope.

  Infix "<~=~>" := Isomorphic : category_scope.

  Notation "x ->> y" := (Epimorphism x y).
  Notation "x (-> y" := (Monomorphism x y).
End CategoryMorphismsNotations.
