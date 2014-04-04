Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual.
Require Import Category.Prod.
Require Import Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import SetCategory.
Require Import Functor.Attributes.
Require Import Functor.Composition.Functorial.
Require Import Functor.Identity.
Require ExponentialLaws.Law4.Functors.
Require ProductLaws.
Require Import HomFunctor.
Require Import FunctorCategory.Core.
Require Import NaturalTransformation.Paths.
Require Import HSet HoTT.Tactics FunextVarieties.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.

(** Quoting Wikipedia on the Yoneda lemma (chainging [A] to [a] and
    [C] to [A] so that we can use unicode superscripts and
    subscripts):

    In mathematics, specifically in category theory, the Yoneda lemma
    is an abstract result on functors of the type morphisms into a
    fixed object. It is a vast generalisation of Cayley's theorem from
    group theory (viewing a group as a particular kind of category
    with just one object). It allows the embedding of any category
    into a category of functors (contravariant set-valued functors)
    defined on that category. It also clarifies how the embedded
    category, of representable functors and their natural
    transformations, relates to the other objects in the larger
    functor category. It is an important tool that underlies several
    modern developments in algebraic geometry and representation
    theory. It is named after Nobuo Yoneda.

    * Generalities

    The Yoneda lemma suggests that instead of studying the (locally
    small) category [A], one should study the category of all functors
    of [A] into [Set] (the category of sets with functions as
    morphisms). [Set] is a category we understand well, and a functor
    of [A] into [Set] can be seen as a "representation" of [A] in
    terms of known structures. The original category [A] is contained
    in this functor category, but new objects appear in the functor
    category which were absent and "hidden" in [A]. Treating these new
    objects just like the old ones often unifies and simplifies the
    theory.  This approach is akin to (and in fact generalizes) the
    common method of studying a ring by investigating the modules over
    that ring. The ring takes the place of the category [A], and the
    category of modules over the ring is a category of functors
    defined on [A].

    * Formal statement

    ** General version

    Yoneda's lemma concerns functors from a fixed category [A] to the
    category of sets, [Set]. If [A] is a locally small category
    (i.e. the hom-sets are actual sets and not proper classes), then
    each object [a] of [A] gives rise to a natural functor to [Set]
    called a hom-functor. This functor is denoted:

    [hᵃ = Hom(a, ─)].

    The (covariant) hom-functor [hᵃ] sends [x] to the set of morphisms
    [Hom(a, x)] and sends a morphism [f] from [x] to [y] to the
    morphism [f ∘ ─] (composition with [f] on the left) that sends a
    morphism [g] in [Hom(a, x)] to the morphism [f ∘ g] in [Hom(a,
    y)]. That is,

    [f ↦ Hom(a, f) = ⟦ Hom(a, x) ∋ g ↦ f ∘ g ∈ Hom(a,y) ⟧].
 *)

Section yoneda.
  Context `{fs : Funext, fs' : Funext}.
  Let fs0 := Funext_downward_closed.
  Let fs1 := Funext_downward_closed.

  (* TODO(JasonGross): Find a way to unify the [yoneda] and [coyoneda] lemmas into a single lemma which is more functorial. *)

  Definition coyoneda A : Functor A^op (@functor_category fs A (@set_cat fs'))
    := ExponentialLaws.Law4.Functors.inverse _ _ _ (hom_functor A).

  Definition yoneda A : Functor A (@functor_category fs A^op (@set_cat fs'))
    := ((coyoneda A^op)^op'L)^op'L.
End yoneda.

Section coyoneda_lemma.
  Local Arguments Overture.compose / .

  Section functor.
    Context `{fs : Funext, fs' : Funext, fs'' : Funext, fs''' : Funext, fs_extra : Funext}.
    Let fs0 := @Funext_downward_closed fs_extra.
    Let fs1 := @Funext_downward_closed fs_extra.
    Let fs2 := @Funext_downward_closed fs_extra.
    Let fs3 := @Funext_downward_closed fs_extra.
    Let fs4 := @Funext_downward_closed fs_extra.

    Variable A : PreCategory.
    (** Let [F] be an arbitrary functor from [A] to [Set]. Then Yoneda's
      lemma says that: *)
    (*Variable F : Functor A (@set_cat fs).*)
    (** For each object [a] of [A], *)
    (*Variable a : A.*)
    (** the natural transformations from [hᵃ] to [F] are in one-to-one
      correspondence with the elements of [F(a)]. That is,

      [Nat(hᵃ, F) ≅ F(a)].

      Moreover this isomorphism is natural in [a] and [F] when both
      sides are regarded as functors from [Setᴬ × A] to
      [Set].

      Given a natural transformation [Φ] from [hᵃ] to [F], the
      corresponding element of [F(a)] is [u = Φₐ(idₐ)]. *)

    (*   Definition coyoneda_lemma_morphism (a : A)
  : morphism set_cat
             (BuildhSet
                (morphism (A -> set_cat) (coyoneda A a) F)
                _)
             (F a)
    := fun phi => phi a 1%morphism. *)


    Definition coyoneda_functor
    : Functor (@functor_category fs A (@set_cat fs'))
              (@functor_category fs'' A (@set_cat fs'''))
      := (@compose_functor fs0 fs1 fs'' fs2 fs3 _ _ (@set_cat fs''') (@coyoneda fs fs' A)^op'L)
           o (@yoneda fs4 fs''' (@functor_category fs A (@set_cat fs'))).
  End functor.

  Section nt.
    Context `{fs : Funext, fs' : Funext, fs'' : Funext, fs''' : Funext, fs_extra : Funext}.

    Variable A : PreCategory.

    Definition coyoneda_natural_transformation_helper F
    : morphism (@functor_category fs''' _ _) (@coyoneda_functor fs fs' fs'' fs' fs_extra A F) F.
    Proof.
      refine (Build_NaturalTransformation
                (coyoneda_functor A F) F
                (fun a phi => phi a 1%morphism)
                _).
      simpl.
      abstract (
          repeat (intro || apply (@path_forall (@Funext_downward_closed fs_extra)));
          simpl in *;
            match goal with
              | [ T : NaturalTransformation _ _ |- _ ]
                => simpl rewrite <- (fun s d m => apD10 (commutes T s d m))
            end;
          rewrite ?left_identity, ?right_identity;
          reflexivity
        ).
    Defined.

    Definition coyoneda_natural_transformation
    : morphism (@functor_category fs''' _ _)
               (@coyoneda_functor fs fs' fs'' fs' fs_extra A)
               (generalized_identity (@functor_category fs A (@set_cat fs')) (@functor_category fs'' A (@set_cat fs'))
                                     idpath idpath idpath (fun x => idpath)).
    Proof.
      hnf.
      simpl.
      let F := match goal with |- NaturalTransformation ?F ?G => constr:(F) end in
      let G := match goal with |- NaturalTransformation ?F ?G => constr:(G) end in
      refine (Build_NaturalTransformation
                F G
                coyoneda_natural_transformation_helper
                _).
      simpl.
      abstract (repeat first [ intro
                             | apply (@path_forall (@Funext_downward_closed fs_extra))
                             | progress path_natural_transformation
                             | reflexivity ]).
    Defined.
  End nt.

  Definition coyoneda_lemma_morphism_inverse
             `{fs : Funext, fs' : Funext, fs'' : Funext, fs''' : Funext, fs_extra : Funext}
             A
             (F : @functor_category fs A (@set_cat fs'))
             a
  : morphism (@set_cat fs')
             (F a)
             (@coyoneda_functor fs fs' fs'' fs' fs_extra A F a).
  Proof.
    intro Fa.
    hnf.
    simpl in *.
    let F0 := match goal with |- NaturalTransformation ?F ?G => constr:(F) end in
    let G0 := match goal with |- NaturalTransformation ?F ?G => constr:(G) end in
    refine (Build_NaturalTransformation
              F0 G0
              (fun a' : A => (fun f : morphism A a a' => morphism_of F f Fa))
              _
           ).
    simpl.
    abstract (
        repeat first [ reflexivity
                     | intro
                     | apply (@path_forall (@Funext_downward_closed fs_extra))
                     | progress rewrite ?composition_of, ?identity_of ]
      ).
  Defined.

  Global Instance coyoneda_lemma {fs fs' fs'' fs''' fs_extra} A
  : IsIsomorphism (@coyoneda_natural_transformation fs fs' fs'' fs''' fs_extra A).
  Proof.
    eapply isisomorphism_natural_transformation.
    simpl.
    intro F.
    eapply isisomorphism_natural_transformation.
    intro a.
    simpl.
    exists (@coyoneda_lemma_morphism_inverse fs fs' fs'' fs''' fs_extra A F a);
      simpl in *;
    abstract (
        repeat (intro || apply (@path_forall (@Funext_downward_closed fs_extra)) || path_natural_transformation);
        simpl in *;
          solve [ simpl rewrite <- (fun c d m => ap10 (commutes x c d m));
                  rewrite ?right_identity, ?left_identity;
                  reflexivity
                | rewrite identity_of;
                  reflexivity ]
      ).
  Defined.
End coyoneda_lemma.

Section yoneda_lemma.
  (** There is a contravariant version of Yoneda's lemma which
      concerns contravariant functors from [A] to [Set]. This version
      involves the contravariant hom-functor

      [hₐ = Hom(─, A)],

      which sends [x] to the hom-set [Hom(x, a)]. Given an arbitrary
      contravariant functor [G] from [A] to [Set], Yoneda's lemma
      asserts that

      [Nat(hₐ, G) ≅ G(a)]. *)

  Local Arguments Overture.compose / .

  Section functor.
    Context `{fs : Funext, fs' : Funext, fs'' : Funext, fs''' : Funext, fs_extra : Funext}.

    Variable A : PreCategory.
    (** Let [F] be an arbitrary functor from [A] to [Set]. Then Yoneda's
      lemma says that: *)
    (*Variable F : Functor A (@set_cat fs).*)
    (** For each object [a] of [A], *)
    (*Variable a : A.*)
    (** the natural transformations from [hᵃ] to [F] are in one-to-one
      correspondence with the elements of [F(a)]. That is,

      [Nat(hᵃ, F) ≅ F(a)].

      Moreover this isomorphism is natural in [a] and [F] when both
      sides are regarded as functors from [Setᴬ × A] to
      [Set].

      Given a natural transformation [Φ] from [hᵃ] to [F], the
      corresponding element of [F(a)] is [u = Φₐ(idₐ)]. *)

    (* Definition yoneda_lemma_morphism A (G : object (A^op -> set_cat)) (a : A)
  : morphism set_cat
             (BuildhSet
                (morphism (A^op -> set_cat) (yoneda A a) G)
                _)
             (G a)
    := fun phi => phi a 1%morphism.*)

    Definition yoneda_functor
    : Functor (@functor_category fs A^op (@set_cat fs'))
              (@functor_category fs'' A^op (@set_cat fs'''))
      := @coyoneda_functor fs fs' fs'' fs''' fs_extra A^op.
  End functor.

  Context `{fs : Funext, fs' : Funext, fs'' : Funext, fs''' : Funext, fs_extra : Funext}.

  Variable A : PreCategory.

  Definition yoneda_natural_transformation
  : morphism (@functor_category fs''' _ _)
             (generalized_identity (@functor_category fs A^op (@set_cat fs')) (@functor_category fs'' A^op (@set_cat fs'))
                                   idpath idpath idpath (fun x => idpath))
             (@yoneda_functor fs fs' fs'' fs' fs_extra A)
    := @morphism_inverse _ _ _ _ (@coyoneda_lemma fs fs' fs'' fs''' fs_extra A^op).

  Global Instance yoneda_lemma
  : IsIsomorphism yoneda_natural_transformation
    := @isisomorphism_inverse _ _ _ _ (@coyoneda_lemma fs fs' fs'' fs''' fs_extra A^op).
End yoneda_lemma.

(** ** The Yoneda embedding

    An important special case of Yoneda's lemma is when the functor
    [F] from [A] to [Set] is another hom-functor [hᵇ]. In this case,
    the covariant version of Yoneda's lemma states that

    [Nat(hᵃ, hᵇ) ≅ Hom(b, a)].

    That is, natural transformations between hom-functors are in
    one-to-one correspondence with morphisms (in the reverse
    direction) between the associated objects. Given a morphism [f : b
    → a] the associated natural transformation is denoted [Hom(f, ─)].

    Mapping each object [a] in [A] to its associated hom-functor [hᵃ=
    Hom(a, ─)] and each morphism [f : B → A] to the corresponding
    natural transformation [Hom(f, ─)] determines a contravariant
    functor [h⁻] from [A] to [Setᴬ], the functor category of all
    (covariant) functors from [A] to [Set]. One can interpret [h⁻] as
    a covariant functor:

    [h⁻ : Aᵒᵖ → Setᴬ].

    The meaning of Yoneda's lemma in this setting is that the functor
    [h⁻] is fully faithful, and therefore gives an embedding of [Aᵒᵖ]
    in the category of functors to [Set]. The collection of all
    functors {[hᵃ], [a] in [A]} is a subcategory of [Set̂ᴬ]. Therefore,
    Yoneda embedding implies that the category [Aᵒᵖ] is isomorphic to
    the category {[hᵃ], [a] in [A]}.

    The contravariant version of Yoneda's lemma states that

    [Nat(hₐ, h_b) ≅ Hom(a, b)].

    Therefore, [h₋] gives rise to a covariant functor from [A] to the
    category of contravariant functors to [Set]:

    [h₋ : A → Set⁽⁽ᴬ⁾ᵒᵖ⁾].

    Yoneda's lemma then states that any locally small category [A] can
    be embedded in the category of contravariant functors from [A] to
    [Set] via [h₋]. This is called the Yoneda embedding. *)

Section FullyFaithful.
  Context `{fs0 : Funext, fs0' : Funext, fs0'' : Funext, fs_extra0 : Funext}.
  Section coyoneda.
    Let fs' := fs0''. (* our hand is forced here *)
    (** These are somewhat free, so we pick the extra instance of [Funext]. *)
    Let fs'''' := @Funext_downward_closed fs_extra0(*fs0*).
    Let fs := @Funext_downward_closed fs_extra0(*fs0*).
    Let fs'' := @Funext_downward_closed fs_extra0(*fs0'*).
    Let fs''' := @Funext_downward_closed fs_extra0(*fs0'*).
    Let fs_extra := @Funext_downward_closed fs_extra0(*fs0'*).

    Variable A : PreCategory.

    Local Arguments Overture.compose / .

    Definition coyoneda_embedding : @IsFullyFaithful fs0 _ _ (@coyoneda fs0' fs0'' A).
    Proof.
      intros a b.
      pose proof (@isisomorphism_inverse
                    _ _ _ _
                    (@isisomorphism_components_of
                       _ _ _ _ _ _
                       (@isisomorphism_components_of
                          _ _ _ _ _ _
                          (@coyoneda_lemma fs fs' fs'' fs''' fs_extra A)
                          (@coyoneda fs'''' _ A b))
                       a)) as H'.

      simpl in *.
      unfold coyoneda_lemma_morphism_inverse in *; simpl in *.
      unfold Functors.inverse_object_of_morphism_of in *; simpl in *.
      let m := match type of H' with IsIsomorphism ?m => constr:(m) end in
      apply isisomorphism_set_cat_natural_transformation_paths with (T1 := m).
      - simpl.
        clear H'.
        abstract (
            intros; apply (@path_forall (@Funext_downward_closed fs_extra));
            intro;
            rewrite left_identity, right_identity;
            reflexivity
          ).
      - destruct H' as [m' H0' H1'].
        (exists m').
        + exact H0'.
        + exact H1'.
    Defined.
  End coyoneda.

  Definition yoneda_embedding A : @IsFullyFaithful fs0 _ _ (@yoneda fs0' fs0'' A).
  Proof.
    intros a b.
    pose proof (@coyoneda_embedding A^op a b) as CYE.
    unfold yoneda.
    let T := type of CYE in
    let T' := (eval simpl in T) in
    pose proof ((fun x : T => (x : T')) CYE) as CYE'.
    let G := match goal with |- ?G => constr:(G) end in
    let G' := (eval simpl in G) in
    exact ((fun x : G' => (x : G)) CYE').
  Defined.
End FullyFaithful.
