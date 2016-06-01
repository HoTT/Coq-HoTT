Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.functors
  HoTTClasses.theory.jections.

Notation "x ⇛ y" := (∀ a, x a ⟶ y a) (at level 90, right associativity) : mc_scope.
  (* Transformations (polymorphic arrows). Couldn't find an "arrow with dot over it" unicode character. *)

(* Natural transformations: *)
Definition id_nat_trans `{Arrows D} `{!CatId D} `(F: C → D): F ⇛ F := λ _, cat_id.

Section NaturalTransformation.
  Context `{Category C} `{Category D} `{!Functor (F: C → D) Fa} `{!Functor (G: C → D) Ga}.
  Class NaturalTransformation (η: F ⇛ G) :=
    natural: ∀ `(f: x ⟶ y), η y ◎ fmap F f = fmap G f ◎ η x.
End NaturalTransformation.

Section UniversalArrow.
  Context `{Category D} `{Category C} `{!Functor (F: D → C) Fa}.
  Class UniversalArrow `(u: c ⟶ F r) (wit: ∀ `(f: c ⟶ F d), r ⟶ d) :=
    universal_arrow: ∀ (d: D) (f: c ⟶ F d), is_sole ((f =) ∘ (◎ u) ∘ fmap F) (wit f).
      (* Todo: Consider an operational type class for wit. *)
End UniversalArrow.

Section adjunction.
  (* Three definitions of adjunctions. *)
  Context `{Category C} `{Category D}
    F `{!Functor (F: C → D) F'}
    G `{!Functor (G: D → C) G'}.

  (* 1. The definition based on φ (MacLane p79): *)
  Class φAdjunction (φ: ∀ `(F c ⟶ d), (c ⟶ G d)) `{∀ c d, Inverse (@φ c d)} :=
    { φ_adjunction_left_functor: Functor F _
    ; φ_adjunction_right_functor: Functor G _
    ; φ_adjunction_bijective: ∀ c d, Bijective (@φ c d)
    ; φ_adjunction_natural_left `(f: F c ⟶ d) `(k: d ⟶ d'): φ (k ◎ f) = fmap G k ◎ φ f
    ; φ_adjunction_natural_right `(f: F c ⟶ d) `(h: c' ⟶ c): φ (f ◎ fmap F h) = φ f ◎ h }.

  (* 2. The definition based on a universal η (MacLane p81 Theorem 2 (i)): *)
  Class ηAdjunction (η: id ⇛ G ∘ F) (uniwit: ∀ `(c ⟶ G d), F c ⟶ d) :=
    { η_adjunction_left_functor: Functor F _
    ; η_adjunction_right_functor: Functor G _
    ; η_adjunction_natural: NaturalTransformation η
    ; η_adjunction_universal: ∀ c: C, UniversalArrow (η c: c ⟶ G (F c)) (@uniwit c) }.

  (* We could symmetically define εAdjunction based on universal ε, as
    in MacLane p81 Theorem 2 (iii), but that would be boring. *)

  (* 3. The definition based on η and ε being inverses (MacLane p81 Theorem 2 (v)): *)
  Class ηεAdjunction (η: id ⇛ G ∘ F) (ε: F ∘ G ⇛ id) :=
    { ηε_adjunction_left_functor: Functor F _
    ; ηε_adjunction_right_functor: Functor G _
    ; ηε_adjunction_η_natural: NaturalTransformation η
    ; ηε_adjunction_ε_natural: NaturalTransformation ε
    ; ηε_adjunction_identity_at_G: ∀ a, fmap G (ε a) ◎ η (G a) = id_nat_trans G a
    ; ηε_adjunction_identity_at_F: ∀ a, ε (F a) ◎ fmap F (η a) = id_nat_trans F a }.

  (* We currently don't define adjunctions as characterized in MacLane p81 Theorem 2 (ii) and (iv). *)
End adjunction.

Section contents.
  Context `{Category X}.

  Class Mono `(a: x ⟶ y) :=
    mono: ∀ z (f g: z ⟶ x), a ◎ f = a ◎ g → f = g.

  Section isomorphy.
    Definition iso_arrows {x y: X} (a: x ⟶ y) (b: y ⟶ x)
      := a ◎ b = cat_id ∧ b ◎ a = cat_id. (* todo: product *)

    Global Instance: HeteroSymmetric (@iso_arrows).
    Proof.
    unfold iso_arrows.
    intros x y a b [p1 p2].
    auto.
    Qed.

    Definition is_iso {x y: X} (a: x ⟶ y) := exist (iso_arrows a).

    Definition isos_unique (x y: X) (a: x ⟶ y) (b b': y ⟶ x)
     : iso_arrows a b → iso_arrows a b' → b = b'.
    Proof.
    intros [P Q] [R S].
    rewrite <- left_identity.
    rewrite <- Q, <-associativity, R.
    apply symmetry, right_identity.
    Qed.

    Definition iso: relation X := λ x y, sig (uncurry (@iso_arrows x y)).
    Definition isoT: X → X → Type := iso.

    Instance: Reflexive iso.
    Proof.
    intros x. exists (cat_id, cat_id).
    split;apply left_identity.
    Qed.

    Instance: Symmetric iso.
    Proof.
    intros ? ? [[f f'] ?].
    exists (f', f).
    unfold uncurry.
    apply (hetero_symmetric). assumption.
    Qed.

    Instance: Transitive iso.
    Proof with assumption.
     intros ? ? ? [[f f'] [U V]] [[g g'] [W Z]].
     exists (g ◎ f, f' ◎ g').
     split; simpl in *.
     - rewrite <- (associativity g f (f' ◎ g')), (associativity f f' g'), U, left_identity.
       assumption.
     - rewrite <- (associativity f' g' (g ◎ f)), (associativity g' g f), Z, left_identity.
       assumption.
    Qed.

    Lemma arrows_between_isomorphic_objects (a b c d: X)
      (ab: a ⟶ b) (ba: b ⟶ a) (cd: c ⟶ d) (dc: d ⟶ c) (ac: a ⟶ c) (bd: b ⟶ d):
       iso_arrows ab ba → iso_arrows cd dc →
        ac ◎ ba = dc ◎ bd →
        bd ◎ ab = cd ◎ ac.
    Proof. (* shows that you only need one half of the diagram to commute for the other half to commute as well*)
     intros [H1 H4] [H2 H5] H3.
     rewrite <- (left_identity (bd ◎ ab)).
     rewrite <- H2.
     rewrite <- (associativity cd dc (comp _ _ _ bd ab)).
     rewrite (associativity dc bd ab).
     rewrite <- H3.
     rewrite <- (associativity ac ba ab).
     rewrite H4.
     rewrite right_identity.
     reflexivity.
    Qed.

    Definition refl_arrows (x: X): isoT x x.
    Proof.
    exists (cat_id, cat_id).
    split; apply left_identity.
    Qed.
  End isomorphy.

  Section initiality.
    Class InitialArrow (x: X): Type := initial_arrow: ∀ y, x ⟶ y.

    Class Initial (x: X) `{InitialArrow x} :=
      initial_arrow_unique: ∀ y f', initial_arrow y = f'.

    Definition initial (x: X): Type := ∀ y: X, sig (λ a: x ⟶ y, ∀ a': x ⟶ y, a = a').

    Lemma initials_unique' (x x': X) `{Ix : Initial x} `{Ix' : Initial x'}:
      iso_arrows (initial_arrow x': x ⟶ x') (initial_arrow x).
    Proof with reflexivity.
    split.
    - rewrite <-(Ix' _ cat_id); symmetry; apply Ix'.
    - rewrite <- (Ix _ cat_id); symmetry; apply Ix.
    Qed.

(*     Lemma initials_unique (x x': X) (a: initial x) (b: initial x'): iso_arrows (a x') (b x).
    Proof.
     split.
      destruct (b x') as [? e1]. rewrite <- e1. apply e1.
     destruct (a x) as [? e0]. rewrite <- e0. apply e0.
    Qed. *)
  End initiality.

  Section products.
    Context {I: Type} (component: I → X).

    Section def.
      Context (product: X).

      Class ElimProduct: Type := tuple_proj: ∀ i, product ⟶ component i.
      Class IntroProduct: Type := make_tuple: ∀ x, (∀ i, x ⟶ component i) → (x ⟶ product).

      Class Product `{ElimProduct} `{IntroProduct} :=
        product_factors: ∀ c ccomp, is_sole (λ h', ∀ i, ccomp i = tuple_proj i ◎ h')
          (make_tuple c ccomp).

      Lemma tuple_round_trip `{Product} (x: X) (h: ∀ i, x ⟶ component i) i:
        tuple_proj i ◎ make_tuple x h = h i.
      Proof. symmetry. apply product_factors. Qed.
    End def.

(*     Lemma products_unique `{Product c} `{Product c'}:
      iso_arrows
        (make_tuple c c' (tuple_proj c'))
        (make_tuple c' c (tuple_proj c)).
    Proof.
    unfold iso_arrows.
    revert c H0 H1 H2 c' H3 H4 H5.
    cut (∀ `{Product x} `{Product y},
      make_tuple x y (tuple_proj y) ◎ make_tuple y x (tuple_proj x) = cat_id).
    - pose proof ((product_factors x x (tuple_proj x)).2) as Q.
    rewrite (Q cat_id)... rewrite Q...
    rewrite associativity.
    repeat rewrite tuple_round_trip...
    rewrite right_identity...
    Qed. *)
  End products.

  Class Producer: Type := product I: (I → X) → X.

  Class HasProducts `{Producer}
    `{∀ I c, ElimProduct c (product I c)}
    `{∀ I c, IntroProduct c (product I c)} :=
      makes_products: ∀ I (c: I → X), Product c (product I c).

(*
  Definition binary_product `{Producer} (x y: X): Product (λ b: bool => if b then x else y) := produce _.
  Definition empty_product `{Producer}: Product (λ f: False => match f with end) := produce _.
*)
(*
  Section freedom.

    Context `{Category B} (forget: X → B) `{!Functor forget forget_arr} (S: B).

    Section candidate.

      Context {x} (inject: S ⟶ forget x).

      Definition proves_free (factor: ∀ x', (S ⟶ forget x') → (x ⟶ x')): PROP :=
          ∀ x' (inject': S ⟶ forget x'), is_sole ((inject' =) ∘ (◎ inject) ∘ fmap forget) (factor _ inject').

      Definition free: PROP := ex proves_free.

    End candidate.

    Lemma frees_unique (x x': X) (inject: S ⟶ forget x) (inject': S ⟶ forget x')
      (factor: ∀ z, (S ⟶ forget z) → (x ⟶ z))
      (factor': ∀ z, (S ⟶ forget z) → (x' ⟶ z)):
       proves_free inject factor → proves_free inject' factor' →
       iso_arrows (factor _ inject') (factor' _ inject).
    Proof with auto; try reflexivity; try apply _.
     intros P Q.
     pose proof (proj1 (P _ inject')) as E.
     pose proof (proj2 (P _ inject)) as R.
     pose proof (proj1 (Q _ inject)) as E'.
     pose proof (proj2 (Q _ inject')) as R'.
     clear P Q.
     unfold compose in *.
     split.
      rewrite (R' cat_id)...
       apply (R' (factor _ inject' ◎ factor' _ inject)).
       rewrite preserves_comp...
       rewrite <- associativity, <- E'...
      rewrite preserves_id, left_identity...
     rewrite (R cat_id)...
      apply (R (factor' _ inject ◎ factor _ inject')).
      rewrite preserves_comp...
      rewrite <- associativity, <- E...
     rewrite preserves_id, left_identity...
    Qed.

  End freedom.
*)
End contents.

(*
Lemma freedom_as_adjunction
  `{Category Base} `{Category Extra}
  `{!Functor (forget: Extra → Base) forget_arr}
  `{!Functor (freeF: Base → Extra) free_arr}
  (eta: id ⇛ forget ∘ freeF)
  (phi: ∀ x y, (x ⟶ forget y) → (freeF x ⟶ y))
  `{!ηAdjunction freeF forget eta phi}:
    ∀ b, proves_free forget b (eta b) (phi b).
Proof. exact (alt_adjunction_η_universal _ _ _ _). Qed.
*)
Arguments Producer : clear implicits.
Arguments HasProducts _ {Arrows Eq CatComp H1 H2} : rename.
Arguments product {X Producer I} _.
