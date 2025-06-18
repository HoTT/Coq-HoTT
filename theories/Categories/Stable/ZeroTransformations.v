(** * Zero Natural Transformations and Forcing Principles

    This file investigates the consequences of the unit (η) or counit (ε)
    of the (Σ, Ω) adjunction being trivial (i.e., zero transformations).
    These results establish fundamental constraints: for a category to satisfy
    the triangle identities, the adjunction cannot be trivial unless the 
    category itself is degenerate.
    
    Contents:
    - Zero unit and counit definitions
    - Zero transformations break triangle identities
    - Non-triviality conditions
    - The η-Zero Forcing Principle
    - Classification of pre-stable categories by zero behavior
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import SemiStableCategories.

(** * Zero Unit and Counit *)

Section ZeroTransformations.
  Context (PS : PreStableCategory).

  (** A pre-stable category has zero unit if η is the zero transformation. *)
  Definition has_zero_eta : Type
    := forall X : object PS,
       components_of (eta PS) X = 
       add_zero_morphism PS X (object_of ((Loop PS) o (Susp PS))%functor X).

  (** A pre-stable category has zero counit if ε is the zero transformation. *)
  Definition has_zero_epsilon : Type
    := forall X : object PS,
       components_of (epsilon PS) X = 
       add_zero_morphism PS (object_of ((Susp PS) o (Loop PS))%functor X) X.

End ZeroTransformations.

(** * Zero Transformations Break Triangle Identities *)

Section ZeroBreaksTriangles.
  Context (PS : PreStableCategory).

  (** If η is zero, the first triangle identity forces degeneracy. *)
  Theorem zero_eta_breaks_triangle_1
    : has_zero_eta PS ->
      satisfies_triangle_1 PS ->
      forall X : object PS, 
      (1%morphism : morphism PS (object_of (Susp PS) X) (object_of (Susp PS) X)) = 
      add_zero_morphism PS (object_of (Susp PS) X) (object_of (Susp PS) X).
  Proof.
    intros H_zero H_tri X.
    pose proof (H_tri X) as H.
    unfold has_zero_eta in H_zero.
    rewrite H_zero in H.
    rewrite susp_preserves_zero_morphisms in H.
    rewrite zero_morphism_right in H.
    simpl in H.
    exact H^.
  Qed.

  (** If ε is zero, the second triangle identity forces degeneracy. *)
  Theorem zero_epsilon_breaks_triangle_2
    : forall X : object PS,
      satisfies_triangle_2 PS ->
      components_of (epsilon PS) X = 
      add_zero_morphism PS (object_of ((Susp PS) o (Loop PS))%functor X) X ->
      (1%morphism : morphism PS (object_of (Loop PS) X) (object_of (Loop PS) X)) = 
      add_zero_morphism PS (object_of (Loop PS) X) (object_of (Loop PS) X).
  Proof.
    intros X H_tri H_zero.
    pose proof (H_tri X) as H.
    rewrite H_zero in H.
    pose proof (additive_functor_preserves_zero_morphisms (Loop PS) 
      (object_of ((Susp PS) o (Loop PS))%functor X) X) as H_loop_zero.
    rewrite H_loop_zero in H.
    rewrite zero_morphism_left in H.
    simpl in H.
    exact H^.
  Qed.

End ZeroBreaksTriangles.

(** * Non-Triviality Conditions *)

Section NonTriviality.
  Context (PS : PreStableCategory).

  (** A category is non-trivial if some object has non-zero identity. *)
  Definition is_non_trivial : Type
    := exists (X : object PS), 
       (1%morphism : morphism PS X X) <> add_zero_morphism PS X X.

End NonTriviality.

(** * Retraction Properties *)

Section RetractionProperties.
  Context (PS : PreStableCategory).

  (** An object admits a retraction from zero if it can be split off from zero. *)
  Definition admits_retraction_from_zero (X : object PS) : Type
    := exists (i : morphism PS (@zero _ (add_zero PS)) X) 
              (r : morphism PS X (@zero _ (add_zero PS))),
       (r o i)%morphism = 1%morphism.

  (** Zero always admits a retraction from itself. *)
  Theorem zero_always_retractable
    : admits_retraction_from_zero (@zero _ (add_zero PS)).
  Proof.
    exists 1%morphism, 1%morphism.
    apply morphism_left_identity.
  Qed.

  (** If an object admits a retraction from zero, the morphisms are unique. *)
  Theorem retractable_objects_unique_inclusion (X : object PS)
    : admits_retraction_from_zero X ->
      forall (i1 i2 : morphism PS (@zero _ (add_zero PS)) X),
      (exists (r1 : morphism PS X (@zero _ (add_zero PS))),
        (r1 o i1)%morphism = 1%morphism) ->
      (exists (r2 : morphism PS X (@zero _ (add_zero PS))),
        (r2 o i2)%morphism = 1%morphism) ->
      i1 = i2.
  Proof.
    intros H_retract i1 i2 H1 H2.
    (* All morphisms from zero are unique *)
    apply initial_morphism_unique.
    apply (is_initial (add_zero PS)).
  Qed.

  Theorem retractable_objects_unique_retraction (X : object PS)
    : admits_retraction_from_zero X ->
      forall (r1 r2 : morphism PS X (@zero _ (add_zero PS))),
      (exists (i1 : morphism PS (@zero _ (add_zero PS)) X),
        (r1 o i1)%morphism = 1%morphism) ->
      (exists (i2 : morphism PS (@zero _ (add_zero PS)) X),
        (r2 o i2)%morphism = 1%morphism) ->
      r1 = r2.
  Proof.
    intros H_retract r1 r2 H1 H2.
    (* All morphisms to zero are unique *)
    apply terminal_morphism_unique.
    apply (is_terminal (add_zero PS)).
  Qed.

  (** Canonical form of retractions. *)
  Theorem retraction_canonical_form (X : object PS)
    : admits_retraction_from_zero X <->
      ((@center _ (is_terminal (add_zero PS) X) o 
        @center _ (is_initial (add_zero PS) X))%morphism = 
       1%morphism).
  Proof.
    split.
    - (* Forward direction *)
      intros [i [r H_retract]].
      assert (H_i: i = @center _ (is_initial (add_zero PS) X)).
      { apply initial_morphism_unique. apply (is_initial (add_zero PS)). }
      assert (H_r: r = @center _ (is_terminal (add_zero PS) X)).
      { apply terminal_morphism_unique. apply (is_terminal (add_zero PS)). }
      rewrite <- H_i, <- H_r.
      exact H_retract.
    - (* Backward direction *)
      intro H_canon.
      exists (@center _ (is_initial (add_zero PS) X)).
      exists (@center _ (is_terminal (add_zero PS) X)).
      exact H_canon.
  Qed.

End RetractionProperties.

(** * The η-Zero Forcing Principle *)

Section EtaZeroForcing.
  Context (PS : PreStableCategory).

  (** If an object X admits a retraction from zero and η vanishes at X,
      then η must also vanish at zero. This reveals a fundamental constraint
      on the vanishing locus of η. *)
Theorem eta_zero_forcing_principle (X : object PS)
    : admits_retraction_from_zero PS X ->
      components_of (eta PS) X = 
      add_zero_morphism PS X (object_of ((Loop PS) o (Susp PS))%functor X) ->
      components_of (eta PS) (@zero _ (add_zero PS)) = 
      add_zero_morphism PS (@zero _ (add_zero PS)) 
        (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))).
  Proof.
    intros [i [r H_retract]] H_eta_X_zero.
    
    (* Step 1: Establish uniqueness of morphisms involving the zero object *)
    assert (H_i_unique: i = @center _ (is_initial (add_zero PS) X)).
    { apply initial_morphism_unique. apply (is_initial (add_zero PS)). }
    
    assert (H_r_unique: r = @center _ (is_terminal (add_zero PS) X)).
    { apply terminal_morphism_unique. apply (is_terminal (add_zero PS)). }
    
    (* Step 2: Analyze the retraction equation under uniqueness *)
    rewrite H_i_unique, H_r_unique in H_retract.
    
    (* Step 3: The composition of canonical morphisms yields the identity *)
    assert (H_key: (@center _ (is_terminal (add_zero PS) X) o 
                    @center _ (is_initial (add_zero PS) X))%morphism = 
                   (1%morphism : morphism PS (@zero _ (add_zero PS)) 
                                            (@zero _ (add_zero PS)))).
    { exact H_retract. }
    
    (* Step 4: Apply uniqueness to characterize endomorphisms of zero *)
    assert (H_zero_to_zero: 
      (@center _ (is_terminal (add_zero PS) X) o 
       @center _ (is_initial (add_zero PS) X))%morphism = 
      @center _ (is_initial (add_zero PS) (@zero _ (add_zero PS)))).
    { apply initial_morphism_unique. apply (is_initial (add_zero PS)). }
    
    rewrite H_zero_to_zero in H_key.
    
    (* Step 5: Conclude that the canonical endomorphism of zero is the identity *)
    assert (H_zero_id: @center _ (is_initial (add_zero PS) 
                                              (@zero _ (add_zero PS))) = 
                       1%morphism).
    { exact H_key. }
    
    (* Step 6: Apply uniqueness to characterize η at the zero object *)
    apply initial_morphism_unique.
    apply (is_initial (add_zero PS)).
  Qed.

  (** The contrapositive: if η is non-zero at zero, it cannot vanish at any
      retractable object. *)
Theorem eta_nonzero_propagation
    : components_of (eta PS) (@zero _ (add_zero PS)) <> 
      add_zero_morphism PS (@zero _ (add_zero PS)) 
        (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))) ->
      forall (X : object PS),
      admits_retraction_from_zero PS X ->
      components_of (eta PS) X <> 
      add_zero_morphism PS X (object_of ((Loop PS) o (Susp PS))%functor X).
  Proof.
    intros H_eta_nonzero_at_zero X H_retraction H_eta_zero_at_X.
    
    (* Apply the contrapositive of eta_zero_forcing_principle *)
    apply H_eta_nonzero_at_zero.
    apply (eta_zero_forcing_principle X).
    - exact H_retraction.
    - exact H_eta_zero_at_X.
  Qed.

End EtaZeroForcing.

(** * Classification of Pre-Stable Categories *)

Section Classification.
  Context (PS : PreStableCategory).

  (** Class I: η vanishes at zero (and hence at all retractable objects). *)
  Definition class_I_prestable : Type
    := components_of (eta PS) (@zero _ (add_zero PS)) = 
       add_zero_morphism PS (@zero _ (add_zero PS)) 
         (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))).

 (** Class II: η is non-zero at all retractable objects. *)
  Definition class_II_prestable : Type
    := forall (X : object PS),
       admits_retraction_from_zero PS X ->
       components_of (eta PS) X <> 
       add_zero_morphism PS X (object_of ((Loop PS) o (Susp PS))%functor X).

  (** The two classes are mutually exclusive. *)
Theorem prestable_classes_disjoint
    : class_I_prestable ->
      ~(class_II_prestable).
  Proof.
    intros H_class_I H_class_II.
    
    (* Zero itself is retractable *)
    pose proof (zero_always_retractable PS) as H_zero_retract.
    
    (* Apply Class II property to zero *)
    pose proof (H_class_II (@zero _ (add_zero PS)) H_zero_retract) as H_contra.
    
    (* But we know η IS zero at zero from Class I *)
    apply H_contra.
    exact H_class_I.
  Qed.

  (** Class II categories can be tested by checking η at zero. *)
  Theorem class_II_test
    : class_II_prestable ->
      components_of (eta PS) (@zero _ (add_zero PS)) <> 
      add_zero_morphism PS (@zero _ (add_zero PS)) 
        (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))).
  Proof.
    intros H_class_II.
    apply H_class_II.
    apply zero_always_retractable.
  Qed.

End Classification.

(** * Compatible Pairs *)

Section CompatiblePairs.
  Context (PS : PreStableCategory).

  (** A compatible pair is any pair of natural transformations satisfying
      the triangle identities. *)
  Definition compatible_pair
    (η' : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
    (ε' : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor)
    : Type
    := (forall X, (components_of ε' (object_of (Susp PS) X) o
                   morphism_of (Susp PS) (components_of η' X))%morphism = 1%morphism) *
       (forall X, (morphism_of (Loop PS) (components_of ε' X) o
                   components_of η' (object_of (Loop PS) X))%morphism = 1%morphism).

  (** Compatible pairs automatically satisfy the triangle identities. *)
  Theorem compatible_pair_satisfies_triangle_1
    (η : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
    (ε : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor)
    : compatible_pair η ε ->
      forall X,
      (components_of ε (object_of (Susp PS) X) o
       morphism_of (Susp PS) (components_of η X))%morphism = 1%morphism.
  Proof.
    intros [H_tri1 H_tri2] X.
    exact (H_tri1 X).
  Qed.

  (** Any compatible pair interacts predictably with zero morphisms. *)
  Theorem compatible_pair_zero_interaction
    (η : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
    (ε : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor)
    : compatible_pair η ε ->
      forall X,
      (components_of ε (object_of (Susp PS) X) o
       morphism_of (Susp PS) (add_zero_morphism PS X 
         (object_of ((Loop PS) o (Susp PS))%functor X)))%morphism =
      add_zero_morphism PS (object_of (Susp PS) X) (object_of (Susp PS) X).
  Proof.
    intros H_compat X.
    rewrite susp_preserves_zero_morphisms.
    apply zero_morphism_right.
  Qed.

End CompatiblePairs.

(** * Export Hints *)

Hint Unfold
  has_zero_eta
  has_zero_epsilon
  class_I_prestable
  class_II_prestable
  : zero_transformations.

Hint Resolve
  zero_always_retractable
  eta_zero_forcing_principle
  prestable_classes_disjoint
  : zero_transformations.

(** The next file in the library will be [AdvancedStructures.v] which explores
    self-dual triangulated categories and other advanced topics. *)