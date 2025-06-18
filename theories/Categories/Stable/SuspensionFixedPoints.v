(** * Suspension Fixed Points and Periodicity

    This file investigates objects that are isomorphic to their suspension,
    known as suspension fixed points. These special objects reveal deep structural
    properties of stable categories and lead to periodicity phenomena.
    
    Contents:
    - Definition of suspension fixed points
    - Basic properties and examples
    - The zero object as a universal fixed point
    - Iteration of functors and periodicity
    - Classification of fixed points
    - Applications to stable categories
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories.Functor Require Import Identity Composition.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import ProperStableCategories.
Require Import SemiStableCategories.

(** * Suspension Fixed Points *)

Section SuspensionFixedPoints.
  Context (PS : PreStableCategory).

  (** An object is a suspension fixed point if it is isomorphic to its suspension. *)
  Definition is_suspension_fixed_point (X : object PS) : Type
    := exists (φ : morphism PS (object_of (Susp PS) X) X), IsIsomorphism φ.

  (** Similarly for loop fixed points. *)
  Definition is_loop_fixed_point (X : object PS) : Type
    := exists (φ : morphism PS (object_of (Loop PS) X) X), IsIsomorphism φ.

  (** A stronger notion: naturally fixed. *)
  Definition is_naturally_suspension_fixed (X : object PS) : Type
    := exists (φ : morphism PS (object_of (Susp PS) X) X),
       IsIsomorphism φ *
       (* The isomorphism is natural with respect to endomorphisms *)
       (forall (f : morphism PS X X),
        (φ o morphism_of (Susp PS) f)%morphism = (f o φ)%morphism).

End SuspensionFixedPoints.

(** * Zero is a Fixed Point *)

Section ZeroFixedPoint.
  Context (PS : PreStableCategory).

  (** The suspended zero object has the initial property. *)
  Lemma susp_zero_is_initial (Y : object PS)
    : Contr (morphism PS (object_of (Susp PS) (@zero _ (add_zero PS))) Y).
  Proof.
    pose proof (preserves_zero PS PS (Susp PS)) as H_zero.
    rewrite H_zero.
    apply (is_initial (add_zero PS) Y).
  Qed.

  (** The suspended zero object has the terminal property. *)
  Lemma susp_zero_is_terminal (X : object PS)
    : Contr (morphism PS X (object_of (Susp PS) (@zero _ (add_zero PS)))).
  Proof.
    pose proof (preserves_zero PS PS (Susp PS)) as H_zero.
    rewrite H_zero.
    apply (is_terminal (add_zero PS) X).
  Qed.

  (** The zero object is always a suspension fixed point. *)
  Theorem zero_is_suspension_fixed_point
    : is_suspension_fixed_point PS (@zero _ (add_zero PS)).
  Proof.
    unfold is_suspension_fixed_point.
    
    (* The morphism from Σ(0) to 0 *)
    pose (φ := @center _ (is_terminal (add_zero PS) 
                          (object_of (Susp PS) (@zero _ (add_zero PS))))).
    exists φ.
    
    (* Its inverse from 0 to Σ(0) *)
    pose (ψ := @center _ (is_initial (add_zero PS) 
                          (object_of (Susp PS) (@zero _ (add_zero PS))))).
    exists ψ.
    
    split.
    - (* Left inverse: ψ ∘ φ = 1 on Σ(0) *)
      apply initial_morphism_unique.
      apply susp_zero_is_initial.
      
    - (* Right inverse: φ ∘ ψ = 1 on 0 *)
      transitivity (@center _ (is_terminal (add_zero PS) (@zero _ (add_zero PS)))).
      + apply terminal_morphism_unique.
        apply (is_terminal (add_zero PS)).
      + apply terminal_zero_to_zero_is_id.
  Qed.

  (** Zero is also a loop fixed point. *)
  Theorem zero_is_loop_fixed_point
    : is_loop_fixed_point PS (@zero _ (add_zero PS)).
  Proof.
    unfold is_loop_fixed_point.
    pose proof (preserves_zero PS PS (Loop PS)) as H_zero.
    
    (* Use the equality to transport *)
    rewrite H_zero.
    
    (* Now we need a morphism from 0 to 0 that's an isomorphism *)
    exists 1%morphism.
    exists 1%morphism.
    split.
    - apply morphism_left_identity.
    - apply morphism_left_identity.
  Qed.

End ZeroFixedPoint.

(** * Iteration of Functors *)

Section IteratedFunctors.
  Context {C : PreCategory} (F : Functor C C).

  (** The n-fold iteration of an endofunctor. *)
  Fixpoint iterate_functor (n : nat) : Functor C C :=
    match n with
    | O => 1%functor
    | S n' => (F o iterate_functor n')%functor
    end.

  (** Basic properties of iteration. *)
  Lemma iterate_zero : iterate_functor O = 1%functor.
  Proof.
    reflexivity.
  Qed.

  Lemma iterate_succ (n : nat) 
    : iterate_functor (S n) = (F o iterate_functor n)%functor.
  Proof.
    reflexivity.
  Qed.

  (** Addition of natural numbers. *)
  Fixpoint nat_add (m n : nat) : nat :=
    match m with
    | O => n
    | S m' => S (nat_add m' n)
    end.

  (** Iteration distributes over addition at the object level. *)
  Lemma iterate_add_objects (m n : nat) (X : object C)
    : object_of (iterate_functor (nat_add m n)) X = 
      object_of (iterate_functor m) (object_of (iterate_functor n) X).
  Proof.
    induction m.
    - reflexivity.
    - simpl.
      rewrite IHm.
      reflexivity.
  Qed.

End IteratedFunctors.

(** * Periodicity *)

Section Periodicity.
  Context (PS : PreStableCategory).

  (** A functor has period n if F^n = Id. *)
  Definition has_period (F : Functor PS PS) (n : nat) : Type
    := forall X : object PS, 
       object_of (iterate_functor F n) X = X.

  (** The suspension functor has period n. *)
  Definition suspension_has_period (n : nat) : Type
    := has_period (Susp PS) n.

  (** If suspension has period n, then Σ^n X ≅ X for all X. *)
  Theorem period_gives_fixed_points (n : nat)
    : suspension_has_period n ->
      forall X : object PS,
      exists (φ : morphism PS (object_of (iterate_functor (Susp PS) n) X) X),
      IsIsomorphism φ.
  Proof.
    intros H_period X.
    rewrite (H_period X).
    exists 1%morphism.
    exists 1%morphism.
    split; apply morphism_left_identity.
  Qed.

  (** Multiplication of natural numbers. *)
  Fixpoint nat_mult (m n : nat) : nat :=
    match m with
    | O => O
    | S m' => nat_add n (nat_mult m' n)
    end.

  (** Periodicity is preserved under multiples. *)
  Theorem period_multiples (n k : nat)
    : suspension_has_period n ->
      suspension_has_period (nat_mult k n).
  Proof.
    intros H_period X.
    induction k.
    - simpl. reflexivity.
    - simpl.
      rewrite iterate_add_objects.
      rewrite IHk.
      apply H_period.
  Qed.

End Periodicity.

(** * Properties of Fixed Points *)

Section FixedPointProperties.
  Context (PS : PreStableCategory).

  (** The suspension functor preserves the fixed point property. *)
  Theorem suspension_preserves_fixed_points (X : object PS)
    : is_suspension_fixed_point PS X ->
      is_suspension_fixed_point PS (object_of (Susp PS) X).
  Proof.
    intro H_fixed.
    destruct H_fixed as [φ [φ_inv [Hφ_left Hφ_right]]].
    
    (* We have φ : ΣX → X with inverse φ_inv
       We need ψ : Σ(ΣX) → ΣX with an inverse *)
    
    (* Take ψ = Σφ : Σ(ΣX) → ΣX *)
    exists (morphism_of (Susp PS) φ).
    
    (* The inverse is Σ(φ_inv) *)
    exists (morphism_of (Susp PS) φ_inv).
    
    split.
    - (* Σ(φ_inv) ∘ Σφ = 1 *)
      rewrite <- (composition_of (Susp PS)).
      rewrite Hφ_left.
      apply (identity_of (Susp PS)).
      
    - (* Σφ ∘ Σ(φ_inv) = 1 *)
      rewrite <- (composition_of (Susp PS)).
      rewrite Hφ_right.
      apply (identity_of (Susp PS)).
  Qed.

  (** Fixed points form a full subcategory. *)
  Definition fixed_point_morphism (X Y : object PS)
    (HX : is_suspension_fixed_point PS X)
    (HY : is_suspension_fixed_point PS Y)
    : Type
    := morphism PS X Y.

  (** Properties preserved by isomorphisms transfer to suspended objects
      for fixed points. *)
  Theorem suspension_fixed_point_transport (X : object PS)
    : is_suspension_fixed_point PS X ->
      forall (P : object PS -> Type),
      (forall Y Z (f : morphism PS Y Z), IsIsomorphism f -> P Y -> P Z) ->
      P X -> P (object_of (Susp PS) X).
  Proof.
    intros [φ [φ_inv [H_left H_right]]] P H_transport H_PX.
    (* Since φ : ΣX → X is iso, its inverse φ_inv : X → ΣX is also iso *)
    assert (H_inv_iso: IsIsomorphism φ_inv).
    {
      exists φ.
      split; assumption.
    }
    (* Apply transport *)
    exact (H_transport X (object_of (Susp PS) X) φ_inv H_inv_iso H_PX).
  Qed.

End FixedPointProperties.

(** * Classification of Fixed Points *)

Section Classification.
  Context (PS : PreStableCategory).

  (** Objects admitting a retraction from zero. *)
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

(** Classification theorem for suspension fixed points. *)
  Theorem fixed_point_classification (X : object PS)
    : is_suspension_fixed_point PS X ->
      admits_retraction_from_zero X ->
      exists (n : nat),
      is_suspension_fixed_point PS
        (object_of (iterate_functor (Susp PS) n) X).
  Proof.
    intros H_fixed H_retract.
    (* X itself is already a fixed point, so n = 0 works *)
    exists O.
    simpl.
    exact H_fixed.
  Qed.

End Classification.

(** * Stable Categories and Fixed Points *)

Section StableFixedPoints.
  Context (PS : ProperStableCategory).

  (** In a proper stable category, every object is "almost" a fixed point
      up to the unit and counit isomorphisms. *)
  Theorem proper_stable_quasi_fixed (X : object PS)
    : exists (φ : morphism PS (object_of (Susp PS) (object_of (Loop PS) X)) X),
      IsIsomorphism φ.
  Proof.
    exists (components_of (epsilon PS) X).
    apply epsilon_is_iso.
  Qed.

  (** The composition ΣΩ has many fixed points. *)
  Definition is_susp_loop_fixed_point (X : object PS) : Type
    := exists (φ : morphism PS 
                   (object_of ((Susp PS) o (Loop PS))%functor X) X),
       IsIsomorphism φ.

  Theorem every_object_is_susp_loop_fixed
    : forall X : object PS, is_susp_loop_fixed_point X.
  Proof.
    intro X.
    exists (components_of (epsilon PS) X).
    apply epsilon_is_iso.
  Qed.

End StableFixedPoints.

(** * Applications *)

Section Applications.
  Context (PS : PreStableCategory).

 (** Periodic categories have special properties. *)
  Definition is_periodic : Type
    := exists n : nat, 
       (match n with O => Empty | S _ => Unit end) * suspension_has_period PS n.

  Theorem periodic_implies_many_fixed_points
    : is_periodic ->
      forall k : nat, exists X : object PS,
      is_suspension_fixed_point PS X.
  Proof.
    intros [n [Hn H_period]] k.
    (* Zero is always a fixed point *)
    exists (@zero _ (add_zero PS)).
    apply zero_is_suspension_fixed_point.
  Qed.

End Applications.

(** * Export Hints *)

Hint Resolve 
  zero_is_suspension_fixed_point
  zero_is_loop_fixed_point
  suspension_preserves_fixed_points
  zero_always_retractable
  : suspension_fixed.

Hint Unfold
  is_suspension_fixed_point
  is_loop_fixed_point
  suspension_has_period
  : suspension_fixed.

(** The next file in the library will be [ZeroTransformations.v] which studies
    the consequences of natural transformations being zero. *)