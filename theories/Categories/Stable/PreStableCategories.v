(** * Pre-Stable Categories

    A pre-stable category is an additive category equipped with
    suspension and loop functors connected by natural transformations.
    This is a precursor to the notion of a stable category.
    
    Contents:
    - Definition of pre-stable categories
    - The suspension functor Σ
    - The loop functor Ω  
    - Natural transformations η : 1 → ΩΣ and ε : ΣΩ → 1
    - Basic properties of suspension and loop functors
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories.Functor Require Import Identity Composition.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.
Require Import AdditiveCategories.

(** * Pre-Stable Categories *)

Record PreStableCategory := {
  A :> AdditiveCategory;
  
  (** The suspension functor Σ *)
  Susp : AdditiveFunctor A A;
  
  (** The loop functor Ω *)
  Loop : AdditiveFunctor A A;
  
  (** Natural transformation 1 → ΩΣ *)
  eta : NaturalTransformation 1%functor (Loop o Susp)%functor;
  
  (** Natural transformation ΣΩ → 1 *)
  epsilon : NaturalTransformation (Susp o Loop)%functor 1%functor
}.

(** * Basic Properties *)

Section PreStableProperties.
  Context (S : PreStableCategory).

  (** The suspension functor preserves zero morphisms (inherited from being additive). *)
  Theorem susp_preserves_zero_morphisms (X Y : object S)
    : morphism_of (Susp S) (add_zero_morphism S X Y) = 
      add_zero_morphism S (object_of (Susp S) X) (object_of (Susp S) Y).
  Proof.
    apply additive_functor_preserves_zero_morphisms.
  Qed.

  (** The suspension functor preserves identity morphisms. *)
  Lemma susp_preserves_identity (X : object S)
    : morphism_of (Susp S) (1%morphism : morphism S X X) = 
      (1%morphism : morphism S (object_of (Susp S) X) (object_of (Susp S) X)).
  Proof.
    apply (identity_of (Susp S)).
  Qed.

  (** The loop functor preserves zero morphisms. *)
  Theorem loop_preserves_zero_morphisms (X Y : object S)
    : morphism_of (Loop S) (add_zero_morphism S X Y) = 
      add_zero_morphism S (object_of (Loop S) X) (object_of (Loop S) Y).
  Proof.
    apply additive_functor_preserves_zero_morphisms.
  Qed.

  (** The loop functor preserves identity morphisms. *)
  Lemma loop_preserves_identity (X : object S)
    : morphism_of (Loop S) (1%morphism : morphism S X X) = 
      (1%morphism : morphism S (object_of (Loop S) X) (object_of (Loop S) X)).
  Proof.
    apply (identity_of (Loop S)).
  Qed.

  (** Components of the natural transformations. *)
  Definition eta_component (X : object S)
    : morphism S X (object_of ((Loop S) o (Susp S))%functor X)
    := components_of (eta S) X.

  Definition epsilon_component (X : object S)
    : morphism S (object_of ((Susp S) o (Loop S))%functor X) X
    := components_of (epsilon S) X.

(** Naturality squares for eta. *)
  Lemma eta_natural {X Y : object S} (f : morphism S X Y)
    : (eta_component Y o f)%morphism =
      (morphism_of ((Loop S) o (Susp S))%functor f o eta_component X)%morphism.
  Proof.
    apply (commutes (eta S)).
  Qed.

(** Naturality squares for epsilon. *)
  Lemma epsilon_natural {X Y : object S} (f : morphism S X Y)
    : (epsilon_component Y o morphism_of ((Susp S) o (Loop S))%functor f)%morphism =
      (f o epsilon_component X)%morphism.
  Proof.
    apply (commutes (epsilon S)).
  Qed.

  (** Composition properties. *)
  Lemma susp_comp {X Y Z : object S} (f : morphism S X Y) (g : morphism S Y Z)
    : morphism_of (Susp S) (g o f)%morphism =
      (morphism_of (Susp S) g o morphism_of (Susp S) f)%morphism.
  Proof.
    apply composition_of.
  Qed.

  Lemma loop_comp {X Y Z : object S} (f : morphism S X Y) (g : morphism S Y Z)
    : morphism_of (Loop S) (g o f)%morphism =
      (morphism_of (Loop S) g o morphism_of (Loop S) f)%morphism.
  Proof.
    apply composition_of.
  Qed.

End PreStableProperties.

(** * Notation and Abbreviations *)

(** Convenient notation for suspended objects. *)
Notation "'Σ' X" := (object_of (Susp _) X) (at level 30).
Notation "'Ω' X" := (object_of (Loop _) X) (at level 30).

(** Convenient notation for suspended morphisms. *)
Notation "'Σf[' f ']'" := (morphism_of (Susp _) f) (at level 30).
Notation "'Ωf[' f ']'" := (morphism_of (Loop _) f) (at level 30).

(** * Examples of Pre-Stable Categories *)

(** The identity pre-stable structure on an additive category. *)
Definition trivial_prestable (A : AdditiveCategory) : PreStableCategory.
Proof.
  refine {|
    A := A;
    Susp := id_additive_functor A;
    Loop := id_additive_functor A;
    eta := NaturalTransformation.identity 1%functor;
    epsilon := NaturalTransformation.identity 1%functor
  |}.
Defined.

(** * Basic Constructions *)

Section Constructions.
  Context (PS : PreStableCategory).

  (** The n-fold suspension. *)
  Fixpoint susp_n (n : nat) : AdditiveFunctor PS PS :=
    match n with
    | O => id_additive_functor PS
    | S n' => compose_additive_functors (Susp PS) (susp_n n')
    end.

  (** The n-fold loop. *)
  Fixpoint loop_n (n : nat) : AdditiveFunctor PS PS :=
    match n with
    | O => id_additive_functor PS
    | S n' => compose_additive_functors (Loop PS) (loop_n n')
    end.

  (** Basic properties of iterated functors. *)
  Lemma susp_n_zero (X : object PS)
    : object_of (susp_n O) X = X.
  Proof.
    reflexivity.
  Qed.

  Lemma susp_n_succ (n : nat) (X : object PS)
    : object_of (susp_n (S n)) X = object_of (Susp PS) (object_of (susp_n n) X).
  Proof.
    reflexivity.
  Qed.

  Lemma loop_n_zero (X : object PS)
    : object_of (loop_n O) X = X.
  Proof.
    reflexivity.
  Qed.

  Lemma loop_n_succ (n : nat) (X : object PS)
    : object_of (loop_n (S n)) X = object_of (Loop PS) (object_of (loop_n n) X).
  Proof.
    reflexivity.
  Qed.

End Constructions.

(** * Export Hints *)

Hint Resolve 
  susp_preserves_zero_morphisms 
  loop_preserves_zero_morphisms
  susp_preserves_identity
  loop_preserves_identity
  : prestable.

Hint Rewrite 
  @eta_natural @epsilon_natural
  @susp_comp @loop_comp
  : prestable_simplify.

(** The next file in the library will be [PreStableCofiber.v] which introduces
    pre-stable categories with cofiber structures. *)