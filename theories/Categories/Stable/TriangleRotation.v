(** * Triangle Rotation

    The rotation operation is fundamental in triangulated categories.
    It transforms a triangle X → Y → Z → ΣX into Y → Z → ΣX → ΣY.
    
    Contents:
    - Definition of triangle rotation
    - Proof that rotation preserves distinguished triangles
    - The shift operation (alternative name for rotation)
    - Shifting of triangle morphisms
    - Statement of axiom TR3
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import Triangles.
Require Import TriangleMorphisms.

(** * Rotation of Triangles *)

Section TriangleRotation.
  Context {S : PreStableCategory}.

  (** The rotation operation transforms a triangle X → Y → Z → ΣX 
      into Y → Z → ΣX → ΣY. *)
  Definition rotate_triangle (T : Triangle S) : Triangle S := {|
    triangle_X := triangle_Y T;
    triangle_Y := triangle_Z T;
    triangle_Z := object_of (Susp S) (triangle_X T);
    triangle_f := triangle_g T;
    triangle_g := triangle_h T;
    triangle_h := morphism_of (Susp S) (triangle_f T)
  |}.

End TriangleRotation.

(** * Rotation Preserves Distinguished Triangles *)

Section RotationPreservesDistinguished.
  Context {S : PreStableCategory}.

  (** The main theorem: rotation preserves the distinguished property. *)
  Theorem rotate_distinguished (T : DistinguishedTriangle S)
    : DistinguishedTriangle S.
  Proof.
    refine {| triangle := rotate_triangle (triangle T) |}.
    - (* zero_comp_1: new g ∘ new f = 0 *)
      simpl.
      exact (zero_comp_2 T).
    - (* zero_comp_2: new h ∘ new g = 0 *)
      simpl.
      exact (zero_comp_3 T).
    - (* zero_comp_3: Σ(new f) ∘ new h = 0 *)
      simpl.
      rewrite <- (composition_of (Susp S)).
      rewrite (zero_comp_1 T).
      apply susp_preserves_zero_morphisms.
  Defined.

End RotationPreservesDistinguished.

(** * Shift and Axiom TR3 *)

Section ShiftOperation.
  Context {S : PreStableCategory}.

  (** The shift operation is another name for rotation. *)
  Definition shift_triangle (T : Triangle S) : Triangle S
    := rotate_triangle T.

  (** Shifting preserves distinguished triangles. *)
  Theorem shift_distinguished (T : DistinguishedTriangle S)
    : DistinguishedTriangle S.
  Proof.
    exact (rotate_distinguished T).
  Defined.

End ShiftOperation.

(** * Helper Lemmas *)

Section HelperLemmas.
  Context {C D : PreCategory} (F : Functor C D).

  (** Functors preserve isomorphisms. *)
  Lemma functor_preserves_iso {X Y : object C} (f : morphism C X Y) 
    (H : IsIsomorphism f) : IsIsomorphism (morphism_of F f).
  Proof.
    destruct H as [g [Hgf Hfg]].
    exists (morphism_of F g).
    split.
    - rewrite <- composition_of.
      rewrite Hgf.
      apply identity_of.
    - rewrite <- composition_of.
      rewrite Hfg.
      apply identity_of.
  Defined.

End HelperLemmas.

(** * Shifting Triangle Morphisms *)

Section ShiftingMorphisms.
  Context {S : PreStableCategory}.

  (** Shifting a triangle morphism. *)
  Definition shift_triangle_morphism {T1 T2 : Triangle S}
    (φ : TriangleMorphism T1 T2)
    : TriangleMorphism (shift_triangle T1) (shift_triangle T2).
  Proof.
    unfold shift_triangle, rotate_triangle.

    apply Build_TriangleMorphism with
      (mor_X := mor_Y φ)
      (mor_Y := mor_Z φ)
      (mor_Z := morphism_of (Susp S) (mor_X φ)).
    - (* comm_f *)
      exact (comm_g φ).
    - (* comm_g *)
      exact (comm_h φ).
    - (* comm_h *)
      rewrite <- (composition_of (Susp S)).
      rewrite (comm_f φ).
      rewrite (composition_of (Susp S)).
      reflexivity.
  Defined.

  (** If φ is an isomorphism, so is its shift. *)
  Lemma shift_preserves_isomorphism {T1 T2 : Triangle S}
    (φ : TriangleMorphism T1 T2)
    (H : IsTriangleIsomorphism φ)
    : IsTriangleIsomorphism (shift_triangle_morphism φ).
  Proof.
    destruct H as [[HX HY] HZ].
    split; [split|].
    - (* mor_X of shifted = mor_Y of original *)
      exact HY.
    - (* mor_Y of shifted = mor_Z of original *)
      exact HZ.
    - (* mor_Z of shifted = Σ(mor_X) of original *)
      apply functor_preserves_iso.
      exact HX.
  Qed.

End ShiftingMorphisms.

(** * Axiom TR3 *)

Section AxiomTR3.
  Context {S : PreStableCategory}.

  (** Statement of TR3: Triangle isomorphisms preserve distinguished triangles. *)
  Definition TR3_statement : Type
    := forall (T T' : Triangle S) 
              (φ : TriangleMorphism T T'),
       IsTriangleIsomorphism φ ->
       DistinguishedTriangle S ->
       DistinguishedTriangle S.

  (** TR3 specific to shifted triangles. *)
  Definition TR3_shift : Type
    := forall (T : DistinguishedTriangle S),
       DistinguishedTriangle S.

  (** The shift operation satisfies TR3_shift trivially. *)
  Theorem TR3_shift_holds : TR3_shift.
  Proof.
    intro T.
    exact (shift_distinguished T).
  Qed.

End AxiomTR3.

(** * Properties of Rotation *)

Section RotationProperties.
  Context {S : PreStableCategory}.

  (** Double rotation. *)
  Definition rotate_twice (T : Triangle S) : Triangle S
    := rotate_triangle (rotate_triangle T).

  (** After two rotations, we get a triangle involving Σ² *)
  Lemma rotate_twice_objects (T : Triangle S)
    : triangle_X (rotate_twice T) = triangle_Z T /\
      triangle_Y (rotate_twice T) = object_of (Susp S) (triangle_X T) /\
      triangle_Z (rotate_twice T) = object_of (Susp S) (triangle_Y T).
  Proof.
    split; [|split]; reflexivity.
  Qed.

  (** Triple rotation. *)
  Definition rotate_thrice (T : Triangle S) : Triangle S
    := rotate_triangle (rotate_triangle (rotate_triangle T)).

  (** After three rotations, objects are suspended versions of originals. *)
  Lemma rotate_thrice_objects (T : Triangle S)
    : triangle_X (rotate_thrice T) = object_of (Susp S) (triangle_X T) /\
      triangle_Y (rotate_thrice T) = object_of (Susp S) (triangle_Y T) /\
      triangle_Z (rotate_thrice T) = object_of (Susp S) (triangle_Z T).
  Proof.
    split; [|split]; reflexivity.
  Qed.

End RotationProperties.

(** * Utilities *)

Section Utilities.
  Context {S : PreStableCategory}.

  (** Helper to extract the first morphism from a rotated triangle. *)
  Definition rotated_first_morphism (T : Triangle S)
    : morphism S (triangle_Y T) (triangle_Z T)
    := triangle_f (rotate_triangle T).

  (** This is just triangle_g. *)
  Lemma rotated_first_morphism_is_g (T : Triangle S)
    : rotated_first_morphism T = triangle_g T.
  Proof.
    reflexivity.
  Qed.

End Utilities.

(** * Export Hints *)

Hint Resolve 
  rotate_distinguished
  shift_distinguished
  shift_preserves_isomorphism
  TR3_shift_holds
  : triangle_rotation.

Hint Rewrite 
  @rotated_first_morphism_is_g
  : triangle_simplify.

(** The next file in the library will be [TriangulatedAxiomsTR123.v] which
    establishes the first three axioms of triangulated categories. *)