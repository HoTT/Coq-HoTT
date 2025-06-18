(** * Morphisms of Triangles

    A morphism between triangles consists of three morphisms between
    the corresponding objects that make all squares commute.
    
    Contents:
    - Definition of triangle morphisms
    - Identity and composition of triangle morphisms
    - Triangle morphisms form a category
    - Triangle isomorphisms
    - Properties needed for axioms TR2 and TR3
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import Triangles.

(** * Triangle Morphisms *)

(** A morphism of triangles consists of three morphisms making all squares commute. *)
Record TriangleMorphism {S : PreStableCategory} (T1 T2 : Triangle S) := {
  mor_X : morphism S (triangle_X T1) (triangle_X T2);
  mor_Y : morphism S (triangle_Y T1) (triangle_Y T2);
  mor_Z : morphism S (triangle_Z T1) (triangle_Z T2);
  
  (** Commutativity conditions *)
  comm_f : (mor_Y o triangle_f T1)%morphism = (triangle_f T2 o mor_X)%morphism;
  comm_g : (mor_Z o triangle_g T1)%morphism = (triangle_g T2 o mor_Y)%morphism;
  comm_h : (morphism_of (Susp S) mor_X o triangle_h T1)%morphism = 
           (triangle_h T2 o mor_Z)%morphism
}.

Arguments TriangleMorphism {S} T1 T2.
Arguments mor_X {S T1 T2} φ : rename.
Arguments mor_Y {S T1 T2} φ : rename.
Arguments mor_Z {S T1 T2} φ : rename.
Arguments comm_f {S T1 T2} φ : rename.
Arguments comm_g {S T1 T2} φ : rename.
Arguments comm_h {S T1 T2} φ : rename.

(** * Identity Triangle Morphism *)

Definition id_triangle_morphism {S : PreStableCategory} (T : Triangle S)
  : TriangleMorphism T T.
Proof.
  refine {| 
    mor_X := 1%morphism;
    mor_Y := 1%morphism;
    mor_Z := 1%morphism
  |}.
  - rewrite morphism_left_identity.
    rewrite morphism_right_identity.
    reflexivity.
  - rewrite morphism_left_identity.
    rewrite morphism_right_identity.
    reflexivity.
  - rewrite (identity_of (Susp S)).
    rewrite morphism_left_identity.
    rewrite morphism_right_identity.
    reflexivity.
Defined.

(** * Composition of Triangle Morphisms *)

Definition triangle_morphism_compose {S : PreStableCategory}
  {T1 T2 T3 : Triangle S}
  (φ : TriangleMorphism T1 T2)
  (ψ : TriangleMorphism T2 T3)
  : TriangleMorphism T1 T3.
Proof.
  refine {| 
    mor_X := (mor_X ψ o mor_X φ)%morphism;
    mor_Y := (mor_Y ψ o mor_Y φ)%morphism;
    mor_Z := (mor_Z ψ o mor_Z φ)%morphism
  |}.
  - rewrite morphism_associativity.
    rewrite (comm_f φ).
    rewrite <- morphism_associativity.
    rewrite (comm_f ψ).
    rewrite morphism_associativity.
    reflexivity.
  - rewrite morphism_associativity.
    rewrite (comm_g φ).
    rewrite <- morphism_associativity.
    rewrite (comm_g ψ).
    rewrite morphism_associativity.
    reflexivity.
  - simpl.
    rewrite (composition_of (Susp S)).
    rewrite morphism_associativity.
    rewrite (comm_h φ).
    rewrite <- morphism_associativity.
    rewrite (comm_h ψ).
    rewrite morphism_associativity.
    reflexivity.
Defined.

(** * Triangle Morphisms Form a Category *)

Section TriangleMorphismCategory.
  Context {S : PreStableCategory}.

  (** Equality of triangle morphisms. *)
  Lemma triangle_morphism_eq {T1 T2 : Triangle S} 
    (φ ψ : TriangleMorphism T1 T2)
    : mor_X φ = mor_X ψ ->
      mor_Y φ = mor_Y ψ ->
      mor_Z φ = mor_Z ψ ->
      φ = ψ.
  Proof.
    destruct φ as [φX φY φZ φf φg φh].
    destruct ψ as [ψX ψY ψZ ψf ψg ψh].
    simpl. intros HX HY HZ.
    destruct HX, HY, HZ.
    assert (Hf: φf = ψf) by apply path_ishprop.
    assert (Hg: φg = ψg) by apply path_ishprop.
    assert (Hh: φh = ψh) by apply path_ishprop.
    destruct Hf, Hg, Hh.
    reflexivity.
  Qed.

  (** Left identity law. *)
  Lemma triangle_morphism_left_id {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    : triangle_morphism_compose φ (id_triangle_morphism T2) = φ.
  Proof.
    apply triangle_morphism_eq.
    - simpl. apply morphism_left_identity.
    - simpl. apply morphism_left_identity.  
    - simpl. apply morphism_left_identity.
  Qed.

  (** Right identity law. *)
  Lemma triangle_morphism_right_id {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    : triangle_morphism_compose (id_triangle_morphism T1) φ = φ.
  Proof.
    apply triangle_morphism_eq.
    - simpl. apply morphism_right_identity.
    - simpl. apply morphism_right_identity.
    - simpl. apply morphism_right_identity.
  Qed.

  (** Associativity of composition. *)
  Lemma triangle_morphism_assoc 
    {T1 T2 T3 T4 : Triangle S}
    (φ : TriangleMorphism T1 T2)
    (ψ : TriangleMorphism T2 T3)
    (χ : TriangleMorphism T3 T4)
    : triangle_morphism_compose φ (triangle_morphism_compose ψ χ) =
      triangle_morphism_compose (triangle_morphism_compose φ ψ) χ.
  Proof.
    apply triangle_morphism_eq.
    - simpl. apply Category.Core.associativity.
    - simpl. apply Category.Core.associativity.
    - simpl. apply Category.Core.associativity.
  Qed.

  (** Triangles form a category. *)
  Theorem triangles_form_category
    : (forall (T1 T2 T3 T4 : Triangle S) 
              (φ : TriangleMorphism T1 T2)
              (ψ : TriangleMorphism T2 T3)
              (χ : TriangleMorphism T3 T4),
        triangle_morphism_compose φ (triangle_morphism_compose ψ χ) =
        triangle_morphism_compose (triangle_morphism_compose φ ψ) χ) /\
      (forall (T1 T2 : Triangle S) (φ : TriangleMorphism T1 T2),
        triangle_morphism_compose φ (id_triangle_morphism T2) = φ) /\
      (forall (T1 T2 : Triangle S) (φ : TriangleMorphism T1 T2),
        triangle_morphism_compose (id_triangle_morphism T1) φ = φ).
  Proof.
    split; [|split].
    - intros. apply triangle_morphism_assoc.
    - intros. apply triangle_morphism_left_id.
    - intros. apply triangle_morphism_right_id.
  Qed.

End TriangleMorphismCategory.

(** * Isomorphisms *)

(** Basic definition of isomorphism needed for triangle isomorphisms. *)
Definition IsIsomorphism {C : PreCategory} {X Y : object C} (f : morphism C X Y)
  : Type
  := { g : morphism C Y X |
       (g o f = 1)%morphism /\ (f o g = 1)%morphism }.

(** Extract the inverse morphism. *)
Definition iso_inverse {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f)
  : morphism C Y X
  := H.1.

(** * Triangle Isomorphisms *)

(** A triangle isomorphism is a triangle morphism where all three
    component morphisms are isomorphisms. *)
Definition IsTriangleIsomorphism {S : PreStableCategory} {T1 T2 : Triangle S} 
  (φ : TriangleMorphism T1 T2)
  : Type
  := IsIsomorphism (mor_X φ) * 
     IsIsomorphism (mor_Y φ) * 
     IsIsomorphism (mor_Z φ).

(** * Properties for TR2 and TR3 *)

Section PropertiesForAxioms.
  Context {S : PreStableCategory}.

  (** If φ is a triangle isomorphism, we can extract the inverse morphisms. *)
  Definition triangle_iso_inv_X {T1 T2 : Triangle S} 
    {φ : TriangleMorphism T1 T2} (H : IsTriangleIsomorphism φ)
    : morphism S (triangle_X T2) (triangle_X T1).
  Proof.
    destruct H as [[HX HY] HZ].
    exact (iso_inverse HX).
  Defined.

  Definition triangle_iso_inv_Y {T1 T2 : Triangle S} 
    {φ : TriangleMorphism T1 T2} (H : IsTriangleIsomorphism φ)
    : morphism S (triangle_Y T2) (triangle_Y T1).
  Proof.
    destruct H as [[HX HY] HZ].
    exact (iso_inverse HY).
  Defined.

  Definition triangle_iso_inv_Z {T1 T2 : Triangle S} 
    {φ : TriangleMorphism T1 T2} (H : IsTriangleIsomorphism φ)
    : morphism S (triangle_Z T2) (triangle_Z T1).
  Proof.
    destruct H as [[HX HY] HZ].
    exact (iso_inverse HZ).
  Defined.

  (** Statement of TR3 for use in later files. *)
  Definition TR3_statement : Type
    := forall (T : Triangle S) (T' : Triangle S) 
              (φ : TriangleMorphism T T'),
       IsTriangleIsomorphism φ ->
       DistinguishedTriangle S ->
       DistinguishedTriangle S.

End PropertiesForAxioms.

(** * Notation *)

Notation "φ '∘t' ψ" := (triangle_morphism_compose ψ φ) 
  (at level 40, left associativity) : triangle_scope.

Open Scope triangle_scope.

(** * Export Hints *)

Hint Resolve 
  triangle_morphism_left_id 
  triangle_morphism_right_id
  : triangle_morphism.

Hint Rewrite 
  @comm_f @comm_g @comm_h
  : triangle_morphism_simplify.

(** The next file in the library will be [TriangleRotation.v] which defines
    the rotation operation on triangles and shows it preserves the distinguished
    property. *)