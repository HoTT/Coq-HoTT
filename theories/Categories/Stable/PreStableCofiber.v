(** * Pre-Stable Categories with Cofiber

    A pre-stable category with cofiber extends a pre-stable category with
    a cofiber/mapping cone construction. This provides the foundation for
    constructing distinguished triangles and establishing the axioms of
    triangulated categories.
    
    Contents:
    - PreStableCategoryWithCofiber record
    - Basic properties of cofibers
    - Triangle construction from morphisms
    - Proof that cofiber triangles are distinguished
    - The axiom TR1 for pre-stable categories with cofiber
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import Triangles.

(** * Pre-Stable Categories with Cofiber *)

Record PreStableCategoryWithCofiber := {
  base :> PreStableCategory;
  
  (** The cofiber of a morphism *)
  cofiber : forall {X Y : object base} (f : morphism base X Y), object base;
  
  (** Structure morphisms for the cofiber *)
  cofiber_in : forall {X Y : object base} (f : morphism base X Y), 
               morphism base Y (cofiber f);
  cofiber_out : forall {X Y : object base} (f : morphism base X Y), 
                morphism base (cofiber f) (object_of (Susp base) X);
  
  (** The cofiber axioms *)
  cofiber_cond1 : forall {X Y : object base} (f : morphism base X Y),
    (cofiber_in f o f)%morphism = 
    add_zero_morphism base X (cofiber f);
    
  cofiber_cond2 : forall {X Y : object base} (f : morphism base X Y),
    (cofiber_out f o cofiber_in f)%morphism = 
    add_zero_morphism base Y (object_of (Susp base) X);
    
  cofiber_cond3 : forall {X Y : object base} (f : morphism base X Y),
    (morphism_of (Susp base) f o cofiber_out f)%morphism = 
    add_zero_morphism base (cofiber f) (object_of (Susp base) Y)
}.

(** * Basic Properties of Cofibers *)

Section CofiberProperties.
  Context (S : PreStableCategoryWithCofiber).

  (** Composition with cofiber_in on the right gives zero. *)
  Lemma cofiber_in_comp_right {X Y Z : object S} 
    (f : morphism S X Y) (g : morphism S Z X)
    : (cofiber_in S f o f o g)%morphism = 
      add_zero_morphism S Z (cofiber S f).
  Proof.
    transitivity ((cofiber_in S f o f) o g)%morphism.
    - reflexivity.
    - rewrite (cofiber_cond1 S f).
      apply zero_morphism_left.
  Qed.

  (** Composition with cofiber_out on the left gives zero. *)
  Lemma cofiber_out_comp_left {X Y Z : object S}
    (f : morphism S X Y) (g : morphism S (object_of (Susp S) X) Z)
    : (g o cofiber_out S f o cofiber_in S f)%morphism =
      add_zero_morphism S Y Z.
  Proof.
    assert (H: (g o cofiber_out S f o cofiber_in S f)%morphism = 
               (g o (cofiber_out S f o cofiber_in S f))%morphism).
    { apply morphism_associativity. }
    rewrite H.
    rewrite (cofiber_cond2 S f).
    apply zero_morphism_right.
  Qed.

  (** Suspended f composed with cofiber_out gives zero. *)
  Lemma susp_f_cofiber_out {X Y Z : object S}
    (f : morphism S X Y) (g : morphism S Z (cofiber S f))
    : (morphism_of (Susp S) f o cofiber_out S f o g)%morphism =
      add_zero_morphism S Z (object_of (Susp S) Y).
  Proof.
    transitivity ((morphism_of (Susp S) f o cofiber_out S f) o g)%morphism.
    - reflexivity.
    - rewrite (cofiber_cond3 S f).
      apply zero_morphism_left.
  Qed.

End CofiberProperties.

(** * Triangles from Morphisms *)

Section TriangleFromMorphism.
  Context (S : PreStableCategoryWithCofiber).

  (** Construct a triangle from any morphism using its cofiber. *)
  Definition triangle_from_morphism {X Y : object S} (f : morphism S X Y)
    : Triangle (base S)
    := {|
    triangle_X := X;
    triangle_Y := Y;
    triangle_Z := @cofiber S X Y f;
    triangle_f := f;
    triangle_g := @cofiber_in S X Y f;
    triangle_h := @cofiber_out S X Y f
  |}.

  (** The triangle from a morphism is distinguished. *)
  Theorem cofiber_triangle_distinguished {X Y : object S} (f : morphism S X Y)
    : DistinguishedTriangle (base S).
  Proof.
    refine {| triangle := triangle_from_morphism f |}.
    - simpl. exact (@cofiber_cond1 S X Y f).
    - simpl. exact (@cofiber_cond2 S X Y f).
    - simpl. exact (@cofiber_cond3 S X Y f).
  Defined.

End TriangleFromMorphism.

(** * The Axiom TR1 *)

Section TR1.
  Context (S : PreStableCategoryWithCofiber).

  (** TR1: Every morphism extends to a distinguished triangle. *)
  Theorem TR1 {X Y : object S} (f : morphism S X Y)
    : DistinguishedTriangle (base S).
  Proof.
    exact (cofiber_triangle_distinguished S f).
  Defined.

  (** The triangle constructed by TR1 has the expected form. *)
  Theorem TR1_correct {X Y : object S} (f : morphism S X Y)
    : triangle (TR1 f) = triangle_from_morphism S f.
  Proof.
    reflexivity.
  Qed.

  (** Constructive version of TR1 providing the data explicitly. *)
  Definition TR1_triangle_data {X Y : object (base S)} (f : morphism (base S) X Y)
    : { Z : object (base S) & 
      { g : morphism (base S) Y Z &
      { h : morphism (base S) Z (object_of (Susp (base S)) X) &
      ((g o f)%morphism = add_zero_morphism (base S) X Z) *
      ((h o g)%morphism = add_zero_morphism (base S) Y (object_of (Susp (base S)) X)) *
      ((morphism_of (Susp (base S)) f o h)%morphism = 
       add_zero_morphism (base S) Z (object_of (Susp (base S)) Y)) }}}.
  Proof.
    exists (@cofiber S X Y f).
    exists (@cofiber_in S X Y f).
    exists (@cofiber_out S X Y f).
    split.
    - split.
      + exact (@cofiber_cond1 S X Y f).
      + exact (@cofiber_cond2 S X Y f).
    - exact (@cofiber_cond3 S X Y f).
  Defined.

End TR1.

(** * Mapping Cone Construction *)

Section MappingCone.
  Context (S : PreStableCategoryWithCofiber).

  (** The cofiber is often called the mapping cone in topology. *)
  Definition mapping_cone {X Y : object S} (f : morphism S X Y) : object S
    := @cofiber S X Y f.

  (** Alternative names for the structure maps. *)
  Definition cone_inclusion {X Y : object S} (f : morphism S X Y)
    : morphism S Y (mapping_cone f)
    := @cofiber_in S X Y f.

  Definition cone_projection {X Y : object S} (f : morphism S X Y)
    : morphism S (mapping_cone f) (object_of (Susp S) X)
    := @cofiber_out S X Y f.

End MappingCone.

(** * Export Hints *)

Hint Resolve 
  cofiber_cond1 cofiber_cond2 cofiber_cond3
  cofiber_triangle_distinguished
  : cofiber.

Hint Rewrite 
  @cofiber_in_comp_right @cofiber_out_comp_left @susp_f_cofiber_out
  : cofiber_simplify.

(** The next file in the library will be [SemiStableCategories.v] which defines
    semi-stable categories and the stability hierarchy. *)