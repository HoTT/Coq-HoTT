(** * Triangles in Pre-Stable Categories

    Triangles are the fundamental structures in triangulated categories.
    A triangle consists of three objects and three morphisms forming a
    specific pattern with the suspension functor.
    
    Contents:
    - Basic triangle structure
    - Distinguished triangles
    - The identity triangle
    - Basic properties of triangles
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.

(** * Basic Triangle Structure *)

(** A triangle X → Y → Z → ΣX *)
Record Triangle {S : PreStableCategory} := {
  triangle_X : object S;
  triangle_Y : object S;
  triangle_Z : object S;
  triangle_f : morphism S triangle_X triangle_Y;
  triangle_g : morphism S triangle_Y triangle_Z;
  triangle_h : morphism S triangle_Z (object_of (Susp S) triangle_X)
}.

Arguments Triangle S : clear implicits.
Arguments triangle_X {S} t : rename.
Arguments triangle_Y {S} t : rename.
Arguments triangle_Z {S} t : rename.
Arguments triangle_f {S} t : rename.
Arguments triangle_g {S} t : rename.
Arguments triangle_h {S} t : rename.

(** * Distinguished Triangles *)

(** A distinguished triangle is a triangle where consecutive morphisms compose to zero. *)
Record DistinguishedTriangle {S : PreStableCategory} := {
  triangle : Triangle S;
  
  (** g ∘ f = 0 *)
  zero_comp_1 : (triangle_g triangle o triangle_f triangle)%morphism = 
                add_zero_morphism S (triangle_X triangle) (triangle_Z triangle);
  
  (** h ∘ g = 0 *)
  zero_comp_2 : (triangle_h triangle o triangle_g triangle)%morphism = 
                add_zero_morphism S (triangle_Y triangle) (object_of (Susp S) (triangle_X triangle));
  
  (** Σf ∘ h = 0 *)
  zero_comp_3 : (morphism_of (Susp S) (triangle_f triangle) o triangle_h triangle)%morphism = 
                add_zero_morphism S (triangle_Z triangle) (object_of (Susp S) (triangle_Y triangle))
}.

Arguments DistinguishedTriangle S : clear implicits.
Arguments triangle {S} d : rename.
Arguments zero_comp_1 {S} d : rename.
Arguments zero_comp_2 {S} d : rename.
Arguments zero_comp_3 {S} d : rename.

(** * The Identity Triangle *)

Section IdentityTriangle.
  Context {S : PreStableCategory} (X : object S).

  (** Construction of the identity triangle X → X → 0 → ΣX *)
  Definition id_triangle : Triangle S := {|
    triangle_X := X;
    triangle_Y := X;
    triangle_Z := @zero _ (add_zero S);
    triangle_f := 1%morphism;
    triangle_g := @center _ (@is_terminal _ (add_zero S) X);
    triangle_h := @center _ (@is_initial _ (add_zero S) (object_of (Susp S) X))
  |}.

  (** The identity triangle is distinguished. *)
  Theorem id_triangle_distinguished : DistinguishedTriangle S.
  Proof.
    refine {| triangle := id_triangle |}.
    
    - (* zero_comp_1: g ∘ f = 0 *)
      simpl.
      unfold add_zero_morphism.
      (* This should work regardless of how add_zero_morphism is defined *)
      apply terminal_morphism_unique.
      apply (@is_terminal _ (add_zero S)).
    
    - (* zero_comp_2: h ∘ g = 0 *)
      simpl.
      apply terminal_comp_is_zero.
    
    - (* zero_comp_3: Σf ∘ h = 0 *)
      simpl.
      rewrite susp_preserves_identity.
      rewrite morphism_left_identity.
      rewrite <- zero_morphism_from_zero.
      unfold add_zero_morphism.
      reflexivity.
  Defined.

End IdentityTriangle.

(** * Basic Properties *)

Section TriangleProperties.
  Context {S : PreStableCategory}.

  (** Two triangles are equal if all their components are equal. *)
  Lemma triangle_eq (T1 T2 : Triangle S)
    (HX : triangle_X T1 = triangle_X T2)
    (HY : triangle_Y T1 = triangle_Y T2)
    (HZ : triangle_Z T1 = triangle_Z T2)
    (Hf : transport (fun p : object S * object S => morphism S (fst p) (snd p)) 
                    (path_prod (triangle_X T1, triangle_Y T1) (triangle_X T2, triangle_Y T2) HX HY)
                    (triangle_f T1) = triangle_f T2)
    (Hg : transport (fun p : object S * object S => morphism S (fst p) (snd p))
                    (path_prod (triangle_Y T1, triangle_Z T1) (triangle_Y T2, triangle_Z T2) HY HZ)
                    (triangle_g T1) = triangle_g T2)
    (Hh : transport (fun p : object S * object S => morphism S (fst p) (object_of (Susp S) (snd p)))
                    (path_prod (triangle_Z T1, triangle_X T1) (triangle_Z T2, triangle_X T2) HZ HX)
                    (triangle_h T1) = triangle_h T2)
    : T1 = T2.
  Proof.
    destruct T1, T2.
    simpl in *.
    destruct HX, HY, HZ.
    simpl in *.
    destruct Hf, Hg, Hh.
    reflexivity.
  Qed.

  (** Objects of a distinguished triangle. *)
  Definition distinguished_objects (D : DistinguishedTriangle S)
    : (object S) * (object S) * (object S)
    := (triangle_X (triangle D), 
        triangle_Y (triangle D), 
        triangle_Z (triangle D)).

  (** Morphisms of a distinguished triangle. *)
  Definition distinguished_morphisms (D : DistinguishedTriangle S)
    : (morphism S (triangle_X (triangle D)) (triangle_Y (triangle D))) *
      (morphism S (triangle_Y (triangle D)) (triangle_Z (triangle D))) *
      (morphism S (triangle_Z (triangle D)) (object_of (Susp S) (triangle_X (triangle D))))
    := (triangle_f (triangle D), 
        triangle_g (triangle D), 
        triangle_h (triangle D)).

End TriangleProperties.

(** * Export Hints *)

Hint Resolve 
  id_triangle_distinguished
  zero_comp_1 zero_comp_2 zero_comp_3
  : triangle.

(** The next file in the library will be [PreStableCofiber.v] which uses
    these triangle definitions to construct distinguished triangles from
    morphisms using the cofiber construction. *)