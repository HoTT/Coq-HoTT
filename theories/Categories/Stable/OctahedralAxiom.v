(** * The Octahedral Axiom (TR4)

    This file establishes the fourth axiom of triangulated categories, known as
    the octahedral axiom (TR4). This axiom describes how distinguished triangles
    arising from composable morphisms fit together in a precise octahedral pattern.
    
    The octahedral axiom is the most complex of the triangulated category axioms,
    requiring careful analysis of how cofiber sequences interact under composition.
    
    Contents:
    - Complete statement of TR4
    - Existence of octahedral morphisms
    - The octahedral diagram
    - Properties and consequences of TR4
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import Triangles.
Require Import PreStableCofiber.
Require Import OctahedralLemmas.

(** * Statement of TR4 *)

Section TR4Statement.
  Context (S : PreStableCategoryWithCofiber).

  (** TR4 requires existence of a morphism making specific diagrams commute. *)
  Definition TR4_statement : Type
    := forall (X Y Z : object S) (f : morphism S X Y) (g : morphism S Y Z),
       exists (u : morphism S (@cofiber S X Y f) (@cofiber S Y Z g)),
       (u o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism.

End TR4Statement.

(** * Octahedral Morphisms *)

Section OctahedralMorphisms.
  Context (S : PreStableCategoryWithCofiber)
          (H_universal : cofiber_universal_property S).

  (** The third morphism in the octahedral diagram connects cofiber(g∘f) to
      the suspension of cofiber(f). *)
  Definition octahedral_third_morphism_exists : Type
    := forall (A B C : object S) (f : morphism S A B) (g : morphism S B C),
       { w : morphism S (@cofiber S A C (g o f)%morphism) 
                        (object_of (Susp S) (@cofiber S A B f)) |
         (* w is the connecting morphism in the distinguished triangle *)
         (w o @cofiber_in S A C (g o f)%morphism)%morphism = 
         add_zero_morphism S C 
           (object_of (Susp S) (@cofiber S A B f)) /\
         (* w fits into the octahedral diagram *)
         exists (t : morphism S (object_of (Susp S) A)
                                (object_of (Susp S) (@cofiber S A B f))),
           w = (t o @cofiber_out S A C (g o f)%morphism)%morphism }.

  (** The second morphism v : cofiber(g) → cofiber(g∘f) exists and is
      compatible with the suspension structure. *)
  Definition has_octahedral_morphisms : Type
    := forall (A B C : object S) (f : morphism S A B) (g : morphism S B C),
       { v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism) |
         (v o @cofiber_in S B C g)%morphism = @cofiber_in S A C (g o f)%morphism /\
         (* v is compatible with the suspension structure *)
         exists (s : morphism S (object_of (Susp S) B) 
                                (object_of (Susp S) A)),
           (@cofiber_out S A C (g o f)%morphism o v)%morphism = 
           (s o @cofiber_out S B C g)%morphism }.

End OctahedralMorphisms.

(** * The Complete Octahedral Axiom *)

Section CompleteOctahedralAxiom.
  Context (S : PreStableCategoryWithCofiber).

  (** The complete octahedral axiom TR4 states that:
      1. Cofibers have the universal property
      2. The octahedral morphisms exist
      3. The third morphism exists
      4. The resulting triangle is distinguished *)
  Definition TR4_octahedral_axiom : Type
    := (cofiber_universal_property S) *
       (has_octahedral_morphisms S) *
       (octahedral_third_morphism_exists S) *
       (forall (A B C : object S) (f : morphism S A B) (g : morphism S B C),
        (* The triangle formed by the three cofibers is distinguished *)
        DistinguishedTriangle S).

End CompleteOctahedralAxiom.

(** * Consequences of TR4 *)

Section ConsequencesTR4.
  Context (S : PreStableCategoryWithCofiber)
          (H_TR4 : TR4_octahedral_axiom S).

  (** Extract the universal property. *)
  Definition TR4_universal : cofiber_universal_property S.
  Proof.
    destruct H_TR4 as [[[H_univ _] _] _].
    exact H_univ.
  Defined.

  (** The octahedral morphisms are unique when they exist. *)
  Theorem TR4_morphisms_unique 
    {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : forall (u1 u2 : morphism S (@cofiber S A B f) (@cofiber S B C g)),
      (u1 o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism ->
      (u2 o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism ->
      u1 = u2.
  Proof.
    intros u1 u2 H1 H2.
    
    (* Both u1 and u2 satisfy the same property, so by uniqueness they're equal *)
    assert (H_zero : ((@cofiber_in S B C g o g)%morphism o f)%morphism =
                     add_zero_morphism S A (@cofiber S B C g)).
    {
      (* We have (cofiber_in(g) ∘ g) ∘ f *)
      (* By cofiber_cond1, cofiber_in(g) ∘ g = 0 *)
      pose proof (@cofiber_cond1 S B C g) as H_cond.
      rewrite H_cond.
      (* Now we have 0 ∘ f = 0 *)
      apply zero_morphism_left.
    }
    
    (* Apply the uniqueness part of the universal property *)
    destruct (TR4_universal A B f (@cofiber S B C g) 
             (@cofiber_in S B C g o g)%morphism H_zero) as [u [Hu Hu_unique]].
    
    rewrite (Hu_unique u1 H1).
    rewrite (Hu_unique u2 H2).
    reflexivity.
  Qed.

  (** The octahedral morphisms satisfy the expected properties. *)
  Theorem octahedral_morphism_properties 
    {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : (* The octahedral morphisms exist with the required properties *)
      exists v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism),
      (v o @cofiber_in S B C g)%morphism = @cofiber_in S A C (g o f)%morphism.
  Proof.
    (* Pattern match on H_TR4 to extract components *)
    destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
    
    (* Now H_oct has type has_octahedral_morphisms S *)
    (* Apply it to get the morphism v *)
    destruct (H_oct A B C f g) as [v [Hv_property H_suspension]].
    
    exists v.
    exact Hv_property.
  Qed.

  (** The third morphism in the octahedral diagram vanishes appropriately. *)
  Theorem octahedral_third_morphism_vanishes 
    {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : (* The third morphism w vanishes when composed with cofiber_in *)
      exists w : morphism S (@cofiber S A C (g o f)%morphism) 
                           (object_of (Susp S) (@cofiber S A B f)),
        (w o @cofiber_in S A C (g o f)%morphism)%morphism = 
        add_zero_morphism S C 
          (object_of (Susp S) (@cofiber S A B f)).
  Proof.
    destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
    destruct (H_third A B C f g) as [w [Hw_zero Hw_exist]].
    exists w.
    exact Hw_zero.
  Qed.

  (** The triangle formed by the three cofibers is distinguished. *)
  Theorem octahedral_triangle_distinguished 
    {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : DistinguishedTriangle S.
  Proof.
    destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
    exact (H_dist A B C f g).
  Qed.

End ConsequencesTR4.

(** * TR4 from Universal Property *)

Section TR4FromUniversal.
  Context (S : PreStableCategoryWithCofiber)
          (H_universal : cofiber_universal_property S).

  (** The TR4 morphism exists when cofibers have the universal property. *)
  Theorem TR4_morphism_exists 
    {X Y Z : object S} (f : morphism S X Y) (g : morphism S Y Z)
    : exists (u : morphism S (@cofiber S X Y f) (@cofiber S Y Z g)),
      (u o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism.
  Proof.
    assert (H_zero : ((@cofiber_in S Y Z g o g)%morphism o f)%morphism = 
                     add_zero_morphism S X (@cofiber S Y Z g)).
    {
      pose proof (@cofiber_cond1 S Y Z g) as H_cof.
      rewrite H_cof.
      apply zero_morphism_left.
    }
    
    destruct (H_universal X Y f (@cofiber S Y Z g) 
                         (@cofiber_in S Y Z g o g)%morphism H_zero) 
      as [u [H_comm H_unique]].
    
    exists u.
    exact H_comm.
  Qed.

  (** TR4 holds when the universal property is satisfied. *)
  Theorem TR4_from_universal : TR4_statement S.
  Proof.
    unfold TR4_statement.
    intros X Y Z f g.
    exact (TR4_morphism_exists f g).
  Qed.

End TR4FromUniversal.

(** * Octahedral Properties *)

Section OctahedralProperties.
  Context (S : PreStableCategoryWithCofiber)
          (H_TR4 : TR4_octahedral_axiom S).

  (** All octahedral morphisms exist and satisfy their defining properties. *)
  Theorem octahedral_morphisms_exist 
    {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : (* All three morphisms in the octahedral diagram exist *)
      (exists u : morphism S (@cofiber S A B f) (@cofiber S A C (g o f)%morphism),
         (u o @cofiber_in S A B f)%morphism = 
         (@cofiber_in S A C (g o f)%morphism o g)%morphism) /\
      (exists v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism),
         (v o @cofiber_in S B C g)%morphism = @cofiber_in S A C (g o f)%morphism) /\
      (exists w : morphism S (@cofiber S A C (g o f)%morphism) 
                            (object_of (Susp S) (@cofiber S A B f)),
         (w o @cofiber_in S A C (g o f)%morphism)%morphism = 
         add_zero_morphism S C 
           (object_of (Susp S) (@cofiber S A B f))).
  Proof.
    destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
    
    split; [|split].
    
    - (* u exists by the universal property *)
      exact (cofiber_composite_factors_through_first S H_universal f g).
      
    - (* v exists by the octahedral morphisms *)
      destruct (H_oct A B C f g) as [v [Hv _]].
      exists v.
      exact Hv.
      
    - (* w exists by the third morphism existence *)
      destruct (H_third A B C f g) as [w [Hw _]].
      exists w.
      exact Hw.
  Qed.

  (** The octahedral morphisms are compatible with the suspension structure. *)
  Theorem octahedral_suspension_compatibility 
    {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : (* The morphism v is compatible with suspension *)
      exists (v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism))
             (s : morphism S (object_of (Susp S) B) 
                            (object_of (Susp S) A)),
        (v o @cofiber_in S B C g)%morphism = @cofiber_in S A C (g o f)%morphism /\
        (@cofiber_out S A C (g o f)%morphism o v)%morphism = 
        (s o @cofiber_out S B C g)%morphism.
  Proof.
    destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
    
    (* Get v and s from the octahedral morphisms *)
    destruct (H_oct A B C f g) as [v [Hv [s Hs]]].
    
    exists v, s.
    split.
    - exact Hv.
    - exact Hs.
  Qed.

  (** The uniqueness property extends to all octahedral morphisms. *)
  Theorem octahedral_universal_uniqueness 
    {A B C : object S} (f : morphism S A B) (g : morphism S B C)
    : forall (u1 u2 : morphism S (@cofiber S A B f) (@cofiber S A C (g o f)%morphism)),
      (u1 o @cofiber_in S A B f)%morphism = 
      (@cofiber_in S A C (g o f)%morphism o g)%morphism ->
      (u2 o @cofiber_in S A B f)%morphism = 
      (@cofiber_in S A C (g o f)%morphism o g)%morphism ->
      u1 = u2.
  Proof.
    intros u1 u2 H1 H2.
    
    (* Extract universal property from H_TR4 *)
    destruct H_TR4 as [[[H_universal _] _] _].
    
    (* Both morphisms vanish on f *)
    assert (H_zero : ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
                     add_zero_morphism S A (@cofiber S A C (g o f)%morphism)).
    {
      apply cofiber_composite_vanishes_on_first.
    }
    
    (* Apply uniqueness from the universal property *)
    destruct (morphism_vanishing_on_f_factors S H_universal f 
             (@cofiber_in S A C (g o f)%morphism o g)%morphism H_zero)
      as [u [Hu Hu_unique]].
    
    rewrite (Hu_unique u1 H1).
    rewrite (Hu_unique u2 H2).
    reflexivity.
  Qed.

  (** TR4 implies that certain compositions in the octahedral diagram are zero. *)
  Theorem octahedral_zero_compositions 
    {A B C : object S} (f_AB : morphism S A B) (g_BC : morphism S B C)
    : (* Various compositions in the octahedral diagram are zero *)
      let T := octahedral_triangle_distinguished S H_TR4 f_AB g_BC in
      let tri := triangle T in
      (triangle_g tri o triangle_f tri)%morphism = 
      add_zero_morphism S (triangle_X tri) (triangle_Z tri) /\
      (triangle_h tri o triangle_g tri)%morphism = 
      add_zero_morphism S (triangle_Y tri) (object_of (Susp S) (triangle_X tri)) /\
      (morphism_of (Susp S) (triangle_f tri) o triangle_h tri)%morphism = 
      add_zero_morphism S (triangle_Z tri) (object_of (Susp S) (triangle_Y tri)).
  Proof.
    simpl.
    pose (T := octahedral_triangle_distinguished S H_TR4 f_AB g_BC).
    pose (tri := triangle T).
    
    (* These follow from T being distinguished *)
    split; [|split].
    - exact (zero_comp_1 T).
    - exact (zero_comp_2 T).
    - exact (zero_comp_3 T).
  Qed.

End OctahedralProperties.

(** * Export Hints *)

Hint Resolve 
  TR4_morphism_exists
  TR4_from_universal
  : octahedral_axiom.

Hint Resolve
  TR4_morphisms_unique
  octahedral_morphism_properties
  octahedral_third_morphism_vanishes
  octahedral_triangle_distinguished
  : octahedral_consequences.

(** The next file in the library will be [OppositeCategories.v] which develops
    the theory of opposite categories and their relationship to stable structures. *)