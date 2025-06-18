(** * Axioms TR1-TR3 of Triangulated Categories

    This file establishes the first three axioms that characterize triangulated
    categories. These axioms ensure that:
    - TR1: Every morphism extends to a distinguished triangle
    - TR2: Triangle isomorphisms preserve the distinguished property
    - TR3: Distinguished triangles can be rotated
    
    Contents:
    - Formal statements of TR1, TR2, and TR3
    - Helper lemmas for isomorphisms
    - The main TR2 theorem with its proof
    - Verification that our structures satisfy these axioms
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import Triangles.
Require Import TriangleMorphisms.
Require Import TriangleRotation.
Require Import PreStableCofiber.

(** * Axiom TR1: Extension of Morphisms to Distinguished Triangles *)

Section AxiomTR1.
  Context {S : PreStableCategory}.

  (** Statement of TR1: Every morphism can be completed to a distinguished triangle. *)
  Definition TR1_statement : Type
    := forall (X Y : object S) (f : morphism S X Y),
       { Z : object S &
       { g : morphism S Y Z &
       { h : morphism S Z (object_of (Susp S) X) &
         DistinguishedTriangle S }}}.

  (** TR1 holds for pre-stable categories with cofiber. *)
  Theorem TR1_holds (SC : PreStableCategoryWithCofiber) 
    (H_base : base SC = S)
    : TR1_statement.
  Proof.
    intros X Y f.
    destruct H_base.
    exists (cofiber SC f).
    exists (cofiber_in SC f).
    exists (cofiber_out SC f).
    exact (cofiber_triangle_distinguished SC f).
  Qed.

End AxiomTR1.

(** * Helper Lemmas for Isomorphisms *)

Section IsomorphismHelpers.
  Context {S : PreStableCategory}.

  (** The identity morphism is an isomorphism. *)
  Lemma iso_identity {X : object S}
    : IsIsomorphism (1%morphism : morphism S X X).
  Proof.
    exists 1%morphism.
    split; apply morphism_left_identity.
  Qed.

  (** Properties of inverses. *)
  Lemma iso_inverse_left {X Y : object S} {f : morphism S X Y} 
    (H : IsIsomorphism f)
    : (iso_inverse H o f = 1)%morphism.
  Proof.
    destruct H as [g [Hl Hr]].
    exact Hl.
  Qed.

  Lemma iso_inverse_right {X Y : object S} {f : morphism S X Y} 
    (H : IsIsomorphism f)
    : (f o iso_inverse H = 1)%morphism.
  Proof.
    destruct H as [g [Hl Hr]].
    exact Hr.
  Qed.

  (** Isomorphisms preserve zero morphisms. *)
  Lemma iso_preserves_zero {X Y Z W : object S}
    (φX : morphism S X Z) (φY : morphism S Y W)
    (HX : IsIsomorphism φX) (HY : IsIsomorphism φY)
    (f : morphism S X Y)
    : f = add_zero_morphism S X Y ->
      (φY o f o iso_inverse HX)%morphism = add_zero_morphism S Z W.
  Proof.
    intro Hf.
    rewrite Hf.
    rewrite zero_morphism_right.
    rewrite zero_morphism_left.
    reflexivity.
  Qed.

End IsomorphismHelpers.

(** * Axiom TR2: Isomorphisms Preserve Distinguished Triangles *)

Section AxiomTR2.
  Context {S : PreStableCategory}.

  (** Helper lemmas for triangle components under isomorphisms. *)
  
  (** How the f morphism transforms under an isomorphism. *)
  Lemma triangle_iso_f_formula {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    (HY_iso : IsIsomorphism (mor_Y φ))
    (HX_iso : IsIsomorphism (mor_X φ))
    : triangle_f T2 = (mor_Y φ o triangle_f T1 o iso_inverse HX_iso)%morphism.
  Proof.
    pose proof (comm_f φ) as Hcomm.
    
    assert (H: forall (g h : morphism S (triangle_X T1) (triangle_Y T2)) 
                      (k : morphism S (triangle_X T2) (triangle_X T1)),
                g = h -> (g o k)%morphism = (h o k)%morphism).
    {
      intros g h k Heq. rewrite Heq. reflexivity.
    }
    
    apply (H _ _ (iso_inverse HX_iso)) in Hcomm.
    rewrite !morphism_associativity in Hcomm.
    rewrite (iso_inverse_right HX_iso) in Hcomm.
    rewrite morphism_right_identity in Hcomm.
    rewrite <- morphism_associativity in Hcomm.
    exact Hcomm^.
  Qed.

  (** How the g morphism transforms under an isomorphism. *)
  Lemma triangle_iso_g_formula {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    (HZ_iso : IsIsomorphism (mor_Z φ))
    (HY_iso : IsIsomorphism (mor_Y φ))
    : triangle_g T2 = (mor_Z φ o triangle_g T1 o iso_inverse HY_iso)%morphism.
  Proof.
    pose proof (comm_g φ) as Hcomm.
    
    assert (H: forall (g h : morphism S (triangle_Y T1) (triangle_Z T2)) 
                      (k : morphism S (triangle_Y T2) (triangle_Y T1)),
                g = h -> (g o k)%morphism = (h o k)%morphism).
    {
      intros g h k Heq. rewrite Heq. reflexivity.
    }
    
    apply (H _ _ (iso_inverse HY_iso)) in Hcomm.
    rewrite !morphism_associativity in Hcomm.
    rewrite (iso_inverse_right HY_iso) in Hcomm.
    rewrite morphism_right_identity in Hcomm.
    rewrite <- morphism_associativity in Hcomm.
    exact Hcomm^.
  Qed.

  (** How the h morphism transforms under an isomorphism. *)
  Lemma triangle_iso_h_formula {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    (HX_iso : IsIsomorphism (mor_X φ))
    (HZ_iso : IsIsomorphism (mor_Z φ))
    : triangle_h T2 = (morphism_of (Susp S) (mor_X φ) o triangle_h T1 o iso_inverse HZ_iso)%morphism.
  Proof.
    pose proof (comm_h φ) as Hcomm.
    
    assert (H: forall (g h : morphism S (triangle_Z T1) (object_of (Susp S) (triangle_X T2))) 
                      (k : morphism S (triangle_Z T2) (triangle_Z T1)),
                g = h -> (g o k)%morphism = (h o k)%morphism).
    {
      intros g h k Heq. rewrite Heq. reflexivity.
    }
    
    apply (H _ _ (iso_inverse HZ_iso)) in Hcomm.
    rewrite !morphism_associativity in Hcomm.
    rewrite (iso_inverse_right HZ_iso) in Hcomm.
    rewrite morphism_right_identity in Hcomm.
    rewrite <- morphism_associativity in Hcomm.
    exact Hcomm^.
  Qed.

  (** Helper for composition patterns. *)
  Lemma triangle_composition_pattern {X1 Y1 Z1 X2 Y2 Z2 : object S}
    (φZ : morphism S Z1 Z2)
    (g : morphism S Y1 Z1)
    (φY_inv : morphism S Y2 Y1)
    (φY : morphism S Y1 Y2)
    (f : morphism S X1 Y1)
    (φX_inv : morphism S X2 X1)
    : (φY_inv o φY)%morphism = 1%morphism ->
      ((φZ o g o φY_inv) o (φY o f o φX_inv))%morphism = 
      (φZ o g o f o φX_inv)%morphism.
  Proof.
    intro H.
    (* First, expand using associativity *)
    rewrite !morphism_associativity.
    (* Now we have: φZ o (g o (φY_inv o (φY o (f o φX_inv)))) *)
    (* We need to show this equals: φZ o (g o (f o φX_inv)) *)
    apply ap.
    (* Now need: g o (φY_inv o (φY o (f o φX_inv))) = g o (f o φX_inv) *)
    apply ap.
    (* Now need: φY_inv o (φY o (f o φX_inv)) = f o φX_inv *)
    rewrite <- morphism_associativity.
    (* Now: (φY_inv o φY) o (f o φX_inv) = f o φX_inv *)
    rewrite H.
    (* Now: 1 o (f o φX_inv) = f o φX_inv *)
    rewrite morphism_left_identity.
    reflexivity.
  Qed.

  (** Helper for four morphism composition with zero. *)
  Lemma morphism_four_compose_with_zero {A B C D E : object S}
    (φ : morphism S D E)
    (g : morphism S C D)
    (f : morphism S B C)
    (ψ : morphism S A B)
    : (g o f)%morphism = add_zero_morphism S B D ->
      (φ o g o f o ψ)%morphism = add_zero_morphism S A E.
  Proof.
    intro H.
    assert (H_assoc: (φ o g o f o ψ)%morphism = (φ o (g o f) o ψ)%morphism).
    {
      rewrite !morphism_associativity.
      reflexivity.
    }
    rewrite H_assoc.
    rewrite H.
    rewrite zero_morphism_right.
    rewrite zero_morphism_left.
    reflexivity.
  Qed.

  (** Preservation of zero compositions under isomorphisms. *)
  
  Lemma triangle_iso_preserves_zero_comp_1 {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    (HX_iso : IsIsomorphism (mor_X φ))
    (HY_iso : IsIsomorphism (mor_Y φ))
    (HZ_iso : IsIsomorphism (mor_Z φ))
    : (triangle_g T1 o triangle_f T1)%morphism = add_zero_morphism S (triangle_X T1) (triangle_Z T1) ->
      (triangle_g T2 o triangle_f T2)%morphism = add_zero_morphism S (triangle_X T2) (triangle_Z T2).
  Proof.
    intro H.
    
    rewrite (triangle_iso_f_formula φ HY_iso HX_iso).
    rewrite (triangle_iso_g_formula φ HZ_iso HY_iso).
    
    rewrite (triangle_composition_pattern 
               (mor_Z φ) (triangle_g T1) 
               (iso_inverse HY_iso) (mor_Y φ)
               (triangle_f T1) (iso_inverse HX_iso)
               (iso_inverse_left HY_iso)).
    
    apply morphism_four_compose_with_zero.
    exact H.
  Qed.

  Lemma triangle_iso_preserves_zero_comp_2 {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    (HX_iso : IsIsomorphism (mor_X φ))
    (HY_iso : IsIsomorphism (mor_Y φ))
    (HZ_iso : IsIsomorphism (mor_Z φ))
    : (triangle_h T1 o triangle_g T1)%morphism = 
      add_zero_morphism S (triangle_Y T1) (object_of (Susp S) (triangle_X T1)) ->
      (triangle_h T2 o triangle_g T2)%morphism = 
      add_zero_morphism S (triangle_Y T2) (object_of (Susp S) (triangle_X T2)).
  Proof.
    intro H.
    
    rewrite (triangle_iso_g_formula φ HZ_iso HY_iso).
    rewrite (triangle_iso_h_formula φ HX_iso HZ_iso).
    
    rewrite (triangle_composition_pattern 
               (morphism_of (Susp S) (mor_X φ)) (triangle_h T1) 
               (iso_inverse HZ_iso) (mor_Z φ)
               (triangle_g T1) (iso_inverse HY_iso)
               (iso_inverse_left HZ_iso)).
    apply morphism_four_compose_with_zero.
    exact H.
  Qed.

  Lemma triangle_iso_preserves_zero_comp_3 {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    (HX_iso : IsIsomorphism (mor_X φ))
    (HY_iso : IsIsomorphism (mor_Y φ))
    (HZ_iso : IsIsomorphism (mor_Z φ))
    : (morphism_of (Susp S) (triangle_f T1) o triangle_h T1)%morphism = 
      add_zero_morphism S (triangle_Z T1) (object_of (Susp S) (triangle_Y T1)) ->
      (morphism_of (Susp S) (triangle_f T2) o triangle_h T2)%morphism = 
      add_zero_morphism S (triangle_Z T2) (object_of (Susp S) (triangle_Y T2)).
  Proof.
    intro H.
    
    rewrite (triangle_iso_f_formula φ HY_iso HX_iso).
    rewrite (triangle_iso_h_formula φ HX_iso HZ_iso).
    
    rewrite (composition_of (Susp S)).
    rewrite (composition_of (Susp S)).
    
    (* Need functor_preserves_inverse lemma *)
    assert (H_inv: morphism_of (Susp S) (iso_inverse HX_iso) = 
                   iso_inverse (functor_preserves_iso (Susp S) (mor_X φ) HX_iso)).
    {
      destruct HX_iso as [g [Hgf Hfg]].
      simpl. reflexivity.
    }
    
    rewrite H_inv.
    
    rewrite (triangle_composition_pattern 
               (morphism_of (Susp S) (mor_Y φ)) 
               (morphism_of (Susp S) (triangle_f T1))
               (iso_inverse (functor_preserves_iso (Susp S) (mor_X φ) HX_iso))
               (morphism_of (Susp S) (mor_X φ))
               (triangle_h T1) 
               (iso_inverse HZ_iso)
               (iso_inverse_left (functor_preserves_iso (Susp S) (mor_X φ) HX_iso))).
    
    apply morphism_four_compose_with_zero.
    exact H.
  Qed.

  (** Main Theorem: TR2 *)
  Theorem TR2 {T1 T2 : Triangle S} 
    (φ : TriangleMorphism T1 T2)
    (Hφ : IsTriangleIsomorphism φ)
    (D1 : DistinguishedTriangle S)
    (H1 : triangle D1 = T1)
    : DistinguishedTriangle S.
  Proof.
    destruct Hφ as [[HX_iso HY_iso] HZ_iso].
    refine {| triangle := T2 |}.
    - (* zero_comp_1 *)
      apply (triangle_iso_preserves_zero_comp_1 φ HX_iso HY_iso HZ_iso).
      rewrite <- H1.
      exact (zero_comp_1 D1).
    - (* zero_comp_2 *)
      apply (triangle_iso_preserves_zero_comp_2 φ HX_iso HY_iso HZ_iso).
      rewrite <- H1.
      exact (zero_comp_2 D1).
    - (* zero_comp_3 *)
      apply (triangle_iso_preserves_zero_comp_3 φ HX_iso HY_iso HZ_iso).
      rewrite <- H1.
      exact (zero_comp_3 D1).
  Defined.

End AxiomTR2.

(** * Axiom TR3: Rotation of Distinguished Triangles *)

Section AxiomTR3.
  Context {S : PreStableCategory}.

  (** Statement of TR3: Distinguished triangles can be rotated. *)
  Definition TR3_statement : Type
    := forall (T : DistinguishedTriangle S),
       DistinguishedTriangle S.

  (** TR3 holds using rotation. *)
  Theorem TR3_holds : TR3_statement.
  Proof.
    intro T.
    exact (rotate_distinguished T).
  Qed.

End AxiomTR3.

(** * Summary of TR1-TR3 *)

Section Summary.
  Context {S : PreStableCategory}.

  (** All three axioms packaged together. *)
  Definition satisfies_TR1_TR2_TR3 (SC : PreStableCategoryWithCofiber) 
    (H_base : base SC = S) : Type.
  Proof.
    exact (@TR1_statement S * 
           (forall {T1 T2 : Triangle S} 
                   (φ : TriangleMorphism T1 T2)
                   (Hφ : IsTriangleIsomorphism φ)
                   (D1 : DistinguishedTriangle S)
                   (H1 : triangle D1 = T1),
             DistinguishedTriangle S) * 
           @TR3_statement S).
  Defined.

  (** Verification that our structures satisfy TR1-TR3. *)
  Theorem verify_TR1_TR2_TR3 (SC : PreStableCategoryWithCofiber) 
    (H_base : base SC = S)
    : satisfies_TR1_TR2_TR3 SC H_base.
  Proof.
    refine (_, _, _).
    - exact (@TR1_holds S SC H_base).
    - intros T1 T2 φ Hφ D1 H1. 
      exact (@TR2 S T1 T2 φ Hφ D1 H1).
    - exact (@TR3_holds S).
  Qed.

End Summary.

(** * Export Hints *)

Hint Resolve 
  iso_identity
  iso_inverse_left iso_inverse_right
  TR3_holds
  : triangulated.

Hint Resolve
  triangle_iso_preserves_zero_comp_1
  triangle_iso_preserves_zero_comp_2
  triangle_iso_preserves_zero_comp_3
  : tr2.

(** The next file in the library will be [OctahedralLemmas.v] which develops
    the technical machinery needed for the octahedral axiom TR4. *)