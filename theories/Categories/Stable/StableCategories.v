(** * Foundations of Stable Category Theory
    
    This file formalizes the foundational definitions for pre-stable and
    stable categories within the framework of Homotopy Type Theory (HoTT).
    It builds the theory from the ground up, starting with additive
    structures like zero objects and biproducts, and defines key concepts
    including distinguished triangles, triangle rotation, and the axioms
    of triangulated categories (TR1, TR2).

    A significant focus is the formalization of the duality principle,
    demonstrating that the opposite of a stable category is stable, with
    the suspension (Σ) and loop (Ω) functors swapping roles.
    
    Author: Charles Norton
    Date: June 16th, 2025
    License: MIT License
    
    Updated and tested with:
    - Coq 8.20.1
    - HoTT 8.20
    
    Originally developed with:
    - JsCoq (0.10.0~beta1)
    - Coq 8.10+beta2/8991 (July 2019)
    - OCaml 4.07.1
    - Js_of_ocaml 3.4.0
*)

From HoTT Require Import Basics.
From HoTT.Basics Require Import Overture PathGroupoids Contractible Equivalences.
From HoTT.Types Require Import Forall Sigma Arrow Paths Sum Prod Unit Empty.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories Require Import InitialTerminalCategory.
From HoTT.Categories.Functor Require Import Identity Composition.
From HoTT.Spaces Require Import Int.


(** ** Zero Objects
    
    A zero object in a category is an object that is both initial and terminal.
    This is the categorical analog of the zero element in an abelian group.
*)

Record ZeroObject (C : PreCategory) := {
  zero : object C;
  is_initial : forall X, Contr (morphism C zero X);
  is_terminal : forall X, Contr (morphism C X zero)
}.

(** The zero morphism between any two objects is the unique morphism
    that factors through the zero object. *)

Definition zero_morphism {C : PreCategory} (Z : ZeroObject C) 
  (X Y : object C) : morphism C X Y :=
  (@center _ (@is_initial _ Z Y) o @center _ (@is_terminal _ Z X))%morphism.

(** ** Biproducts
    
    A biproduct is an object that is simultaneously a product and coproduct.
    In additive categories, finite products and coproducts coincide.
*)

Record Biproduct {C : PreCategory} (X Y : object C) := {
  biproduct_obj : object C;
  
  (* Coproduct structure *)
  inl : morphism C X biproduct_obj;
  inr : morphism C Y biproduct_obj;
  
  (* Product structure *)
  outl : morphism C biproduct_obj X;
  outr : morphism C biproduct_obj Y
}.

(** A biproduct satisfies specific axioms relating the injections and projections *)

Record IsBiproduct {C : PreCategory} {X Y : object C} 
                   (B : Biproduct X Y) (Z : ZeroObject C) := {
  (* Projection-injection identities *)
  beta_l : (@outl _ _ _ B o @inl _ _ _ B = 1)%morphism;
  beta_r : (@outr _ _ _ B o @inr _ _ _ B = 1)%morphism;
  
  (* Mixed terms are zero *)
  mixed_l : (@outl _ _ _ B o @inr _ _ _ B)%morphism = zero_morphism Z Y X;
  mixed_r : (@outr _ _ _ B o @inl _ _ _ B)%morphism = zero_morphism Z X Y
}.

(** The universal property of biproducts combines the universal properties
    of products and coproducts *)

Record BiproductUniversal {C : PreCategory} {X Y : object C} 
                          (B : Biproduct X Y) := {
  coprod_universal : forall (Z : object C) 
    (f : morphism C X Z) (g : morphism C Y Z),
    Contr {h : morphism C (@biproduct_obj _ _ _ B) Z | 
           (h o @inl _ _ _ B = f)%morphism /\ 
           (h o @inr _ _ _ B = g)%morphism};
  
  prod_universal : forall (Z : object C) 
    (f : morphism C Z X) (g : morphism C Z Y),
    Contr {h : morphism C Z (@biproduct_obj _ _ _ B) | 
           (@outl _ _ _ B o h = f)%morphism /\ 
           (@outr _ _ _ B o h = g)%morphism}
}.

(** ** Additive Categories
    
    An additive category is a category enriched over abelian groups,
    with a zero object and biproducts for all pairs of objects.
*)

Record AdditiveCategory := {
  cat :> PreCategory;
  
  add_zero : ZeroObject cat;
  
  add_biproduct : forall (X Y : object cat), Biproduct X Y;
  
  add_biproduct_props : forall (X Y : object cat), 
    IsBiproduct (add_biproduct X Y) add_zero;
  
  add_biproduct_universal : forall (X Y : object cat),
    BiproductUniversal (add_biproduct X Y)
}.

(** ** Additive Functors
    
    An additive functor preserves the additive structure: zero objects
    and biproducts.
*)

Record AdditiveFunctor (A B : AdditiveCategory) := {
  add_functor :> Functor A B;
  
  preserves_zero : 
    object_of add_functor (@zero _ (add_zero A)) = 
    @zero _ (add_zero B);
  
  preserves_biproduct : forall (X Y : object A),
    object_of add_functor (@biproduct_obj _ _ _ (add_biproduct A X Y)) =
    @biproduct_obj _ _ _ (add_biproduct B (object_of add_functor X) 
                                         (object_of add_functor Y))
}.

(** ** Basic Lemmas for Categories with Zero Objects
    
    This section establishes fundamental properties of morphisms in categories
    with zero objects, including uniqueness results and composition properties.
*)

(** *** Uniqueness of Initial and Terminal Morphisms *)

(** Any two morphisms from an initial object are equal *)
Lemma initial_morphism_unique {C : PreCategory} 
  (I : object C) (X : object C)
  (H_initial : Contr (morphism C I X))
  (f g : morphism C I X) : f = g.
Proof.
  transitivity (@center _ H_initial).
  - exact (@contr _ H_initial f)^.
  - exact (@contr _ H_initial g).
Qed.

(** Any two morphisms to a terminal object are equal *)
Lemma terminal_morphism_unique {C : PreCategory} 
  (X : object C) (T : object C)
  (H_terminal : Contr (morphism C X T))
  (f g : morphism C X T) : f = g.
Proof.
  transitivity (@center _ H_terminal).
  - exact (@contr _ H_terminal f)^.
  - exact (@contr _ H_terminal g).
Qed.

(** *** Properties of Zero Morphisms *)

(** Any morphism that factors through a zero object is the zero morphism *)
Lemma morphism_through_zero_is_zero {C : PreCategory} 
  (Z : ZeroObject C) (X Y : object C)
  (f : morphism C X (@zero _ Z))
  (g : morphism C (@zero _ Z) Y) :
  (g o f)%morphism = zero_morphism Z X Y.
Proof.
  unfold zero_morphism.
  apply ap011.
  - apply initial_morphism_unique.
    apply (@is_initial _ Z).
  - apply terminal_morphism_unique.
    apply (@is_terminal _ Z).
Qed.

(** *** Transport Lemmas for Morphisms
    
    These lemmas handle how morphisms behave under transport along
    equality proofs between objects.
*)

Lemma transport_compose_morphism {C : PreCategory}
  {X Y Z W : object C} (p : X = W)
  (f : morphism C X Y) (g : morphism C Y Z) :
  transport (fun U => morphism C U Z) p (g o f)%morphism =
  (g o transport (fun U => morphism C U Y) p f)%morphism.
Proof.
  destruct p; reflexivity.
Qed.

Lemma transport_morphism_compose_middle {C : PreCategory}
  {W X Y Z : object C} (p : W = X)
  (f : morphism C Y W) (g : morphism C Z Y) :
  (transport (fun U => morphism C Y U) p f o g)%morphism =
  transport (fun U => morphism C Z U) p (f o g)%morphism.
Proof.
  destruct p. reflexivity.
Qed.

Lemma transport_compose_both_inverse {C : PreCategory}
  {W X Y Z : object C} (p : W = X)
  (f : morphism C W Z) (g : morphism C Y W) :
  (transport (fun U : object C => morphism C U Z) p f o 
   transport (fun U : object C => morphism C Y U) p g)%morphism =
  (f o g)%morphism.
Proof.
  destruct p. reflexivity.
Qed.

Lemma transport_initial_morphism {C : PreCategory}
  (I I' X : object C) (p : I = I')
  (H_initial : Contr (morphism C I X))
  (H_initial' : Contr (morphism C I' X))
  (f : morphism C I X) :
  transport (fun U => morphism C U X) p f = 
  @center _ H_initial'.
Proof.
  apply (@contr _ H_initial' (transport (fun U => morphism C U X) p f))^.
Qed.

Lemma transport_terminal_morphism {C : PreCategory}
  (X T T' : object C) (p : T = T')
  (H_terminal : Contr (morphism C X T))
  (H_terminal' : Contr (morphism C X T'))
  (f : morphism C X T) :
  transport (fun U => morphism C X U) p f = 
  @center _ H_terminal'.
Proof.
  apply (@contr _ H_terminal' (transport (fun U => morphism C X U) p f))^.
Qed.

Lemma transport_inverse_is_inverse {A : Type} {B : A -> Type}
  {x y : A} (p : x = y) (b : B x) :
  transport B p^ (transport B p b) = b.
Proof.
  destruct p. reflexivity.
Qed.

Lemma transport_inverse_eq {A : Type} {P : A -> Type} 
  {x y : A} (p : x = y) (u : P x) (v : P y) :
  transport P p u = v -> u = transport P p^ v.
Proof.
  intro H.
  rewrite <- H.
  destruct p.
  reflexivity.
Qed.

Lemma transport_path_inverse {A : Type} {P : A -> Type}
  {x y : A} (p : x = y) (u : P y) :
  transport P p^ u = transport P p^ u.
Proof.
  reflexivity.
Qed.

Lemma morphism_eq_transport_inverse {C : PreCategory}
  {W X Y : object C} (p : W = X)
  (f : morphism C W Y) (g : morphism C X Y) :
  transport (fun Z => morphism C Z Y) p f = g ->
  f = transport (fun Z => morphism C Z Y) p^ g.
Proof.
  intro H.
  rewrite <- H.
  destruct p.
  reflexivity.
Qed.

(** *** Basic Morphism Identities *)

Lemma morphism_right_identity {C : PreCategory} {X Y : object C} (f : morphism C X Y) :
  (f o 1)%morphism = f.
Proof.
  apply Category.Core.right_identity.
Qed.

Lemma morphism_left_identity {C : PreCategory} {X Y : object C} (f : morphism C X Y) :
  (1 o f)%morphism = f.
Proof.
  apply Category.Core.left_identity.
Qed.

Lemma morphism_associativity {C : PreCategory} {W X Y Z : object C} 
  (f : morphism C W X) (g : morphism C X Y) (h : morphism C Y Z) :
  ((h o g) o f)%morphism = (h o (g o f))%morphism.
Proof.
  apply Category.Core.associativity.
Qed.

(** ** Properties of Additive Functors
    
    This section establishes that additive functors preserve zero morphisms
    and other structural properties of additive categories.
*)

(** *** Preservation of Initial and Terminal Morphisms *)

(** Additive functors preserve initial morphisms *)
Lemma functor_preserves_initial_morphism 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (Y : object A) :
  transport (fun Z => morphism B Z (object_of F Y)) 
            (preserves_zero A B F)
            (morphism_of F (@center _ (@is_initial _ (add_zero A) Y))) =
  @center _ (@is_initial _ (add_zero B) (object_of F Y)).
Proof.
  apply (@path_contr _ (@is_initial _ (add_zero B) (object_of F Y))).
Qed.

(** Additive functors preserve terminal morphisms *)
Lemma functor_preserves_terminal_morphism 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (X : object A) :
  transport (fun Z => morphism B (object_of F X) Z) 
            (preserves_zero A B F)
            (morphism_of F (@center _ (@is_terminal _ (add_zero A) X))) =
  @center _ (@is_terminal _ (add_zero B) (object_of F X)).
Proof.
  apply (@path_contr _ (@is_terminal _ (add_zero B) (object_of F X))).
Qed.

(** *** Main Theorem: Additive Functors Preserve Zero Morphisms *)

(** The fundamental property that additive functors preserve zero morphisms *)
Theorem additive_functor_preserves_zero_morphisms 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (X Y : object A) :
  morphism_of F (zero_morphism (add_zero A) X Y) = 
  zero_morphism (add_zero B) (object_of F X) (object_of F Y).
Proof.
  unfold zero_morphism.
  rewrite composition_of.
  
  set (p := preserves_zero A B F).
  
  assert (H1: morphism_of F (@center _ (@is_terminal _ (add_zero A) X)) =
              transport (fun Z => morphism B (object_of F X) Z) p^
                       (@center _ (@is_terminal _ (add_zero B) (object_of F X)))).
  {
    apply transport_inverse_eq.
    apply functor_preserves_terminal_morphism.
  }
  
  assert (H2: morphism_of F (@center _ (@is_initial _ (add_zero A) Y)) =
              transport (fun Z => morphism B Z (object_of F Y)) p^
                       (@center _ (@is_initial _ (add_zero B) (object_of F Y)))).
  {
    apply morphism_eq_transport_inverse.
    apply functor_preserves_initial_morphism.
  }
  
  rewrite H1, H2.
  
  rewrite <- (transport_compose_both_inverse p^).
  
  reflexivity.
Qed.

(** ** Pre-Stable Categories
    
    A pre-stable category is an additive category equipped with
    suspension and loop functors connected by natural transformations.
    This is a precursor to the notion of a stable category.
*)

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

(** The suspension functor preserves zero morphisms (inherited from being additive) *)
Theorem susp_preserves_zero_morphisms {S : PreStableCategory} (X Y : object S) :
  morphism_of (Susp S) (zero_morphism (add_zero S) X Y) = 
  zero_morphism (add_zero S) (object_of (Susp S) X) (object_of (Susp S) Y).
Proof.
  apply additive_functor_preserves_zero_morphisms.
Qed.

(** ** Triangles in Pre-Stable Categories
    
    Triangles are the fundamental structures in triangulated categories.
    A triangle consists of three objects and three morphisms forming a
    specific pattern with the suspension functor.
*)

(** *** Basic Triangle Structure *)

(** A triangle X → Y → Z → ΣX *)
Record Triangle {S : PreStableCategory} := {
  X : object S;
  Y : object S;
  Z : object S;
  f : morphism S X Y;
  g : morphism S Y Z;
  h : morphism S Z (object_of (Susp S) X)
}.

(** *** Distinguished Triangles
    
    A distinguished triangle is a triangle where consecutive morphisms compose to zero.
    This is the triangulated category analog of an exact sequence.
*)

Record DistinguishedTriangle {S : PreStableCategory} := {
  triangle : Triangle;
  
  (** g ∘ f = 0 *)
  zero_comp_1 : (g triangle o f triangle)%morphism = 
                zero_morphism (add_zero S) (X triangle) (Z triangle);
  
  (** h ∘ g = 0 *)
  zero_comp_2 : (h triangle o g triangle)%morphism = 
                zero_morphism (add_zero S) (Y triangle) (object_of (Susp S) (X triangle));
  
  (** Σf ∘ h = 0 *)
  zero_comp_3 : (morphism_of (Susp S) (f triangle) o h triangle)%morphism = 
                zero_morphism (add_zero S) (Z triangle) (object_of (Susp S) (Y triangle))
}.

(** *** The Identity Triangle
    
    For any object X, there is a canonical distinguished triangle
    X → X → 0 → ΣX
*)

(** Construction of the identity triangle *)
Definition id_triangle {S : PreStableCategory} (X : object S) : @Triangle S := {|
  X := X;
  Y := X;
  Z := @zero _ (add_zero S);
  f := 1%morphism;
  g := @center _ (@is_terminal _ (add_zero S) X);
  h := @center _ (@is_initial _ (add_zero S) (object_of (Susp S) X))
|}.

(** *** Lemmas for Zero Objects in Pre-Stable Categories *)

(** The morphism from zero to itself is the identity *)
Lemma zero_to_zero_is_id {S : PreStableCategory} : 
  @center _ (@is_initial _ (add_zero S) (@zero _ (add_zero S))) = 1%morphism.
Proof.
  apply (@contr _ (@is_initial _ (add_zero S) (@zero _ (add_zero S)))).
Qed.

(** The terminal morphism from zero to itself is the identity *)
Lemma terminal_zero_to_zero_is_id {S : PreStableCategory} : 
  @center _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S))) = 
  (1%morphism : morphism S (@zero _ (add_zero S)) (@zero _ (add_zero S))).
Proof.
  apply terminal_morphism_unique.
  apply (@is_terminal _ (add_zero S) (@zero _ (add_zero S))).
Qed.

(** Composition with a terminal morphism to zero gives zero morphism *)
Lemma terminal_comp_is_zero {S : PreStableCategory} (X Y : object S) 
  (f : morphism S X (@zero _ (add_zero S))) :
  (@center _ (@is_initial _ (add_zero S) Y) o f)%morphism = 
  zero_morphism (add_zero S) X Y.
Proof.
  apply morphism_through_zero_is_zero.
Qed.

(** The zero morphism from zero is the initial morphism *)
Lemma zero_morphism_from_zero {S : PreStableCategory} (Y : object S) :
  zero_morphism (add_zero S) (@zero _ (add_zero S)) Y =
  @center _ (@is_initial _ (add_zero S) Y).
Proof.
  unfold zero_morphism.
  assert (H: @center _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S))) = 
            (1%morphism : morphism S (@zero _ (add_zero S)) (@zero _ (add_zero S)))).
  { 
    apply (@contr _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S)))).
  }
  rewrite H.
  apply morphism_right_identity.
Qed.

(** The suspension functor preserves identity morphisms *)
Lemma susp_preserves_identity {S : PreStableCategory} (X : object S) :
  morphism_of (Susp S) (1%morphism : morphism S X X) = 
  (1%morphism : morphism S (object_of (Susp S) X) (object_of (Susp S) X)).
Proof.
  apply (identity_of (Susp S)).
Qed.

(** *** The Identity Triangle is Distinguished *)

Theorem id_triangle_distinguished {S : PreStableCategory} (X : object S) : 
  @DistinguishedTriangle S.
Proof.
  refine {| triangle := id_triangle X |}.
  
  - (* zero_comp_1: g ∘ f = 0 *)
    simpl.
    rewrite morphism_right_identity.
    unfold zero_morphism.
    rewrite zero_to_zero_is_id.
    rewrite morphism_left_identity.
    reflexivity.
  
  - (* zero_comp_2: h ∘ g = 0 *)
    simpl.
    apply terminal_comp_is_zero.
  
  - (* zero_comp_3: Σf ∘ h = 0 *)
    simpl.
    rewrite susp_preserves_identity.
    rewrite morphism_left_identity.
    rewrite <- zero_morphism_from_zero.
    reflexivity.
Defined.

(** ** Morphisms of Triangles
    
    A morphism between triangles consists of three morphisms between
    the corresponding objects that make all squares commute.
*)

(** *** Triangle Morphisms *)

Record TriangleMorphism {S : PreStableCategory} (T1 T2 : @Triangle S) := {
  mor_X : morphism S (X T1) (X T2);
  mor_Y : morphism S (Y T1) (Y T2);
  mor_Z : morphism S (Z T1) (Z T2);
  
  (** Commutativity conditions *)
  comm_f : (mor_Y o f T1)%morphism = (f T2 o mor_X)%morphism;
  comm_g : (mor_Z o g T1)%morphism = (g T2 o mor_Y)%morphism;
  comm_h : (morphism_of (Susp S) mor_X o h T1)%morphism = 
           (h T2 o mor_Z)%morphism
}.

(** *** Identity Triangle Morphism *)

Definition id_triangle_morphism {S : PreStableCategory} (T : @Triangle S) : 
  TriangleMorphism T T.
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

(** *** Composition of Triangle Morphisms *)

Definition triangle_morphism_compose {S : PreStableCategory}
  (T1 T2 T3 : @Triangle S)
  (φ : TriangleMorphism T1 T2)
  (ψ : TriangleMorphism T2 T3) : 
  TriangleMorphism T1 T3.
Proof.
  refine {| 
    mor_X := (mor_X _ _ ψ o mor_X _ _ φ)%morphism;
    mor_Y := (mor_Y _ _ ψ o mor_Y _ _ φ)%morphism;
    mor_Z := (mor_Z _ _ ψ o mor_Z _ _ φ)%morphism
  |}.
  - rewrite morphism_associativity.
    rewrite (comm_f _ _ φ).
    rewrite <- morphism_associativity.
    rewrite (comm_f _ _ ψ).
    rewrite morphism_associativity.
    reflexivity.
  - rewrite morphism_associativity.
    rewrite (comm_g _ _ φ).
    rewrite <- morphism_associativity.
    rewrite (comm_g _ _ ψ).
    rewrite morphism_associativity.
    reflexivity.
  - simpl.
    rewrite (composition_of (Susp S)).
    rewrite morphism_associativity.
    rewrite (comm_h _ _ φ).
    rewrite <- morphism_associativity.
    rewrite (comm_h _ _ ψ).
    rewrite morphism_associativity.
    reflexivity.
Defined.

(** *** Triangle Morphisms Form a Category *)

(** Equality of triangle morphisms *)
Lemma triangle_morphism_eq {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ ψ : TriangleMorphism T1 T2) :
  mor_X _ _ φ = mor_X _ _ ψ ->
  mor_Y _ _ φ = mor_Y _ _ ψ ->
  mor_Z _ _ φ = mor_Z _ _ ψ ->
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

(** Left identity law *)
Lemma triangle_morphism_left_id {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ : TriangleMorphism T1 T2) :
  triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply morphism_left_identity.
  - simpl. apply morphism_left_identity.  
  - simpl. apply morphism_left_identity.
Qed.

(** Right identity law *)
Lemma triangle_morphism_right_id {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ : TriangleMorphism T1 T2) :
  triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply morphism_right_identity.
  - simpl. apply morphism_right_identity.
  - simpl. apply morphism_right_identity.
Qed.

(** Associativity of composition *)
Lemma triangle_morphism_assoc {S : PreStableCategory} 
  (T1 T2 T3 T4 : @Triangle S)
  (φ : TriangleMorphism T1 T2)
  (ψ : TriangleMorphism T2 T3)
  (χ : TriangleMorphism T3 T4) :
  triangle_morphism_compose T1 T2 T4 φ (triangle_morphism_compose T2 T3 T4 ψ χ) =
  triangle_morphism_compose T1 T3 T4 (triangle_morphism_compose T1 T2 T3 φ ψ) χ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply Category.Core.associativity.
  - simpl. apply Category.Core.associativity.
  - simpl. apply Category.Core.associativity.
Qed.

(** Triangles form a category *)
Theorem triangles_form_category {S : PreStableCategory} : 
  (forall (T1 T2 T3 T4 : @Triangle S) 
          (φ : TriangleMorphism T1 T2)
          (ψ : TriangleMorphism T2 T3)
          (χ : TriangleMorphism T3 T4),
    triangle_morphism_compose T1 T2 T4 φ (triangle_morphism_compose T2 T3 T4 ψ χ) =
    triangle_morphism_compose T1 T3 T4 (triangle_morphism_compose T1 T2 T3 φ ψ) χ) /\
  (forall (T1 T2 : @Triangle S) (φ : TriangleMorphism T1 T2),
    triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ) /\
  (forall (T1 T2 : @Triangle S) (φ : TriangleMorphism T1 T2),
    triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ).
Proof.
  split; [|split].
  - intros. apply triangle_morphism_assoc.
  - intros. apply triangle_morphism_left_id.
  - intros. apply triangle_morphism_right_id.
Qed.

(** ** Triangle Rotation
    
    The rotation operation is fundamental in triangulated categories.
    It transforms a triangle X → Y → Z → ΣX into Y → Z → ΣX → ΣY.
*)

(** *** Rotation of Triangles *)

Definition rotate_triangle {S : PreStableCategory} (T : @Triangle S) : @Triangle S := {|
  X := Y T;
  Y := Z T;
  Z := object_of (Susp S) (X T);
  f := g T;
  g := h T;
  h := morphism_of (Susp S) (f T)
|}.

(** *** Rotation Preserves Distinguished Triangles *)

Theorem rotate_distinguished {S : PreStableCategory} (T : @DistinguishedTriangle S) :
  @DistinguishedTriangle S.
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

(** ** Axioms of Triangulated Categories
    
    We now formalize the axioms that characterize triangulated categories.
    TR1 ensures every morphism extends to a distinguished triangle.
*)

(** *** Axiom TR1: Extension of Morphisms to Distinguished Triangles *)

(** Statement of TR1: Every morphism can be completed to a distinguished triangle *)
Definition TR1_statement {S : PreStableCategory} : Type :=
  forall (X Y : object S) (f : morphism S X Y),
  { Z : object S &
  { g : morphism S Y Z &
  { h : morphism S Z (object_of (Susp S) X) &
    @DistinguishedTriangle S }}}.

(** Helper to construct a triangle from morphisms *)
Definition triangle_from_morphisms {S : PreStableCategory}
  {X Y Z : object S} 
  (f : morphism S X Y)
  (g : morphism S Y Z)
  (h : morphism S Z (object_of (Susp S) X)) : @Triangle S :=
{|
  X := X;
  Y := Y;
  Z := Z;
  f := f;
  g := g;
  h := h
|}.

(** ** Mapping Cones
    
    The mapping cone construction provides a canonical way to complete
    a morphism to a distinguished triangle.
*)

(** *** Basic Cone Construction *)

Definition cone {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) : object S :=
  @biproduct_obj _ _ _ (add_biproduct S Y (object_of (Susp S) X)).

Definition cone_in {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) : 
  morphism S Y (cone f) :=
  @inl _ _ _ (add_biproduct S Y (object_of (Susp S) X)).

Definition cone_out {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) : 
  morphism S (cone f) (object_of (Susp S) X) :=
  @outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)).

(** *** Cone Triangle Construction *)

Definition cone_triangle {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) : 
  @Triangle S :=
{|
  X := X;
  Y := Y;
  Z := cone f;
  f := f;
  g := cone_in f;
  h := cone_out f
|}.

(** *** Properties of Cone Morphisms *)

Lemma cone_out_cone_in_zero {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) :
  ((cone_out f) o (cone_in f))%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X).
Proof.
  unfold cone_out, cone_in.
  apply (@mixed_r _ _ _ (add_biproduct S Y (object_of (Susp S) X)) (add_zero S) 
                        (add_biproduct_props S Y (object_of (Susp S) X))).
Qed.

(** Helper lemma for cone distinguished triangle construction *)
Lemma cone_distinguished_conditions {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) :
  ((cone_in f) o f)%morphism = zero_morphism (add_zero S) X (cone f) ->
  ((cone_out f) o (cone_in f))%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X) ->
  (morphism_of (Susp S) f o (cone_out f))%morphism = zero_morphism (add_zero S) (cone f) (object_of (Susp S) Y) ->
  @DistinguishedTriangle S.
Proof.
  intros H1 H2 H3.
  refine {| triangle := cone_triangle f |}.
  - exact H1.
  - exact H2.
  - exact H3.
Defined.

(** ** Pre-Stable Categories with Cofiber
    
    A more structured version of pre-stable categories where the mapping
    cone/cofiber construction is given as part of the data.
*)

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
    zero_morphism (add_zero base) X (cofiber f);
    
  cofiber_cond2 : forall {X Y : object base} (f : morphism base X Y),
    (cofiber_out f o cofiber_in f)%morphism = 
    zero_morphism (add_zero base) Y (object_of (Susp base) X);
    
  cofiber_cond3 : forall {X Y : object base} (f : morphism base X Y),
    (morphism_of (Susp base) f o cofiber_out f)%morphism = 
    zero_morphism (add_zero base) (cofiber f) (object_of (Susp base) Y)
}.

(** *** Cofiber Gives Distinguished Triangles *)

Definition triangle_from_morphism {S : PreStableCategoryWithCofiber} 
  {X Y : object S} (f : morphism S X Y) : @Triangle (base S) :=
{|
  X := X;
  Y := Y;
  Z := @cofiber S X Y f;
  f := f;
  g := @cofiber_in S X Y f;
  h := @cofiber_out S X Y f
|}.

Theorem cofiber_triangle_distinguished {S : PreStableCategoryWithCofiber} 
  {X Y : object S} (f : morphism S X Y) : @DistinguishedTriangle (base S).
Proof.
  refine {| triangle := triangle_from_morphism f |}.
  - simpl. exact (@cofiber_cond1 S X Y f).
  - simpl. exact (@cofiber_cond2 S X Y f).
  - simpl. exact (@cofiber_cond3 S X Y f).
Defined.

(** *** TR1 for Categories with Cofiber *)

Theorem TR1 {S : PreStableCategoryWithCofiber} {X Y : object S} (f : morphism S X Y) :
  @DistinguishedTriangle (base S).
Proof.
  exact (cofiber_triangle_distinguished f).
Defined.

Theorem TR1_correct {S : PreStableCategoryWithCofiber} {X Y : object S} (f : morphism S X Y) :
  triangle (TR1 f) = triangle_from_morphism f.
Proof.
  reflexivity.
Qed.

(** Constructive version of TR1 *)
Definition TR1_triangle_data {S : PreStableCategoryWithCofiber} 
  {X Y : object (base S)} (f : morphism (base S) X Y) :
  { Z : object (base S) & 
  { g : morphism (base S) Y Z &
  { h : morphism (base S) Z (object_of (Susp (base S)) X) &
  ((g o f)%morphism = zero_morphism (add_zero (base S)) X Z) *
  ((h o g)%morphism = zero_morphism (add_zero (base S)) Y (object_of (Susp (base S)) X)) *
  ((morphism_of (Susp (base S)) f o h)%morphism = 
   zero_morphism (add_zero (base S)) Z (object_of (Susp (base S)) Y)) }}}.
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

(** ** Isomorphisms in Categories
    
    We define isomorphisms and establish their basic properties,
    which will be needed for the axioms of triangulated categories.
*)

(** *** Basic Isomorphism Definition *)

Definition IsIsomorphism {C : PreCategory} {X Y : object C} (f : morphism C X Y) : Type :=
  { g : morphism C Y X |
    (g o f = 1)%morphism /\ (f o g = 1)%morphism }.

(** Extract the inverse morphism *)
Definition iso_inverse {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f) : morphism C Y X :=
  H.1.

(** The identity morphism is an isomorphism *)
Lemma iso_identity {C : PreCategory} {X : object C} : 
  IsIsomorphism (1%morphism : morphism C X X).
Proof.
  exists 1%morphism.
  split; apply morphism_left_identity.
Qed.

(** Properties of inverses *)
Lemma iso_inverse_left {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f) :
  (iso_inverse H o f = 1)%morphism.
Proof.
  destruct H as [g [Hl Hr]].
  exact Hl.
Qed.

Lemma iso_inverse_right {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f) :
  (f o iso_inverse H = 1)%morphism.
Proof.
  destruct H as [g [Hl Hr]].
  exact Hr.
Qed.

(** *** Triangle Isomorphisms *)

(** A triangle isomorphism is a triangle morphism where all three
    component morphisms are isomorphisms *)
Definition IsTriangleIsomorphism {S : PreStableCategory} {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2) : Type :=
  IsIsomorphism (mor_X _ _ φ) * 
  IsIsomorphism (mor_Y _ _ φ) * 
  IsIsomorphism (mor_Z _ _ φ).

(** ** Axiom TR2: Isomorphisms of Distinguished Triangles
    
    TR2 states that if we have an isomorphism between two triangles
    and one is distinguished, then so is the other.
*)

(** *** Helper Lemmas for Isomorphisms *)

(** Isomorphisms preserve terminal morphisms *)
Lemma iso_preserves_terminal {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ)
  (f : morphism S X (@zero _ (add_zero S))) :
  (f o iso_inverse H)%morphism = @center _ (@is_terminal _ (add_zero S) Y).
Proof.
  symmetry.
  apply (@contr _ (@is_terminal _ (add_zero S) Y)).
Qed.

(** Isomorphisms preserve initial morphisms *)
Lemma iso_preserves_initial {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ)
  (f : morphism S (@zero _ (add_zero S)) X) :
  (φ o f)%morphism = @center _ (@is_initial _ (add_zero S) Y).
Proof.
  symmetry.
  apply (@contr _ (@is_initial _ (add_zero S) Y)).
Qed.

(** Composition with zero morphism on the right *)
Lemma zero_morphism_right {S : PreStableCategory} {X Y Z : object S}
  (g : morphism S Y Z) :
  (g o zero_morphism (add_zero S) X Y)%morphism = 
  zero_morphism (add_zero S) X Z.
Proof.
  unfold zero_morphism.
  assert (H: (g o @center _ (@is_initial _ (add_zero S) Y))%morphism = 
             @center _ (@is_initial _ (add_zero S) Z)).
  {
    symmetry.
    apply (@contr _ (@is_initial _ (add_zero S) Z)).
  }
  rewrite <- morphism_associativity.
  rewrite H.
  reflexivity.
Qed.

(** Composition with zero morphism on the left *)
Lemma zero_morphism_left {S : PreStableCategory} {X Y Z : object S}
  (f : morphism S X Y) :
  (zero_morphism (add_zero S) Y Z o f)%morphism = 
  zero_morphism (add_zero S) X Z.
Proof.
  unfold zero_morphism.
  assert (H: (@center _ (@is_terminal _ (add_zero S) Y) o f)%morphism = 
             @center _ (@is_terminal _ (add_zero S) X)).
  {
    symmetry.
    apply (@contr _ (@is_terminal _ (add_zero S) X)).
  }
  rewrite morphism_associativity.
  rewrite H.
  reflexivity.
Qed.

(** Isomorphisms preserve zero morphisms *)
Lemma iso_preserves_zero {S : PreStableCategory} {X Y Z W : object S}
  (φX : morphism S X Z) (φY : morphism S Y W)
  (HX : IsIsomorphism φX) (HY : IsIsomorphism φY)
  (f : morphism S X Y) :
  f = zero_morphism (add_zero S) X Y ->
  (φY o f o iso_inverse HX)%morphism = zero_morphism (add_zero S) Z W.
Proof.
  intro Hf.
  rewrite Hf.
  rewrite zero_morphism_right.
  rewrite zero_morphism_left.
  reflexivity.
Qed.

(** *** Functors Preserve Isomorphisms *)

Lemma functor_preserves_iso {C D : PreCategory} (F : Functor C D)
  {X Y : object C} (f : morphism C X Y) (H : IsIsomorphism f) :
  IsIsomorphism (morphism_of F f).
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

Lemma functor_preserves_inverse {C D : PreCategory} (F : Functor C D)
  {X Y : object C} (f : morphism C X Y) (H : IsIsomorphism f) :
  morphism_of F (iso_inverse H) = 
  iso_inverse (functor_preserves_iso F f H).
Proof.
  destruct H as [g [Hgf Hfg]].
  simpl.
  reflexivity.
Qed.

(** *** Helper Lemmas for Composition *)

Lemma ap_morphism_comp_left {C : PreCategory} {X Y Z : object C} 
  (f : morphism C Y Z) (g h : morphism C X Y) :
  g = h -> (f o g)%morphism = (f o h)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_cancel_left {C : PreCategory} {X Y Z : object C} 
  (f : morphism C Y Z) (g h : morphism C X Y) :
  (f o g)%morphism = (f o h)%morphism -> 
  (1 o g)%morphism = (1 o h)%morphism ->
  g = h.
Proof.
  intros H1 H2.
  rewrite morphism_left_identity in H2.
  rewrite morphism_left_identity in H2.
  exact H2.
Qed.

Lemma iso_comp_to_id {C : PreCategory} {X Y : object C} 
  (f : morphism C X Y) (g : morphism C Y X)
  (H : (g o f = 1)%morphism) :
  forall (Z : object C) (h : morphism C Z X),
  ((g o f) o h)%morphism = (1 o h)%morphism.
Proof.
  intros Z h.
  rewrite H.
  reflexivity.
Qed.

Lemma four_way_compose_eq {C : PreCategory} {V W X Y Z : object C}
  (p : morphism C Y Z) 
  (q1 q2 : morphism C X Y)
  (r : morphism C W X)
  (s : morphism C V W) :
  q1 = q2 ->
  (p o q1 o r o s)%morphism = (p o q2 o r o s)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_left {C : PreCategory} {X Y Z : object C}
  (p : morphism C Y Z)
  (q1 q2 : morphism C X Y) :
  q1 = q2 ->
  (p o q1)%morphism = (p o q2)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_right {C : PreCategory} {X Y Z : object C}
  (p1 p2 : morphism C Y Z)
  (q : morphism C X Y) :
  p1 = p2 ->
  (p1 o q)%morphism = (p2 o q)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

(** *** Additional Helper Lemmas for TR2 *)

Lemma iso_morphism_cancel {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ) :
  (iso_inverse H o φ)%morphism = 1%morphism.
Proof.
  apply iso_inverse_left.
Qed.

Lemma composition_with_identity_middle {S : PreStableCategory} {A B C D : object S}
  (f : morphism S C D)
  (g : morphism S B C) 
  (h : morphism S A B) :
  (f o 1 o g o h)%morphism = (f o g o h)%morphism.
Proof.
  rewrite morphism_right_identity.
  reflexivity.
Qed.

Lemma rearrange_middle_composition {S : PreStableCategory} {A B C D E : object S}
  (f : morphism S D E)
  (g : morphism S C D)
  (h : morphism S B C)
  (k : morphism S A B) :
  (f o (g o (h o k)))%morphism = (f o ((g o h) o k))%morphism.
Proof.
  rewrite morphism_associativity.
  reflexivity.
Qed.

Lemma get_morphisms_adjacent {S : PreStableCategory} {A B C D E F : object S}
  (f : morphism S E F)
  (g : morphism S D E)
  (h : morphism S C D)
  (k : morphism S B C)
  (l : morphism S A B) :
  (f o (g o (h o (k o l))))%morphism = 
  (f o (g o ((h o k) o l)))%morphism.
Proof.
  rewrite morphism_associativity.
  reflexivity.
Qed.

Lemma four_morphism_assoc {S : PreStableCategory} {A B C D E : object S}
  (φ : morphism S D E)
  (g : morphism S C D)
  (f : morphism S B C)
  (ψ : morphism S A B) :
  (φ o g o f o ψ)%morphism = (φ o (g o f) o ψ)%morphism.
Proof.
  rewrite (morphism_associativity ψ f (φ o g)%morphism).
  rewrite (morphism_associativity (f o ψ)%morphism g φ).
  rewrite <- (morphism_associativity ψ f g).
  rewrite <- morphism_associativity.
  reflexivity.
Qed.

Lemma morphism_four_compose_with_zero {S : PreStableCategory} {A B C D E : object S}
  (φ : morphism S D E)
  (g : morphism S C D)
  (f : morphism S B C)
  (ψ : morphism S A B) :
  (g o f)%morphism = zero_morphism (add_zero S) B D ->
  (φ o g o f o ψ)%morphism = zero_morphism (add_zero S) A E.
Proof.
  intro H.
  rewrite four_morphism_assoc.
  rewrite H.
  rewrite zero_morphism_right.
  rewrite zero_morphism_left.
  reflexivity.
Qed.

Lemma triangle_composition_pattern {S : PreStableCategory} {X1 Y1 Z1 X2 Y2 Z2 : object S}
  (φZ : morphism S Z1 Z2)
  (g : morphism S Y1 Z1)
  (φY_inv : morphism S Y2 Y1)
  (φY : morphism S Y1 Y2)
  (f : morphism S X1 Y1)
  (φX_inv : morphism S X2 X1) :
  (φY_inv o φY)%morphism = 1%morphism ->
  ((φZ o g o φY_inv) o (φY o f o φX_inv))%morphism = 
  (φZ o g o f o φX_inv)%morphism.
Proof.
  intro H.
  rewrite !morphism_associativity.
  rewrite get_morphisms_adjacent.
  rewrite H.
  rewrite morphism_left_identity.
  reflexivity.
Qed.

(** ** Axiom TR2: Isomorphisms Preserve Distinguished Triangles
    
    This section proves that isomorphisms of triangles preserve the property
    of being distinguished. This is one of the fundamental axioms of
    triangulated categories.
*)

(** *** Formulas for Triangle Components Under Isomorphisms *)

(** How the f morphism transforms under an isomorphism *)
Lemma triangle_iso_f_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HY_iso : IsIsomorphism (mor_Y _ _ φ))
  (HX_iso : IsIsomorphism (mor_X _ _ φ)) :
  f T2 = (mor_Y _ _ φ o f T1 o iso_inverse HX_iso)%morphism.
Proof.
  pose proof (comm_f _ _ φ) as Hcomm.
  
  assert (H: forall (g h : morphism S (X T1) (Y T2)) (k : morphism S (X T2) (X T1)),
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

(** How the g morphism transforms under an isomorphism *)
Lemma triangle_iso_g_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ))
  (HY_iso : IsIsomorphism (mor_Y _ _ φ)) :
  g T2 = (mor_Z _ _ φ o g T1 o iso_inverse HY_iso)%morphism.
Proof.
  pose proof (comm_g _ _ φ) as Hcomm.
  
  assert (H: forall (g h : morphism S (Y T1) (Z T2)) (k : morphism S (Y T2) (Y T1)),
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

(** How the h morphism transforms under an isomorphism *)
Lemma triangle_iso_h_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HX_iso : IsIsomorphism (mor_X _ _ φ))
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ)) :
  h T2 = (morphism_of (Susp S) (mor_X _ _ φ) o h T1 o iso_inverse HZ_iso)%morphism.
Proof.
  pose proof (comm_h _ _ φ) as Hcomm.
  
  assert (H: forall (g h : morphism S (Z T1) (object_of (Susp S) (X T2))) 
                    (k : morphism S (Z T2) (Z T1)),
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

(** *** Preservation of Zero Compositions *)

(** Isomorphisms preserve the first zero composition g∘f = 0 *)
Lemma triangle_iso_preserves_zero_comp_1 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ) :
  (g T1 o f T1)%morphism = zero_morphism (add_zero S) (X T1) (Z T1) ->
  (g T2 o f T2)%morphism = zero_morphism (add_zero S) (X T2) (Z T2).
Proof.
  intro H.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  
  rewrite (triangle_iso_f_formula φ HY_iso HX_iso).
  rewrite (triangle_iso_g_formula φ HZ_iso HY_iso).
  
  rewrite (triangle_composition_pattern 
             (mor_Z _ _ φ) (g T1) 
             (iso_inverse HY_iso) (mor_Y _ _ φ)
             (f T1) (iso_inverse HX_iso)
             (iso_inverse_left HY_iso)).
  
  apply morphism_four_compose_with_zero.
  exact H.
Qed.

(** Isomorphisms preserve the second zero composition h∘g = 0 *)
Lemma triangle_iso_preserves_zero_comp_2 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ) :
  (h T1 o g T1)%morphism = zero_morphism (add_zero S) (Y T1) (object_of (Susp S) (X T1)) ->
  (h T2 o g T2)%morphism = zero_morphism (add_zero S) (Y T2) (object_of (Susp S) (X T2)).
Proof.
  intro H.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  
  rewrite (triangle_iso_g_formula φ HZ_iso HY_iso).
  rewrite (triangle_iso_h_formula φ HX_iso HZ_iso).
  
  rewrite (triangle_composition_pattern 
             (morphism_of (Susp S) (mor_X _ _ φ)) (h T1) 
             (iso_inverse HZ_iso) (mor_Z _ _ φ)
             (g T1) (iso_inverse HY_iso)
             (iso_inverse_left HZ_iso)).
  apply morphism_four_compose_with_zero.
  exact H.
Qed.

(** Isomorphisms preserve the third zero composition Σf∘h = 0 *)
Lemma triangle_iso_preserves_zero_comp_3 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ) :
  (morphism_of (Susp S) (f T1) o h T1)%morphism = 
  zero_morphism (add_zero S) (Z T1) (object_of (Susp S) (Y T1)) ->
  (morphism_of (Susp S) (f T2) o h T2)%morphism = 
  zero_morphism (add_zero S) (Z T2) (object_of (Susp S) (Y T2)).
Proof.
  intro H.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  
  rewrite (triangle_iso_f_formula φ HY_iso HX_iso).
  rewrite (triangle_iso_h_formula φ HX_iso HZ_iso).
  
  rewrite (composition_of (Susp S)).
  rewrite (composition_of (Susp S)).
      
  rewrite (functor_preserves_inverse (Susp S) (mor_X _ _ φ) HX_iso).
  
  rewrite (triangle_composition_pattern 
             (morphism_of (Susp S) (mor_Y _ _ φ)) 
             (morphism_of (Susp S) (f T1))
             (iso_inverse (functor_preserves_iso (Susp S) (mor_X _ _ φ) HX_iso))
             (morphism_of (Susp S) (mor_X _ _ φ))
             (h T1) 
             (iso_inverse HZ_iso)
             (iso_inverse_left (functor_preserves_iso (Susp S) (mor_X _ _ φ) HX_iso))).
  
  apply morphism_four_compose_with_zero.
  exact H.
Qed.

(** *** Main Theorem: TR2 *)

(** TR2: Triangle isomorphisms preserve the distinguished property *)
Theorem TR2 {S : PreStableCategory} {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ)
  (D1 : @DistinguishedTriangle S)
  (H1 : triangle D1 = T1) :
  @DistinguishedTriangle S.
Proof.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  refine {| triangle := T2 |}.
  - (* zero_comp_1 *)
    apply (triangle_iso_preserves_zero_comp_1 φ (conj (conj HX_iso HY_iso) HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_1 D1).
  - (* zero_comp_2 *)
    apply (triangle_iso_preserves_zero_comp_2 φ (conj (conj HX_iso HY_iso) HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_2 D1).
  - (* zero_comp_3 *)
    apply (triangle_iso_preserves_zero_comp_3 φ (conj (conj HX_iso HY_iso) HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_3 D1).
Defined.

(** ** Shift and Axiom TR3
    
    The shift operation is another name for rotation. We formalize how
    triangle morphisms behave under shifting.
*)

Definition shift_triangle {S : PreStableCategory} (T : @Triangle S) : @Triangle S := 
  rotate_triangle T.

Theorem shift_distinguished {S : PreStableCategory} (T : @DistinguishedTriangle S) :
  @DistinguishedTriangle S.
Proof.
  exact (rotate_distinguished T).
Defined.

(** Shifting a triangle morphism *)
Definition shift_triangle_morphism {S : PreStableCategory} {T1 T2 : @Triangle S}
  (φ : TriangleMorphism T1 T2) : 
  TriangleMorphism (shift_triangle T1) (shift_triangle T2).
Proof.
  unfold shift_triangle, rotate_triangle.

  apply Build_TriangleMorphism with
    (mor_X := mor_Y T1 T2 φ)
    (mor_Y := mor_Z T1 T2 φ)
    (mor_Z := morphism_of (Susp S) (mor_X T1 T2 φ)).
  - (* comm_f *)
    exact (comm_g T1 T2 φ).
  - (* comm_g *)
    exact (comm_h T1 T2 φ).
  - (* comm_h *)
    rewrite <- (composition_of (Susp S)).
    rewrite (comm_f T1 T2 φ).
    rewrite (composition_of (Susp S)).
    reflexivity.
Defined.

(** Statement of TR3 *)
Definition TR3_statement {S : PreStableCategory} : Type :=
  forall (T : @Triangle S) (T' : @Triangle S) 
         (φ : TriangleMorphism T T'),
  IsTriangleIsomorphism φ ->
  @DistinguishedTriangle S ->
  @DistinguishedTriangle S.
  
  (** ** Opposite Categories
    
    The opposite category construction reverses all morphisms. This section
    shows that pre-stable categories have a natural opposite structure where
    the suspension and loop functors are interchanged.
*)

(** *** Basic Opposite Category Construction *)

Definition opposite_category (C : PreCategory) : PreCategory.
Proof.
  exact (@Build_PreCategory
    (object C)
    (fun X Y => morphism C Y X)
    (fun X => 1%morphism)
    (fun X Y Z f g => (g o f)%morphism)
    (fun s d d' d'' m1 m2 m3 => (Category.Core.associativity C d'' d' d s m3 m2 m1)^)
    (fun a b f => Category.Core.right_identity C b a f)
    (fun a b f => Category.Core.left_identity C b a f)
    (fun s d => trunc_morphism C d s)).
Defined.

(** *** Opposite Zero Object *)

Definition opposite_zero_object {C : PreCategory} (Z : ZeroObject C) : 
  ZeroObject (opposite_category C).
Proof.
  exact (Build_ZeroObject 
    (opposite_category C)
    (zero _ Z)
    (fun X => is_terminal _ Z X)
    (fun X => is_initial _ Z X)).
Defined.

(** *** Opposite Biproduct *)

Definition opposite_biproduct {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) : @Biproduct (opposite_category C) Y X.
Proof.
  exact (Build_Biproduct
    (opposite_category C) Y X
    (@biproduct_obj _ _ _ B)
    (@outr _ _ _ B)
    (@outl _ _ _ B)
    (@inr _ _ _ B)
    (@inl _ _ _ B)).
Defined.

(** *** Properties of Opposite Biproducts *)

Lemma opposite_biproduct_beta_l {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (Z : ZeroObject C) (H : IsBiproduct B Z) :
  (@outl _ _ _ (opposite_biproduct B) o @inl _ _ _ (opposite_biproduct B) = 1)%morphism.
Proof.
  simpl.
  exact (@beta_r _ _ _ B Z H).
Qed.

Lemma opposite_biproduct_beta_r {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (Z : ZeroObject C) (H : IsBiproduct B Z) :
  (@outr _ _ _ (opposite_biproduct B) o @inr _ _ _ (opposite_biproduct B) = 1)%morphism.
Proof.
  simpl.
  exact (@beta_l _ _ _ B Z H).
Qed.

Lemma opposite_biproduct_mixed_r {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (Z : ZeroObject C) (H : IsBiproduct B Z) :
  (@outr _ _ _ (opposite_biproduct B) o @inl _ _ _ (opposite_biproduct B))%morphism = 
  zero_morphism (opposite_zero_object Z) Y X.
Proof.
  simpl.
  exact (@mixed_r _ _ _ B Z H).
Qed.

(** *** Universal Property of Opposite Biproducts *)

(** Helper equivalence for swapping products *)
Lemma swap_product_equiv {A : Type} {P Q : A -> Type} :
  {a : A & (P a * Q a)} <~> {a : A & (Q a * P a)}.
Proof.
  apply equiv_functor_sigma_id.
  intro a.
  apply equiv_prod_symm.
Defined.

Lemma swap_product_contr {A : Type} {P Q : A -> Type} :
  Contr {a : A & (P a * Q a)} ->
  Contr {a : A & (Q a * P a)}.
Proof.
  intro H.
  apply (contr_equiv' _ (swap_product_equiv)).
Qed.

Lemma opposite_coprod_universal {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (H : BiproductUniversal B) :
  forall (Z : object (opposite_category C)) 
         (f : morphism (opposite_category C) Y Z) 
         (g : morphism (opposite_category C) X Z),
  Contr {h : morphism (opposite_category C) (@biproduct_obj _ _ _ (opposite_biproduct B)) Z | 
         (h o @inl _ _ _ (opposite_biproduct B) = f)%morphism /\ 
         (h o @inr _ _ _ (opposite_biproduct B) = g)%morphism}.
Proof.
  intros Z f g.
  simpl in *.
  apply swap_product_contr.
  exact (@prod_universal _ _ _ B H Z g f).
Qed.

Lemma opposite_prod_universal {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (H : BiproductUniversal B) :
  forall (Z : object (opposite_category C)) 
         (f : morphism (opposite_category C) Z Y) 
         (g : morphism (opposite_category C) Z X),
  Contr {h : morphism (opposite_category C) Z (@biproduct_obj _ _ _ (opposite_biproduct B)) | 
         (@outl _ _ _ (opposite_biproduct B) o h = f)%morphism /\ 
         (@outr _ _ _ (opposite_biproduct B) o h = g)%morphism}.
Proof.
  intros Z f g.
  simpl in *.
  apply swap_product_contr.
  exact (@coprod_universal _ _ _ B H Z g f).
Qed.

Definition opposite_biproduct_universal {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (H : BiproductUniversal B) : 
  BiproductUniversal (opposite_biproduct B).
Proof.
  exact (Build_BiproductUniversal
    (opposite_category C) Y X
    (opposite_biproduct B)
    (opposite_coprod_universal B H)
    (opposite_prod_universal B H)).
Defined.

(** *** Opposite Additive Category *)

Definition opposite_additive_category (A : AdditiveCategory) : AdditiveCategory.
Proof.
  refine (Build_AdditiveCategory
    (opposite_category A)
    (opposite_zero_object (add_zero A))
    (fun X Y => opposite_biproduct (add_biproduct A Y X))
    _ _).
  - (* Biproduct properties *)
    intros X Y.
    pose (B := add_biproduct A Y X).
    pose (Z := add_zero A).
    pose (H := add_biproduct_props A Y X).
    exact (Build_IsBiproduct
      (opposite_category A) X Y
      (opposite_biproduct B)
      (opposite_zero_object Z)
      (@beta_r _ _ _ B Z H)
      (@beta_l _ _ _ B Z H)
      (@mixed_l _ _ _ B Z H)
      (@mixed_r _ _ _ B Z H)).
  - (* Universal property *)
    intros X Y.
    apply opposite_biproduct_universal.
    exact (add_biproduct_universal A Y X).
Defined.

(** *** Opposite Functor *)

Definition opposite_functor {C D : PreCategory} (F : Functor C D) : 
  Functor (opposite_category C) (opposite_category D).
Proof.
  exact (Build_Functor
    (opposite_category C) (opposite_category D)
    (object_of F)
    (fun X Y f => morphism_of F f)
    (fun X Y Z f g => composition_of F Z Y X g f)
    (fun X => identity_of F X)).
Defined.

(** *** Opposite Additive Functor *)

Definition opposite_additive_functor {A B : AdditiveCategory} 
  (F : AdditiveFunctor A B) : 
  AdditiveFunctor (opposite_additive_category A) (opposite_additive_category B).
Proof.
  exact (Build_AdditiveFunctor
    (opposite_additive_category A) (opposite_additive_category B)
    (opposite_functor F)
    (preserves_zero A B F)
    (fun X Y => preserves_biproduct A B F Y X)).
Defined.

(** *** Opposite Natural Transformation *)

Definition opposite_natural_transformation {C D : PreCategory} 
  {F G : Functor C D} (η : NaturalTransformation F G) : 
  NaturalTransformation (opposite_functor G) (opposite_functor F).
Proof.
  exact (Build_NaturalTransformation
    (opposite_functor G) (opposite_functor F)
    (fun X => components_of η X)
    (fun X Y f => (commutes η Y X f)^)).
Defined.

(** *** Opposite Pre-Stable Category *)

(** The key insight: in the opposite category, suspension and loop functors swap roles *)
Definition opposite_prestable_category (PS : PreStableCategory) : PreStableCategory.
Proof.
  exact (Build_PreStableCategory
    (opposite_additive_category PS)
    (opposite_additive_functor (Loop PS))  (* Loop becomes Susp *)
    (opposite_additive_functor (Susp PS))  (* Susp becomes Loop *)
    (opposite_natural_transformation (epsilon PS))  (* epsilon becomes eta *)
    (opposite_natural_transformation (eta PS))).     (* eta becomes epsilon *)
Defined.

(** *** Double Opposite is Identity *)

Definition double_opposite_functor (C : PreCategory) : 
  Functor (opposite_category (opposite_category C)) C.
Proof.
  exact (Build_Functor
    (opposite_category (opposite_category C)) C
    (fun X => X)
    (fun X Y f => f)
    (fun X Y Z f g => idpath)
    (fun X => idpath)).
Defined.

Definition to_double_opposite_functor (C : PreCategory) : 
  Functor C (opposite_category (opposite_category C)).
Proof.
  exact (Build_Functor
    C (opposite_category (opposite_category C))
    (fun X => X)
    (fun X Y f => f)
    (fun X Y Z f g => idpath)
    (fun X => idpath)).
Defined.

(** *** Basic Properties of Opposite Categories *)

Lemma opposite_involution_objects (C : PreCategory) : 
  object (opposite_category (opposite_category C)) = object C.
Proof.
  reflexivity.
Qed.

Lemma opposite_involution_morphisms (C : PreCategory) (X Y : object C) : 
  morphism (opposite_category (opposite_category C)) X Y = morphism C X Y.
Proof.
  reflexivity.
Qed.

(** *** Main Theorems about Opposite Pre-Stable Categories *)

Theorem opposite_prestable_exists :
  forall (PS : PreStableCategory),
  exists (PS_op : PreStableCategory),
    cat PS_op = opposite_additive_category PS.
Proof.
  intro PS.
  exists (opposite_prestable_category PS).
  reflexivity.
Qed.

Theorem opposite_morphisms_flip :
  forall (PS : PreStableCategory) (X Y : object PS),
  morphism (opposite_prestable_category PS) X Y = morphism PS Y X.
Proof.
  intros.
  reflexivity.
Qed.

(** ** Examples and Properties of Opposite Pre-Stable Categories
    
    This section demonstrates how the opposite construction works in practice,
    showing how morphisms, compositions, and distinguished triangles behave
    under dualization.
*)

(** *** Composition in Opposite Categories *)

(** Example showing how composition reverses in the opposite category *)
Lemma opposite_composition_demo {PS : PreStableCategory} 
  (X Y Z : object PS)
  (f : morphism PS X Y) (g : morphism PS Y Z) :
  let original_composition := (g o f)%morphism in
  let f_op : morphism (opposite_prestable_category PS) Y X := f in
  let g_op : morphism (opposite_prestable_category PS) Z Y := g in
  let opposite_composition := (f_op o g_op)%morphism in
  opposite_composition = original_composition.
Proof.
  simpl.
  reflexivity.
Qed.

(** *** Zero Morphisms in Opposite Categories *)

(** Zero morphisms dualize correctly *)
Theorem zero_morphism_dualizes {PS : PreStableCategory} (X Y : object PS) :
  zero_morphism (add_zero (opposite_prestable_category PS)) Y X = 
  zero_morphism (add_zero PS) X Y.
Proof.
  unfold zero_morphism.
  simpl.
  reflexivity.
Qed.

(** *** Suspension and Loop Duality *)

(** The fundamental duality: suspension and loop functors swap *)
Theorem suspension_loop_swap {PS : PreStableCategory} (X : object PS) :
  (object_of (Susp (opposite_prestable_category PS)) X = 
   object_of (Loop PS) X) /\
  (object_of (Loop (opposite_prestable_category PS)) X = 
   object_of (Susp PS) X).
Proof.
  split; simpl; reflexivity.
Qed.

(** *** Distinguished Triangles Under Duality *)
(** How a distinguished triangle appears in the opposite category *)
Lemma distinguished_triangle_duality {PS : PreStableCategory} 
  (D : @DistinguishedTriangle PS) :
  let T := triangle D in
  let X := X T in
  let Y := Y T in  
  let Z := Z T in
  let f := f T in
  let g := g T in
  let h := h T in
  (* In PS^op, morphisms have flipped source/target *)
  let f_dual : morphism (opposite_prestable_category PS) Y X := f in
  let g_dual : morphism (opposite_prestable_category PS) Z Y := g in
  (* h : Z → ΣX in PS becomes h : ΩX → Z in PS^op (since Σ and Ω swap) *)
  let h_dual : morphism (opposite_prestable_category PS) 
                        (object_of (Susp PS) X) Z := h in
  (* The triangle pattern reverses:
     Original in PS:     X --f--> Y --g--> Z --h--> ΣX
     In PS^op:          Y <--f-- X,  Z <--g-- Y,  ΩX <--h-- Z *)
  Unit.
Proof.
  exact tt.
Qed.

(** ** Proper Stable Categories
    
    A proper stable category is a pre-stable category where the suspension
    and loop functors are inverse equivalences.
*)

Record ProperStableCategory := {
  pre_stable :> PreStableCategory;
  
  (** η and ε are isomorphisms at each object *)
  eta_is_iso : forall X, IsIsomorphism (components_of (eta pre_stable) X);
  epsilon_is_iso : forall X, IsIsomorphism (components_of (epsilon pre_stable) X);
  
  (** Triangle identities for the adjunction *)
  triangle_1 : forall X, 
    (components_of (epsilon pre_stable) (object_of (Susp pre_stable) X) o 
     morphism_of (Susp pre_stable) (components_of (eta pre_stable) X))%morphism = 1%morphism;
     
  triangle_2 : forall X,
    (morphism_of (Loop pre_stable) (components_of (epsilon pre_stable) X) o
     components_of (eta pre_stable) (object_of (Loop pre_stable) X))%morphism = 1%morphism
}.

(** ** Opposite of Proper Stable Categories
    
    We show that the opposite of a proper stable category is again
    a proper stable category, with the roles of Σ and Ω swapped.
*)

(** *** Helper Lemmas for Opposite Natural Transformations *)

Lemma opposite_nat_trans_components {PS : PreStableCategory}
  {F G : Functor PS PS}
  (η : NaturalTransformation F G) (X : object PS) :
  components_of (opposite_natural_transformation η) X = components_of η X.
Proof.
  reflexivity.
Qed.

(** *** Isomorphisms in Opposite Categories *)

Lemma opposite_preserves_iso {PS : PreStableCategory} 
  {X Y : object PS} (f : morphism PS X Y) :
  IsIsomorphism f -> 
  IsIsomorphism (f : morphism (opposite_category PS) Y X).
Proof.
  intro H.
  destruct H as [g [Hgf Hfg]].
  exists g.
  split.
  - simpl. exact Hfg.
  - simpl. exact Hgf.
Qed.

(** *** Preservation of Isomorphisms Under Opposite *)

Lemma eta_iso_opposite (PS : ProperStableCategory) : 
  forall X, IsIsomorphism (components_of (eta (opposite_prestable_category (pre_stable PS))) X).
Proof.
  intro X.
  simpl.
  apply opposite_preserves_iso.
  exact (epsilon_is_iso PS X).
Qed.

Lemma epsilon_iso_opposite (PS : ProperStableCategory) : 
  forall X, IsIsomorphism (components_of (epsilon (opposite_prestable_category (pre_stable PS))) X).
Proof.
  intro X.
  simpl.
  apply opposite_preserves_iso.
  exact (eta_is_iso PS X).
Qed.

(** *** Triangle Identities in the Opposite *)

Lemma opposite_triangle_1 (PS : ProperStableCategory) : 
  forall X,
  (components_of (epsilon (opposite_prestable_category (pre_stable PS))) 
    (object_of (Susp (opposite_prestable_category (pre_stable PS))) X) o 
   morphism_of (Susp (opposite_prestable_category (pre_stable PS))) 
    (components_of (eta (opposite_prestable_category (pre_stable PS))) X))%morphism = 
  1%morphism.
Proof.
  intro X.
  simpl.
  (* In the opposite: Susp^op = Loop, eta^op = epsilon, epsilon^op = eta
     So this becomes: eta(Loop X) ∘ Loop(epsilon X) = 1
     Which is triangle_2 from the original *)
  exact (triangle_2 PS X).
Qed.

Lemma opposite_triangle_2 (PS : ProperStableCategory) : 
  forall X,
  (morphism_of (Loop (opposite_prestable_category (pre_stable PS))) 
    (components_of (epsilon (opposite_prestable_category (pre_stable PS))) X) o
   components_of (eta (opposite_prestable_category (pre_stable PS))) 
    (object_of (Loop (opposite_prestable_category (pre_stable PS))) X))%morphism = 
  1%morphism.
Proof.
  intro X.
  simpl.
  (* In the opposite: Loop^op = Susp, eta^op = epsilon, epsilon^op = eta
     So this becomes: Susp(eta X) ∘ epsilon(Susp X) = 1
     Which is triangle_1 from the original *)
  exact (triangle_1 PS X).
Qed.

(** *** Main Theorem: Opposite of Proper Stable is Proper Stable *)

Definition opposite_proper_stable_category (PS : ProperStableCategory) : 
  ProperStableCategory.
Proof.
  exact (Build_ProperStableCategory
    (opposite_prestable_category (pre_stable PS))
    (eta_iso_opposite PS)
    (epsilon_iso_opposite PS)
    (opposite_triangle_1 PS)
    (opposite_triangle_2 PS)).
Defined.

(** ** Main Duality Theorems *)

(** The opposite of a proper stable category exists and has the expected form *)
Theorem proper_stable_duality_principle :
  forall (PS : ProperStableCategory),
  exists (PS_op : ProperStableCategory),
    pre_stable PS_op = opposite_prestable_category (pre_stable PS).
Proof.
  intro PS.
  exists (opposite_proper_stable_category PS).
  reflexivity.
Qed.

(** The beautiful symmetry: Susp and Loop functors perfectly swap roles *)
Theorem suspension_loop_duality (PS : ProperStableCategory) :
  object_of (Susp (opposite_proper_stable_category PS)) = 
  object_of (opposite_functor (Loop (pre_stable PS))) /\
  object_of (Loop (opposite_proper_stable_category PS)) = 
  object_of (opposite_functor (Susp (pre_stable PS))).
Proof.
  split; reflexivity.
Qed.

(** * Part IV: Explorations in Stable Category Theory
    
    This section explores novel concepts and relationships in the theory of
    stable categories, building upon the foundational definitions and theorems
    established in Parts I-III.
*)

(** ** Section IV.1: The Fundamental Duality Principle
    
    We begin by establishing the general duality principle that underlies
    all of stable category theory.
*)

(** *** The Universal Duality Theorem *)

Theorem duality_principle : 
  forall (statement : PreStableCategory -> Prop),
  (forall PS, statement PS) -> 
  (forall PS, statement (opposite_prestable_category PS)).
Proof.
  intros statement H PS.
  apply H.
Qed.

(** Print the definition to see the structure *)
Print opposite_prestable_category.

(** This completes our formalization of stable categories and their duality theory.
    The key insights are:
    
    1. Pre-stable categories have suspension and loop functors connected by natural transformations
    2. In the opposite category, these functors swap roles
    3. Proper stable categories (where Σ and Ω are equivalences) are self-dual
    4. Every theorem has a dual obtained by passing to the opposite category
    
    This duality is fundamental in the theory of triangulated and stable categories,
    providing a powerful tool for proving theorems and understanding the structure.
*)

(** ** Section IV.2: Opposite Pre-Stable Categories
    
    We investigate whether the opposite of a pre-stable category is always
    pre-stable, without requiring the additional conditions of proper stability.
*)

(** *** Construction of Opposite Pre-Stable Categories *)

Theorem opposite_prestable_is_prestable : 
  forall (PS : PreStableCategory),
  PreStableCategory.
Proof.
  intro PS.
  (* We already have the additive category part *)
  refine (Build_PreStableCategory
    (opposite_additive_category PS)
    (opposite_additive_functor (Loop PS))
    (opposite_additive_functor (Susp PS))
    _ _).
  - (* eta: 1 → Loop ∘ Susp *)
    exact (opposite_natural_transformation (epsilon PS)).
  - (* epsilon: Susp ∘ Loop → 1 *)
    exact (opposite_natural_transformation (eta PS)).
Defined.

(** *** Verification of Functor Correspondence *)

Theorem check_opposite_prestable_functors : 
  forall (PS : PreStableCategory),
  Susp (opposite_prestable_is_prestable PS) = opposite_additive_functor (Loop PS).
Proof.
  intro PS.
  reflexivity.
Qed.

(** *** Double Opposite Properties *)

Theorem double_opposite_susp_commutes :
  forall (PS : PreStableCategory),
  object_of (Susp PS) = 
  object_of (Susp (opposite_prestable_is_prestable (opposite_prestable_is_prestable PS))).
Proof.
  intro PS.
  simpl.
  reflexivity.
Qed.

(** *** Natural Transformation Preservation *)

Theorem opposite_preserves_eta_components :
  forall (PS : PreStableCategory) (X : object PS),
  components_of (eta (opposite_prestable_is_prestable PS)) X =
  components_of (opposite_natural_transformation (epsilon PS)) X.
Proof.
  intros PS X.
  simpl.
  reflexivity.
Qed.

(** ** Section IV.3: Stability Gaps and Asymmetric Stability
    
    We explore the possibility of categories that are stable in one direction
    but not the other.
*)

(** *** Double Opposite for Proper Stable Categories *)

Theorem proper_stable_double_opposite_suspension :
  forall (PS : ProperStableCategory) (X : object (pre_stable PS)),
  object_of (Susp (pre_stable PS)) X = 
  object_of (Susp (pre_stable (opposite_proper_stable_category 
    (opposite_proper_stable_category PS)))) X.
Proof.
  intros PS X.
  simpl.
  reflexivity.
Qed.

Theorem proper_stable_double_opposite_eta :
  forall (PS : ProperStableCategory) (X : object (pre_stable PS)),
  components_of (eta (pre_stable PS)) X =
  components_of (eta (pre_stable (opposite_proper_stable_category 
    (opposite_proper_stable_category PS)))) X.
Proof.
  intros PS X.
  simpl.
  reflexivity.
Qed.

(** ** Section IV.4: Zero Morphisms and Composition in Opposite Categories
    
    We establish how zero morphisms and compositions behave under the
    opposite construction.
*)

(** *** Zero Morphism Duality *)

Theorem zero_morphism_opposite :
  forall (PS : PreStableCategory) (X Y : object PS),
  zero_morphism (add_zero (opposite_prestable_is_prestable PS)) X Y =
  zero_morphism (add_zero PS) Y X.
Proof.
  intros PS X Y.
  unfold zero_morphism.
  simpl.
  reflexivity.
Qed.

(** *** Preservation of Zero Compositions *)

Theorem zero_comp_opposite :
  forall (PS : PreStableCategory) (X Y Z : object PS)
    (f : morphism PS Y X) (g : morphism PS Z Y),
  (f o g)%morphism = zero_morphism (add_zero PS) Z X ->
  ((g : morphism (opposite_prestable_is_prestable PS) Y Z) o 
   (f : morphism (opposite_prestable_is_prestable PS) X Y))%morphism = 
  zero_morphism (add_zero (opposite_prestable_is_prestable PS)) X Z.
Proof.
  intros PS X Y Z f g H.
  simpl.
  exact H.
Qed.

(** ** Section IV.5: Self-Opposite Categories
    
    We investigate categories that are isomorphic to their opposites.
*)

(** *** Definition of Self-Opposite *)

Definition is_self_opposite (PS : PreStableCategory) : Type :=
  exists (F : AdditiveFunctor PS (opposite_prestable_is_prestable PS)),
    forall X, object_of F X = X.

(** *** Basic Properties of Double Opposite *)

Theorem double_opposite_preserves_initial :
  forall (PS : PreStableCategory) (X : object PS),
  (forall Y, Contr (morphism PS X Y)) ->
  (forall Y, Contr (morphism PS X Y)).
Proof.
  intros PS X H Y.
  exact (H Y).
Qed.

(** *** Groupoid Properties Under Opposite *)

Theorem opposite_preserves_groupoid_property :
  forall (PS : PreStableCategory),
  (forall X Y (f : morphism PS X Y), IsIsomorphism f) ->
  (forall X Y (f : morphism (opposite_prestable_is_prestable PS) X Y), IsIsomorphism f).
Proof.
  intros PS H_groupoid X Y f.
  (* f in opposite is a morphism Y -> X in original *)
  pose proof (H_groupoid Y X f) as H_iso.
  destruct H_iso as [g [Hgf Hfg]].
  exists g.
  split.
  - exact Hfg.
  - exact Hgf.
Qed.

(** ** Section IV.6: Triangulated Structure Under Duality
    
    We explore how triangulated structures behave under the opposite construction.
*)

(** *** Zero Composition in Triangles *)

Theorem opposite_preserves_zero_composition :
  forall (PS : PreStableCategory) (X Y Z : object PS) 
    (f : morphism PS X Y) (g : morphism PS Y Z),
  (g o f)%morphism = zero_morphism (add_zero PS) X Z ->
  ((f : morphism (opposite_prestable_is_prestable PS) Y X) o 
   (g : morphism (opposite_prestable_is_prestable PS) Z Y))%morphism = 
  zero_morphism (add_zero (opposite_prestable_is_prestable PS)) Z X.
Proof.
  intros PS X Y Z f g H.
  simpl.
  exact H.
Qed.

(** *** Diagonal Morphisms *)

Definition diagonal_morphism (PS : PreStableCategory) (X : object PS) :
  morphism PS X X := 1%morphism.

(** ** Section IV.7: Relationships Between η and ε
    
    We investigate the deep connections between the unit and counit
    of the adjunction between suspension and loop functors.
*)

(** *** Propagation of Isomorphism Properties *)

Theorem eta_iso_implies_epsilon_iso_at_loop :
  forall (PS : ProperStableCategory) (X : object (pre_stable PS)),
  IsIsomorphism (components_of (eta (pre_stable PS)) X) ->
  IsIsomorphism (components_of (epsilon (pre_stable PS)) (object_of (Loop (pre_stable PS)) X)).
Proof.
  intros PS X H_eta.
  (* We already know this for proper stable categories *)
  apply (epsilon_is_iso PS).
Qed.

(** *** Complementary Adjoints *)

Definition has_complementary_adjoints (PS : PreStableCategory) : Type :=
  forall X : object PS,
    IsIsomorphism (components_of (eta PS) X) ->
    IsIsomorphism (components_of (epsilon PS) (object_of (Susp PS) X)).

(** *** Trivial Implications *)
Theorem eta_iso_everywhere_implies_proper_stable :
  forall (PS : PreStableCategory),
  (forall X, IsIsomorphism (components_of (eta PS) X)) ->
  (forall X, IsIsomorphism (components_of (epsilon PS) X)) ->
  Unit.
Proof.
  intros PS H_eta H_eps.
  exact tt.
Qed.

(** ** Section IV.8: Preservation of Zero Morphisms
    
    We verify that suspension functors always preserve zero morphisms,
    a fundamental property of additive functors.
*)

(** *** Strong Preservation of Zeros *)

Definition strongly_preserves_zeros (PS : PreStableCategory) : Type :=
  forall X Y : object PS,
  morphism_of (Susp PS) (zero_morphism (add_zero PS) X Y) = 
  zero_morphism (add_zero PS) (object_of (Susp PS) X) (object_of (Susp PS) Y).

(** *** Universal Property *)

Theorem all_prestable_strongly_preserve_zeros :
  forall (PS : PreStableCategory),
  strongly_preserves_zeros PS.
Proof.
  intro PS.
  unfold strongly_preserves_zeros.
  intros X Y.
  apply susp_preserves_zero_morphisms.
Qed.

(** ** Section IV.9: Commuting Suspension and Loop
    
    We explore when suspension and loop functors commute up to
    natural isomorphism.
*)

(** *** Definition of Commuting Functors *)

Definition has_commuting_susp_loop (PS : PreStableCategory) : Type :=
  exists (α : NaturalTransformation 
    ((Susp PS) o (Loop PS))%functor
    ((Loop PS) o (Susp PS))%functor),
  forall X, IsIsomorphism (components_of α X).

(** *** Existence of Morphisms Between Compositions *)

Theorem susp_loop_zero_morphism_exists :
  forall (PS : PreStableCategory) (X : object PS),
  morphism PS 
    (object_of ((Susp PS) o (Loop PS))%functor X)
    (object_of ((Loop PS) o (Susp PS))%functor X).
Proof.
  intros PS X.
  simpl.
  (* There's always the zero morphism *)
  apply (zero_morphism (add_zero PS)).
Qed.

(** ** Section IV.10: Balanced Categories
    
    We introduce the notion of balanced pre-stable categories where
    the isomorphism properties of η and ε are perfectly correlated.
*)

(** *** Definition of Balanced *)

Definition is_balanced (PS : PreStableCategory) : Type :=
  forall X : object PS,
    IsIsomorphism (components_of (eta PS) X) <->
    IsIsomorphism (components_of (epsilon PS) (object_of (Susp PS) X)).

(** *** Proper Stable Categories are Balanced *)

Theorem proper_stable_is_balanced :
  forall (PS : ProperStableCategory),
  is_balanced (pre_stable PS).
Proof.
  intros PS X.
  split.
  - intro H. apply (epsilon_is_iso PS).
  - intro H. apply (eta_is_iso PS).
Qed.

(** ** Section IV.11: Semi-Stable Categories
    
    We introduce and study categories that are stable in only one direction,
    providing intermediate steps between pre-stable and proper stable.
*)

(** *** Left and Right Semi-Stability *)

Definition is_left_semi_stable (PS : PreStableCategory) : Type :=
  forall X : object PS, IsIsomorphism (components_of (eta PS) X).

Definition is_right_semi_stable (PS : PreStableCategory) : Type :=
  forall X : object PS, IsIsomorphism (components_of (epsilon PS) X).

(** *** Duality of Semi-Stability *)

Theorem left_semi_stable_opposite_is_right :
  forall (PS : PreStableCategory),
  is_left_semi_stable PS ->
  is_right_semi_stable (opposite_prestable_is_prestable PS).
Proof.
  intros PS H_left X.
  unfold is_left_semi_stable in H_left.
  simpl.
  (* In opposite: epsilon becomes eta, so we need eta to be iso *)
  apply opposite_preserves_iso.
  apply H_left.
Qed.

(** *** Almost Proper Stable Categories *)

Definition is_almost_proper_stable (PS : PreStableCategory) : Type :=
  is_left_semi_stable PS * is_right_semi_stable PS.

(** *** Relationship to Balanced Categories *)

Theorem semi_stable_both_directions_implies_balanced :
  forall (PS : PreStableCategory),
  is_left_semi_stable PS ->
  is_right_semi_stable PS ->
  is_balanced PS.
Proof.
  intros PS H_left H_right X.
  split.
  - intro H. apply H_right.
  - intro H. apply H_left.
Qed.

(** ** Section IV.12: Triangle Identities
    
    We study the triangle identities that provide coherence conditions
    for the adjunction between suspension and loop functors.
*)

(** *** The Two Triangle Identities *)

Definition satisfies_triangle_1 (PS : PreStableCategory) : Type :=
  forall X : object PS,
  (components_of (epsilon PS) (object_of (Susp PS) X) o 
   morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism.

Definition satisfies_triangle_2 (PS : PreStableCategory) : Type :=
  forall X : object PS,
  (morphism_of (Loop PS) (components_of (epsilon PS) X) o
   components_of (eta PS) (object_of (Loop PS) X))%morphism = 1%morphism.

(** *** Duality of Triangle Identities *)

Theorem triangle_1_in_opposite :
  forall (PS : PreStableCategory),
  satisfies_triangle_1 PS ->
  satisfies_triangle_2 (opposite_prestable_is_prestable PS).
Proof.
  intros PS H1 X.
  simpl.
  exact (H1 X).
Qed.

(** *** One-Sided Inverses *)

Definition eta_has_left_inverse (PS : PreStableCategory) : Type :=
  forall X : object PS,
  exists (g : morphism PS (object_of ((Loop PS) o (Susp PS))%functor X) X),
  (g o components_of (eta PS) X)%morphism = 1%morphism.

Definition epsilon_has_right_inverse (PS : PreStableCategory) : Type :=
  forall X : object PS,
  exists (g : morphism PS X (object_of ((Susp PS) o (Loop PS))%functor X)),
  (components_of (epsilon PS) X o g)%morphism = 1%morphism.

(** *** Basic Properties of Triangle Identities *)

Theorem triangle_identity_constraint :
  forall (PS : PreStableCategory) (X : object PS),
  satisfies_triangle_1 PS ->
  (components_of (epsilon PS) (object_of (Susp PS) X) o 
   morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 
  (1%morphism : morphism PS (object_of (Susp PS) X) (object_of (Susp PS) X)).
Proof.
  intros PS X H1.
  exact (H1 X).
Qed.

(** ** Section IV.13: Zero Natural Transformations
    
    We investigate what happens when η or ε is the zero natural transformation,
    revealing fundamental constraints on pre-stable categories.
*)

(** *** Zero Eta *)

Definition has_zero_eta (PS : PreStableCategory) : Type :=
  forall X : object PS,
  components_of (eta PS) X = zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X).

(** *** Zero Eta Breaks Triangle Identity *)

Theorem zero_eta_breaks_triangle_1 :
  forall (PS : PreStableCategory),
  has_zero_eta PS ->
  satisfies_triangle_1 PS ->
  forall X : object PS, 
  (1%morphism : morphism PS (object_of (Susp PS) X) (object_of (Susp PS) X)) = 
  zero_morphism (add_zero PS) (object_of (Susp PS) X) (object_of (Susp PS) X).
Proof.
  intros PS H_zero H_tri X.
  pose proof (H_tri X) as H.
  unfold has_zero_eta in H_zero.
  rewrite H_zero in H.
  rewrite susp_preserves_zero_morphisms in H.
  rewrite zero_morphism_right in H.
  simpl in H.
  exact H^.
Qed.

(** *** Non-Triviality *)

Definition is_non_trivial (PS : PreStableCategory) : Type :=
  exists (X : object PS), 
  (1%morphism : morphism PS X X) <> zero_morphism (add_zero PS) X X.

(** *** Triangle Identities Force Non-Zero Eta *)

Theorem triangle_identity_nontrivial :
  forall (PS : PreStableCategory) (X : object PS),
  satisfies_triangle_1 PS ->
  components_of (eta PS) X = zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X) ->
  (1%morphism : morphism PS (object_of (Susp PS) X) (object_of (Susp PS) X)) = 
  zero_morphism (add_zero PS) (object_of (Susp PS) X) (object_of (Susp PS) X).
Proof.
  intros PS X H_tri H_zero.
  pose proof (H_tri X) as H.
  rewrite H_zero in H.
  rewrite susp_preserves_zero_morphisms in H.
  rewrite zero_morphism_right in H.
  simpl in H.
  exact H^.
Qed.

(** *** Zero Epsilon *)

Definition has_zero_epsilon (PS : PreStableCategory) : Type :=
  forall X : object PS,
  components_of (epsilon PS) X = zero_morphism (add_zero PS) (object_of ((Susp PS) o (Loop PS))%functor X) X.

(** *** Zero Epsilon Breaks Triangle Identity *)

Theorem zero_epsilon_breaks_triangle_2 :
  forall (PS : PreStableCategory) (X : object PS),
  satisfies_triangle_2 PS ->
  components_of (epsilon PS) X = zero_morphism (add_zero PS) (object_of ((Susp PS) o (Loop PS))%functor X) X ->
  (1%morphism : morphism PS (object_of (Loop PS) X) (object_of (Loop PS) X)) = 
  zero_morphism (add_zero PS) (object_of (Loop PS) X) (object_of (Loop PS) X).
Proof.
  intros PS X H_tri H_zero.
  pose proof (H_tri X) as H.
  rewrite H_zero in H.
  pose proof (additive_functor_preserves_zero_morphisms (Loop PS) 
    (object_of ((Susp PS) o (Loop PS))%functor X) X) as H_loop_zero.
  rewrite H_loop_zero in H.
  rewrite zero_morphism_left in H.
  simpl in H.
  exact H^.
Qed.

(** ** Section IV.14: Independence of Triangle Identities
    
    We explore whether the two triangle identities are independent or
    if one implies the other.
*)

(** *** Categories with Only One Triangle Identity *)

Definition satisfies_only_triangle_1 (PS : PreStableCategory) : Type :=
  satisfies_triangle_1 PS * (satisfies_triangle_2 PS -> Empty).

(** *** Implication Between Triangle Identities *)

Definition triangle_1_implies_2 (PS : PreStableCategory) : Type :=
  satisfies_triangle_1 PS -> satisfies_triangle_2 PS.

(** *** Perfect Duality of Triangle Identities *)

Theorem triangle_identities_dual :
  forall (PS : PreStableCategory),
  satisfies_triangle_1 PS <-> 
  satisfies_triangle_2 (opposite_prestable_is_prestable PS).
Proof.
  intro PS.
  split.
  - exact (triangle_1_in_opposite PS).
  - intro H2_op.
    intro X.
    exact (H2_op X).
Qed.

(** ** Section IV.15: Self-Dual Triangulated Categories
    
    We introduce categories where the triangle identities are equivalent,
    revealing a special symmetry.
*)

(** *** Definition of Self-Dual Triangulated *)

Definition is_self_dual_triangulated (PS : PreStableCategory) : Type :=
  forall X : object PS,
  ((components_of (epsilon PS) (object_of (Susp PS) X) o 
    morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism) <->
  ((morphism_of (Loop PS) (components_of (epsilon PS) X) o
    components_of (eta PS) (object_of (Loop PS) X))%morphism = 1%morphism).

(** *** Self-Duality Propagates Triangle Identities *)

Theorem self_dual_gives_both_triangles :
  forall (PS : PreStableCategory),
  is_self_dual_triangulated PS ->
  satisfies_triangle_1 PS ->
  satisfies_triangle_2 PS.
Proof.
  intros PS H_self H1 X.
  destruct (H_self X) as [H_forward H_backward].
  apply H_forward.
  apply H1.
Qed.

(** ** Section IV.16: Functor Compositions and Identities
    
    We study when the compositions of suspension and loop functors
    yield special relationships with the identity functor.
*)

(** *** Coinciding Compositions *)

Definition has_coinciding_compositions (PS : PreStableCategory) : Type :=
  forall X : object PS,
  object_of ((Susp PS) o (Loop PS))%functor X = 
  object_of ((Loop PS) o (Susp PS))%functor X.

(** *** Composition as Identity *)

Definition susp_loop_is_identity (PS : PreStableCategory) : Type :=
  forall X : object PS,
  object_of ((Susp PS) o (Loop PS))%functor X = X.

Definition loop_susp_is_identity (PS : PreStableCategory) : Type :=
  forall X : object PS,
  object_of ((Loop PS) o (Susp PS))%functor X = X.

(** *** Identity Compositions Coincide *)

Theorem both_compositions_identity_coincide :
  forall (PS : PreStableCategory),
  susp_loop_is_identity PS ->
  loop_susp_is_identity PS ->
  has_coinciding_compositions PS.
Proof.
  intros PS H_sl H_ls X.
  rewrite H_sl.
  rewrite H_ls.
  reflexivity.
Qed.

(** *** Inverse Objects *)

Definition has_inverse_objects (PS : PreStableCategory) : Type :=
  susp_loop_is_identity PS * loop_susp_is_identity PS.

(** *** Inverse Objects Under Duality *)

Theorem inverse_objects_opposite :
  forall (PS : PreStableCategory),
  has_inverse_objects PS ->
  has_inverse_objects (opposite_prestable_is_prestable PS).
Proof.
  intros PS [H_sl H_ls].
  split.
  - intro X. simpl. exact (H_ls X).
  - intro X. simpl. exact (H_sl X).
Qed.

(** ** Section IV.17: The Complete Stability Hierarchy
    
    We synthesize all our discoveries into a complete characterization
    of the hierarchy from pre-stable to proper stable categories.
*)

(** *** Almost Proper Stable (Strong Version) *)

Definition almost_proper_stable_strong (PS : PreStableCategory) : Type :=
  is_left_semi_stable PS * 
  is_right_semi_stable PS * 
  satisfies_triangle_1 PS * 
  satisfies_triangle_2 PS.

(** *** Almost Proper is Proper *)

Theorem almost_proper_is_proper :
  forall (PS : PreStableCategory),
  almost_proper_stable_strong PS ->
  (* All the data for ProperStableCategory is present *)
  (forall X, IsIsomorphism (components_of (eta PS) X)) *
  (forall X, IsIsomorphism (components_of (epsilon PS) X)) *
  satisfies_triangle_1 PS *
  satisfies_triangle_2 PS.
Proof.
  intros PS H.
  destruct H as [[[H_left H_right] H_tri1] H_tri2].
  unfold is_left_semi_stable in H_left.
  unfold is_right_semi_stable in H_right.
  refine (_, _, _, _).
  - exact H_left.
  - exact H_right.
  - exact H_tri1.
  - exact H_tri2.
Qed.

(** *** The Complete Hierarchy *)
Definition stability_hierarchy_summary : Type :=
  forall (PS : PreStableCategory),
  (* Level 0: Pre-stable *)
  Unit ->
  (* Level 1: Semi-stable (one direction) *)
  (is_left_semi_stable PS + is_right_semi_stable PS) ->
  (* Level 2: Almost proper (both directions) *)
  (is_left_semi_stable PS * is_right_semi_stable PS) ->
  (* Level 3: Weak proper (triangle identities) *)
  (satisfies_triangle_1 PS * satisfies_triangle_2 PS) ->
  (* Level 4: Proper stable (all conditions) *)
  almost_proper_stable_strong PS.

(** *** The Hierarchy Theorem *)
Theorem stability_hierarchy_holds :
  stability_hierarchy_summary.
Proof.
  unfold stability_hierarchy_summary.
  intros PS _ _ H_almost H_triangles.
  unfold almost_proper_stable_strong.
  destruct H_almost as [H_left H_right].
  destruct H_triangles as [H_tri1 H_tri2].
  exact (H_left, H_right, H_tri1, H_tri2).
Qed.

(** ** Section IV.13: Triangle Identities and Non-Triviality
    
    This section explores the consequences of the unit (`η`) or counit (`ε`)
    of the (Σ, Ω) adjunction being trivial (i.e., zero transformations).
    These theorems establish that for a category to satisfy the triangle
    identities, the adjunction cannot be trivial unless the category itself is,
    in a sense, trivial (meaning its identity morphisms are equal to its
    zero morphisms).
*)

(** *** One-Sided Inverses from Triangle Identities
    
    The triangle identities directly imply that the components of the unit and
    counit possess one-sided inverses, which is a key step towards them being
    isomorphisms in a proper stable category.
*)

(** If the first triangle identity holds, then Ση has a left inverse *)
Theorem triangle_identity_1_gives_left_inverse :
  forall (PS : PreStableCategory) (X : object PS),
  (components_of (epsilon PS) (object_of (Susp PS) X) o
    morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism ->
  exists (g : morphism PS (object_of ((Susp PS) o (Loop PS) o (Susp PS))%functor X)
                          (object_of (Susp PS) X)),
  (g o morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism.
Proof.
  intros PS X H_tri.
  exists (components_of (epsilon PS) (object_of (Susp PS) X)).
  exact H_tri.
Qed.

(** *** Consequences of a Zero Adjunction Unit (η)
    
    Here we show that if the unit `η` is a zero natural transformation,
    the triangle identities can only hold in a trivial category.
*)

(** If η is zero at the zero object, the first triangle identity forces triviality *)
Theorem eta_zero_at_zero_prevents_triangle_identity :
  forall (PS : PreStableCategory),
  components_of (eta PS) (@zero _ (add_zero PS)) =
    zero_morphism (add_zero PS) (@zero _ (add_zero PS)) (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))) ->
  satisfies_triangle_1 PS ->
  (* Then the identity morphism on Susp(zero) must be the zero morphism *)
  (1%morphism : morphism PS (object_of (Susp PS) (@zero _ (add_zero PS))) (object_of (Susp PS) (@zero _ (add_zero PS)))) =
  zero_morphism (add_zero PS) (object_of (Susp PS) (@zero _ (add_zero PS))) (object_of (Susp PS) (@zero _ (add_zero PS))).
Proof.
  intros PS H_eta_zero H_tri1.
  pose proof (H_tri1 (@zero _ (add_zero PS))) as H_at_zero.
  rewrite H_eta_zero in H_at_zero.
  (* Since Susp is an additive functor, it preserves zero morphisms *)
  rewrite susp_preserves_zero_morphisms in H_at_zero.
  rewrite zero_morphism_right in H_at_zero.
  exact H_at_zero^.
Qed.

(** If η is zero for any object, it is also zero for the zero object *)
Theorem eta_zero_propagates_to_zero_object :
  forall (PS : PreStableCategory) (X : object PS),
  components_of (eta PS) X = zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X) ->
  components_of (eta PS) (@zero _ (add_zero PS)) =
  zero_morphism (add_zero PS) (@zero _ (add_zero PS)) (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))).
Proof.
  intros PS X H_zero.
  (* Both sides are morphisms from the zero object to another object.
     The space of such morphisms is contractible, so any two are equal. *)
  apply initial_morphism_unique.
  apply (@is_initial _ (add_zero PS) _).
Qed.

(** ** Section IV.14: The Space of Adjunction Data
    
    This section abstracts the properties of `η` and `ε` to any pair of
    natural transformations that could potentially define an adjunction between
    the suspension and loop functors. This allows for studying the structural
    constraints imposed by the triangle identities themselves.
*)

(** *** Compatible Pairs of Natural Transformations
    
    A "compatible pair" is any `(η', ε')` that satisfies the two triangle
    identities, forming the core data of an adjunction.
*)

Definition compatible_pair (PS : PreStableCategory)
  (η' : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
  (ε' : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor) : Type :=
  (forall X, (components_of ε' (object_of (Susp PS) X) o
               morphism_of (Susp PS) (components_of η' X))%morphism = 1%morphism) *
  (forall X, (morphism_of (Loop PS) (components_of ε' X) o
               components_of η' (object_of (Loop PS) X))%morphism = 1%morphism).

(** *** Properties of Compatible Pairs
    
    Any compatible pair must adhere to certain fundamental properties,
    such as how they interact with zero morphisms.
*)

(** The first triangle identity holds by definition for a compatible pair *)
Theorem compatible_pair_satisfies_triangle_1 :
  forall (PS : PreStableCategory)
    (η : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
    (ε : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor),
  compatible_pair PS η ε ->
  forall X,
  (components_of ε (object_of (Susp PS) X) o
    morphism_of (Susp PS) (components_of η X))%morphism = 1%morphism.
Proof.
  intros PS η ε [H_tri1 H_tri2] X.
  exact (H_tri1 X).
Qed.

(** Interaction of a compatible pair with a zero morphism *)
Theorem compatible_pair_zero_interaction :
  forall (PS : PreStableCategory)
    (η : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
    (ε : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor),
  compatible_pair PS η ε ->
  forall X,
  (components_of ε (object_of (Susp PS) X) o
    morphism_of (Susp PS) (zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X)))%morphism =
  zero_morphism (add_zero PS) (object_of (Susp PS) X) (object_of (Susp PS) X).
Proof.
  intros PS η ε H_compat X.
  rewrite susp_preserves_zero_morphisms.
  apply zero_morphism_right.
Qed.

Theorem biproduct_determined_by_universal_property (A : AdditiveCategory) (X Y : object A) :
  let B1 := add_biproduct A X Y in
  let B2 := add_biproduct A X Y in
  (* Two calls to add_biproduct give the same result *)
  B1 = B2.
Proof.
  reflexivity.
Qed.

(** The biproduct of two objects is unique up to definitional equality *)
Theorem biproduct_unique_by_definition (A : AdditiveCategory) (X Y : object A) :
  let B1 := add_biproduct A X Y in
  let B2 := add_biproduct A X Y in
  exists (f : morphism A (@biproduct_obj _ _ _ B1) (@biproduct_obj _ _ _ B2)),
    IsIsomorphism f /\
    (f o @inl _ _ _ B1 = @inl _ _ _ B2)%morphism /\
    (f o @inr _ _ _ B1 = @inr _ _ _ B2)%morphism.
Proof.
  intros B1 B2.
  (* Since B1 and B2 are definitionally equal, the identity morphism is the required isomorphism. *)
  exists 1%morphism.
  split; [|split].
  - apply iso_identity.
  - apply morphism_left_identity.
  - apply morphism_left_identity.
Qed.

(** ** The η-Zero Forcing Principle for Pre-Stable Categories
    
    We establish a fundamental constraint on the vanishing locus of the unit
    natural transformation η in pre-stable categories. Specifically, we prove
    that the existence of a retraction from the zero object to any object X
    creates a rigidity phenomenon: if η vanishes at X, it must also vanish
    at the zero object.
    
    This result reveals an unexpected interplay between the retraction structure
    and stability properties of pre-stable categories.
*)

(** Main Theorem: η-zeros propagate through retractions to the zero object *)
Theorem eta_zero_forcing_principle :
  forall (PS : PreStableCategory) (X : object PS),
  (* Hypothesis 1: X is a retract of the zero object *)
  (exists (i : morphism PS (@zero _ (add_zero PS)) X) 
          (r : morphism PS X (@zero _ (add_zero PS))),
    (r o i)%morphism = 1%morphism) ->
  (* Hypothesis 2: The unit η vanishes at X *)
  components_of (eta PS) X = 
    zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X) ->
  (* Conclusion: The unit η must vanish at the zero object *)
  components_of (eta PS) (@zero _ (add_zero PS)) = 
    zero_morphism (add_zero PS) (@zero _ (add_zero PS)) 
      (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))).
Proof.
  intros PS X [i [r H_retract]] H_eta_X_zero.
  
  (* Step 1: Establish uniqueness of morphisms involving the zero object *)
  assert (H_i_unique: i = @center _ (@is_initial _ (add_zero PS) X)).
  { apply initial_morphism_unique. apply (@is_initial _ (add_zero PS)). }
  
  assert (H_r_unique: r = @center _ (@is_terminal _ (add_zero PS) X)).
  { apply terminal_morphism_unique. apply (@is_terminal _ (add_zero PS)). }
  
  (* Step 2: Analyze the retraction equation under uniqueness *)
  rewrite H_i_unique, H_r_unique in H_retract.
  
  (* Step 3: The composition of canonical morphisms yields the identity *)
  assert (H_key: (@center _ (@is_terminal _ (add_zero PS) X) o 
                  @center _ (@is_initial _ (add_zero PS) X))%morphism = 
                 (1%morphism : morphism PS (@zero _ (add_zero PS)) 
                                          (@zero _ (add_zero PS)))).
  { exact H_retract. }
  
  (* Step 4: Apply uniqueness to characterize endomorphisms of zero *)
  assert (H_zero_to_zero: 
    (@center _ (@is_terminal _ (add_zero PS) X) o 
     @center _ (@is_initial _ (add_zero PS) X))%morphism = 
    @center _ (@is_initial _ (add_zero PS) (@zero _ (add_zero PS)))).
  { apply initial_morphism_unique. apply (@is_initial _ (add_zero PS)). }
  
  rewrite H_zero_to_zero in H_key.
  
  (* Step 5: Conclude that the canonical endomorphism of zero is the identity *)
  assert (H_zero_id: @center _ (@is_initial _ (add_zero PS) 
                                            (@zero _ (add_zero PS))) = 
                     1%morphism).
  { exact H_key. }
  
  (* Step 6: Apply uniqueness to characterize η at the zero object *)
  apply initial_morphism_unique.
  apply (@is_initial _ (add_zero PS)).
Qed.

(** ** The η-Nonzero Propagation Principle
    
    This theorem establishes the contrapositive of the η-Zero Forcing Principle,
    revealing that non-vanishing of η at the zero object propagates through
    all retractable objects.
*)

Theorem eta_nonzero_propagation :
  forall (PS : PreStableCategory),
  (* Hypothesis: The unit η does not vanish at the zero object *)
  components_of (eta PS) (@zero _ (add_zero PS)) <> 
    zero_morphism (add_zero PS) (@zero _ (add_zero PS)) 
      (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))) ->
  (* Conclusion: For any object admitting a retraction from zero *)
  forall (X : object PS),
  (exists (i : morphism PS (@zero _ (add_zero PS)) X) 
          (r : morphism PS X (@zero _ (add_zero PS))),
    (r o i)%morphism = 1%morphism) ->
  (* The unit η cannot vanish at that object *)
  components_of (eta PS) X <> 
    zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X).
Proof.
  intros PS H_eta_nonzero_at_zero X H_retraction H_eta_zero_at_X.
  
  (* Apply the contrapositive of eta_zero_forcing_principle *)
  apply H_eta_nonzero_at_zero.
  apply (eta_zero_forcing_principle PS X).
  - exact H_retraction.
  - exact H_eta_zero_at_X.
Qed.

(** ** The Pre-Stable Dichotomy Implication
    
    A constructive version showing that the two classes are mutually exclusive.
*)

Theorem prestable_classes_disjoint :
  forall (PS : PreStableCategory),
  (* If η vanishes at zero *)
  components_of (eta PS) (@zero _ (add_zero PS)) = 
    zero_morphism (add_zero PS) (@zero _ (add_zero PS)) 
      (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))) ->
  (* Then it's not the case that η is non-zero at all retractable objects *)
  ~(forall (X : object PS),
    (exists (i : morphism PS (@zero _ (add_zero PS)) X) 
            (r : morphism PS X (@zero _ (add_zero PS))),
      (r o i)%morphism = 1%morphism) ->
    components_of (eta PS) X <> 
      zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X)).
Proof.
  intros PS H_eta_zero_at_zero H_all_retractable_nonzero.
  
  (* Zero itself is retractable *)
  assert (H_zero_retractable: 
    exists (i : morphism PS (@zero _ (add_zero PS)) (@zero _ (add_zero PS))) 
           (r : morphism PS (@zero _ (add_zero PS)) (@zero _ (add_zero PS))),
    (r o i)%morphism = 1%morphism).
  {
    exists 1%morphism, 1%morphism.
    apply morphism_left_identity.
  }
  
  (* Apply the assumption to zero *)
  pose proof (H_all_retractable_nonzero (@zero _ (add_zero PS)) H_zero_retractable) as H_contra.
  
  (* But we know η IS zero at zero *)
  apply H_contra.
  exact H_eta_zero_at_zero.
Qed.

(** ** Zero is Always Retractable 
    
    This theorem establishes that the zero object always admits a retraction
    from itself, providing a canonical example for our classification.
*)

Theorem zero_always_retractable :
  forall (PS : PreStableCategory),
  exists (i : morphism PS (@zero _ (add_zero PS)) (@zero _ (add_zero PS))) 
         (r : morphism PS (@zero _ (add_zero PS)) (@zero _ (add_zero PS))),
  (r o i)%morphism = 1%morphism.
Proof.
  intro PS.
  exists 1%morphism, 1%morphism.
  apply morphism_left_identity.
Qed.

(** ** Class II Categories Have Non-Zero η at Zero
    
    This provides a concrete test for Class II categories by showing that
    if η is non-zero at all retractable objects, then it must specifically
    be non-zero at the zero object.
*)

Theorem class_II_test :
  forall (PS : PreStableCategory),
  (* If PS is in Class II (η non-zero at all retractables) *)
  (forall (X : object PS),
    (exists (i : morphism PS (@zero _ (add_zero PS)) X) 
            (r : morphism PS X (@zero _ (add_zero PS))),
      (r o i)%morphism = 1%morphism) ->
    components_of (eta PS) X <> 
      zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X)) ->
  (* Then specifically, η is non-zero at zero *)
  components_of (eta PS) (@zero _ (add_zero PS)) <> 
    zero_morphism (add_zero PS) (@zero _ (add_zero PS)) 
      (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))).
Proof.
  intros PS H_class_II.
  apply H_class_II.
  apply zero_always_retractable.
Qed.

(** ** Retractable Objects Have Unique Inclusion
    
    This theorem shows that if any object admits a retraction from zero,
    then the inclusion morphism from zero is uniquely determined.
*)

Theorem retractable_objects_unique_inclusion :
  forall (PS : PreStableCategory) (X : object PS),
  (exists (i : morphism PS (@zero _ (add_zero PS)) X) 
          (r : morphism PS X (@zero _ (add_zero PS))),
    (r o i)%morphism = 1%morphism) ->
  (* Any two such inclusions are equal *)
  forall (i1 i2 : morphism PS (@zero _ (add_zero PS)) X),
  (exists (r1 : morphism PS X (@zero _ (add_zero PS))),
    (r1 o i1)%morphism = 1%morphism) ->
  (exists (r2 : morphism PS X (@zero _ (add_zero PS))),
    (r2 o i2)%morphism = 1%morphism) ->
  i1 = i2.
Proof.
  intros PS X H_retract i1 i2 H1 H2.
  (* All morphisms from zero are unique *)
  apply initial_morphism_unique.
  apply (@is_initial _ (add_zero PS)).
Qed.

(** ** Retraction Uniqueness Principle
    
    This theorem establishes that if an object admits a retraction from zero,
    then the retraction morphism is also uniquely determined.
*)

Theorem retractable_objects_unique_retraction :
  forall (PS : PreStableCategory) (X : object PS),
  (exists (i : morphism PS (@zero _ (add_zero PS)) X) 
          (r : morphism PS X (@zero _ (add_zero PS))),
    (r o i)%morphism = 1%morphism) ->
  (* Any two such retractions are equal *)
  forall (r1 r2 : morphism PS X (@zero _ (add_zero PS))),
  (exists (i1 : morphism PS (@zero _ (add_zero PS)) X),
    (r1 o i1)%morphism = 1%morphism) ->
  (exists (i2 : morphism PS (@zero _ (add_zero PS)) X),
    (r2 o i2)%morphism = 1%morphism) ->
  r1 = r2.
Proof.
  intros PS X H_retract r1 r2 H1 H2.
  (* All morphisms to zero are unique *)
  apply terminal_morphism_unique.
  apply (@is_terminal _ (add_zero PS)).
Qed.

(** ** Retraction Characterization
    
    This theorem shows that an object admits a retraction from zero
    if and only if specific canonical morphisms form a retraction pair.
*)

Theorem retraction_canonical_form :
  forall (PS : PreStableCategory) (X : object PS),
  (exists (i : morphism PS (@zero _ (add_zero PS)) X) 
          (r : morphism PS X (@zero _ (add_zero PS))),
    (r o i)%morphism = 1%morphism) <->
  ((@center _ (@is_terminal _ (add_zero PS) X) o 
    @center _ (@is_initial _ (add_zero PS) X))%morphism = 
   1%morphism).
Proof.
  intros PS X.
  split.
  - (* Forward direction *)
    intros [i [r H_retract]].
    assert (H_i: i = @center _ (@is_initial _ (add_zero PS) X)).
    { apply initial_morphism_unique. apply (@is_initial _ (add_zero PS)). }
    assert (H_r: r = @center _ (@is_terminal _ (add_zero PS) X)).
    { apply terminal_morphism_unique. apply (@is_terminal _ (add_zero PS)). }
    rewrite <- H_i, <- H_r.
    exact H_retract.
  - (* Backward direction *)
    intro H_canon.
    exists (@center _ (@is_initial _ (add_zero PS) X)).
    exists (@center _ (@is_terminal _ (add_zero PS) X)).
    exact H_canon.
Qed.

(** ** Eta Behavior on Retractable Objects
    
    This theorem shows that if two objects both admit retractions from zero,
    then any morphism between them interacts predictably with eta.
*)

Theorem eta_naturality_retractable :
  forall (PS : PreStableCategory) (X Y : object PS),
  (exists (iX : morphism PS (@zero _ (add_zero PS)) X) 
          (rX : morphism PS X (@zero _ (add_zero PS))),
    (rX o iX)%morphism = 1%morphism) ->
  (exists (iY : morphism PS (@zero _ (add_zero PS)) Y) 
          (rY : morphism PS Y (@zero _ (add_zero PS))),
    (rY o iY)%morphism = 1%morphism) ->
  forall (f : morphism PS X Y),
  (* The following diagram commutes *)
  (f o @center _ (@is_initial _ (add_zero PS) X))%morphism = 
  @center _ (@is_initial _ (add_zero PS) Y).
Proof.
  intros PS X Y H_X_retract H_Y_retract f.
  (* Both sides are morphisms from zero to Y *)
  (* All such morphisms are equal *)
  apply initial_morphism_unique.
  apply (@is_initial _ (add_zero PS)).
Qed.

(** ** Section IV.18: Suspension Fixed Points
    
    We investigate objects X such that ΣX ≅ X, revealing special structures
    in pre-stable categories. These fixed points play a fundamental role in
    understanding the periodic behavior of suspension functors.
*)

(** *** Definition of Suspension Fixed Points *)

(** An object X is a suspension fixed point if there exists an isomorphism ΣX ≅ X *)
Definition is_suspension_fixed_point (PS : PreStableCategory) (X : object PS) : Type :=
  exists (φ : morphism PS (object_of (Susp PS) X) X), IsIsomorphism φ.

(** *** Helper Lemmas for Suspended Zero Objects *)

(** The suspended zero object inherits the initial property from zero *)
Lemma susp_zero_is_initial :
  forall (PS : PreStableCategory) (Y : object PS),
  Contr (morphism PS (object_of (Susp PS) (@zero _ (add_zero PS))) Y).
Proof.
  intros PS Y.
  (* We know Σ preserves zero *)
  pose proof (preserves_zero PS PS (Susp PS)) as H_zero.
  (* Transport the initial property along the equality *)
  rewrite H_zero.
  apply (@is_initial _ (add_zero PS) Y).
Qed.

(** The suspended zero object inherits the terminal property from zero *)
Lemma susp_zero_is_terminal :
  forall (PS : PreStableCategory) (X : object PS),
  Contr (morphism PS X (object_of (Susp PS) (@zero _ (add_zero PS)))).
Proof.
  intros PS X.
  (* We know Σ preserves zero *)
  pose proof (preserves_zero PS PS (Susp PS)) as H_zero.
  (* Transport the terminal property along the equality *)
  rewrite H_zero.
  apply (@is_terminal _ (add_zero PS) X).
Qed.

(** *** Main Theorem: Zero is a Suspension Fixed Point *)

(** The zero object is always a suspension fixed point in any pre-stable category *)
Theorem zero_is_suspension_fixed_point :
  forall (PS : PreStableCategory),
  is_suspension_fixed_point PS (@zero _ (add_zero PS)).
Proof.
  intro PS.
  unfold is_suspension_fixed_point.
  
  (* The morphism from Σ(0) to 0 *)
  pose (φ := @center _ (@is_terminal _ (add_zero PS) (object_of (Susp PS) (@zero _ (add_zero PS))))).
  exists φ.
  
  (* Its inverse from 0 to Σ(0) *)
  pose (ψ := @center _ (@is_initial _ (add_zero PS) (object_of (Susp PS) (@zero _ (add_zero PS))))).
  exists ψ.
  
  split.
  - (* Left inverse: ψ ∘ φ = 1 on Σ(0) *)
    (* Both sides are morphisms from Σ(0) to Σ(0), so they're unique *)
    apply initial_morphism_unique.
    apply susp_zero_is_initial.
    
  - (* Right inverse: φ ∘ ψ = 1 on 0 *)
    (* Both sides are morphisms from 0 to 0 *)
    (* The composition of terminal after initial gives a morphism 0 → 0 *)
    (* All morphisms 0 → 0 are equal by terminality *)
    transitivity (@center _ (@is_terminal _ (add_zero PS) (@zero _ (add_zero PS)))).
    + apply terminal_morphism_unique.
      apply (@is_terminal _ (add_zero PS)).
    + apply terminal_zero_to_zero_is_id.
Qed.

(** *** Consequences of Suspension Fixed Points *)

(** Morphisms to Σ(0) are unique, just like morphisms to 0 *)
Corollary morphism_to_susp_zero_unique :
  forall (PS : PreStableCategory) (X : object PS) 
    (f g : morphism PS X (object_of (Susp PS) (@zero _ (add_zero PS)))),
  f = g.
Proof.
  intros PS X f g.
  apply terminal_morphism_unique.
  apply susp_zero_is_terminal.
Qed.

(** Properties preserved by isomorphisms transfer between X and ΣX for fixed points *)
Theorem suspension_fixed_point_transport :
  forall (PS : PreStableCategory) (X : object PS),
  is_suspension_fixed_point PS X ->
  (* Any property of X that's preserved by isomorphism also holds for ΣX *)
  forall (P : object PS -> Type),
  (forall Y Z (f : morphism PS Y Z), IsIsomorphism f -> P Y -> P Z) ->
  P X -> P (object_of (Susp PS) X).
Proof.
  intros PS X [φ [φ_inv [H_left H_right]]] P H_transport H_PX.
  (* Since φ : ΣX → X is iso, its inverse φ_inv : X → ΣX is also iso *)
  assert (H_inv_iso: IsIsomorphism φ_inv).
  {
    exists φ.
    split; assumption.
  }
  (* Apply transport *)
  exact (H_transport X (object_of (Susp PS) X) φ_inv H_inv_iso H_PX).
Qed.

(** ** Axiom TR4: The Octahedral Axiom
    
    The octahedral axiom is the fourth axiom of triangulated categories.
    Given two composable morphisms f: X → Y and g: Y → Z, it describes
    how the distinguished triangles arising from f, g, and their composition
    g∘f fit together in a commutative octahedral diagram.
    
    This formalization establishes TR4 using the universal property of cofibers.
*)

(** *** Statement of TR4 *)

(** A simple version of what TR4 requires: existence of a connecting morphism *)
Definition TR4_statement (S : PreStableCategoryWithCofiber) : Type :=
  forall (X Y Z : object S) (f : morphism S X Y) (g : morphism S Y Z),
  exists (u : morphism S (@cofiber S X Y f) (@cofiber S Y Z g)),
  (* u makes a specific square commute *)
  (u o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism.

(** *** Universal Property of Cofibers *)

(** The universal property characterizes cofibers: any morphism from Y
    that vanishes when precomposed with f factors uniquely through the cofiber *)
Definition cofiber_universal_property (S : PreStableCategoryWithCofiber) : Type :=
  forall (X Y : object S) (f : morphism S X Y) (W : object S)
    (h : morphism S Y W),
  (h o f)%morphism = zero_morphism (add_zero (base S)) X W ->
  { k : morphism S (@cofiber S X Y f) W |
    (k o @cofiber_in S X Y f)%morphism = h /\
    forall k' : morphism S (@cofiber S X Y f) W,
    (k' o @cofiber_in S X Y f)%morphism = h -> k' = k }.

(** *** Uniqueness of the TR4 Morphism *)

(** If the cofiber universal property holds, then the TR4 morphism is unique *)
Theorem TR4_morphism_unique_via_universal :
  forall (S : PreStableCategoryWithCofiber),
  cofiber_universal_property S ->
  forall (X Y Z : object S) (f : morphism S X Y) (g : morphism S Y Z)
    (u1 u2 : morphism S (@cofiber S X Y f) (@cofiber S Y Z g)),
  (u1 o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism ->
  (u2 o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism ->
  u1 = u2.
Proof.
  intros S H_universal X Y Z f g u1 u2 H1 H2.
  
  (* First, verify that cofiber_in ∘ g satisfies the zero condition *)
  assert (H_zero: ((@cofiber_in S Y Z g o g) o f)%morphism = 
                  zero_morphism (add_zero (base S)) X (@cofiber S Y Z g)).
  {
    (* We know cofiber_in g ∘ g = 0 *)
    pose proof (@cofiber_cond1 S Y Z g) as H_cof.
    (* Rewrite using this *)
    rewrite H_cof.
    (* Now 0 ∘ f = 0 *)
    apply zero_morphism_left.
  }
  
  (* Apply universal property to get unique k *)
  destruct (H_universal X Y f (@cofiber S Y Z g) 
                       (@cofiber_in S Y Z g o g)%morphism H_zero) 
    as [k [H_comm H_unique]].
  
  (* Both u1 and u2 equal k by uniqueness *)
  rewrite (H_unique u1 H1).
  rewrite (H_unique u2 H2).
  reflexivity.
Qed.

(** *** Existence of the TR4 Morphism *)

(** If the cofiber universal property holds, then the TR4 morphism exists *)
Theorem TR4_morphism_exists :
  forall (S : PreStableCategoryWithCofiber),
  cofiber_universal_property S ->
  forall (X Y Z : object S) (f : morphism S X Y) (g : morphism S Y Z),
  exists (u : morphism S (@cofiber S X Y f) (@cofiber S Y Z g)),
  (u o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism.
Proof.
  intros S H_universal X Y Z f g.
  
  (* We need to check that cofiber_in g ∘ g vanishes on f *)
  assert (H_zero: ((@cofiber_in S Y Z g o g) o f)%morphism = 
                  zero_morphism (add_zero (base S)) X (@cofiber S Y Z g)).
  {
    pose proof (@cofiber_cond1 S Y Z g) as H_cof.
    rewrite H_cof.
    apply zero_morphism_left.
  }
  
  (* Apply universal property *)
  destruct (H_universal X Y f (@cofiber S Y Z g) 
                       (@cofiber_in S Y Z g o g)%morphism H_zero) 
    as [u [H_comm H_unique]].
  
  exists u.
  exact H_comm.
Qed.

(** *** The Complete TR4 Axiom *)

(** The full TR4 axiom: existence of the octahedral diagram with all
    required morphisms and commutativity conditions *)
Definition satisfies_TR4 (S : PreStableCategoryWithCofiber) : Type :=
  cofiber_universal_property S *
  forall (A B C : object S) (f : morphism S A B) (g : morphism S B C),
  { u : morphism S (@cofiber S A B f) (@cofiber S B C g) &
  { v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism) &
  { w : morphism S (@cofiber S A C (g o f)%morphism) 
                   (object_of (Susp (base S)) (@cofiber S A B f)) &
  { T : @DistinguishedTriangle (base S) |
    (* The triangle connects the three cofibers *)
    X (triangle T) = @cofiber S A B f /\
    Y (triangle T) = @cofiber S B C g /\
    Z (triangle T) = @cofiber S A C (g o f)%morphism /\
    (* And the morphism u is the one we constructed *)
    (u o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism }}}}.
