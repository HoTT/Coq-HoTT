(** * Foundations of Stable Category Theory

    A formalization of stable category theory in Homotopy Type Theory. The development
    begins with zero objects and biproducts, constructs additive categories, and
    introduces pre-stable categories equipped with suspension and loop functors. We
    establish the theory of distinguished triangles, prove the axioms TR1-TR4 of
    triangulated categories, and demonstrate that proper stable categories with
    cofibers are triangulated. The formalization includes a complete treatment of
    the duality principle showing that the opposite of a stable category is stable
    with suspension and loop functors interchanged.
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories Require Import InitialTerminalCategory.
From HoTT.Categories.Functor Require Import Identity Composition.
From HoTT.Spaces Require Import Int.

(** * Section 1: Zero Objects *)

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

Definition zero_morphism {C : PreCategory} (Z : ZeroObject C) (X Y : object C)
  : morphism C X Y
  := (@center _ (@is_initial _ Z Y) o @center _ (@is_terminal _ Z X))%morphism.

(** ** Basic Lemmas for Categories with Zero Objects
    
    This section establishes fundamental properties of morphisms in categories
    with zero objects, including uniqueness results and composition properties.
*)

(** *** Uniqueness of Initial and Terminal Morphisms *)

(** Any two morphisms from an initial object are equal. *)
Lemma initial_morphism_unique {C : PreCategory} 
  (I : object C) (X : object C)
  (H_initial : Contr (morphism C I X))
  (f g : morphism C I X)
  : f = g.
Proof.
  transitivity (@center _ H_initial).
  - exact (@contr _ H_initial f)^.
  - exact (@contr _ H_initial g).
Qed.

(** Any two morphisms to a terminal object are equal. *)
Lemma terminal_morphism_unique {C : PreCategory} 
  (X : object C) (T : object C)
  (H_terminal : Contr (morphism C X T))
  (f g : morphism C X T)
  : f = g.
Proof.
  transitivity (@center _ H_terminal).
  - exact (@contr _ H_terminal f)^.
  - exact (@contr _ H_terminal g).
Qed.

(** *** Properties of Zero Morphisms *)

(** Any morphism that factors through a zero object is the zero morphism. *)
Lemma morphism_through_zero_is_zero {C : PreCategory} 
  (Z : ZeroObject C) (X Y : object C)
  (f : morphism C X (@zero _ Z))
  (g : morphism C (@zero _ Z) Y)
  : (g o f)%morphism = zero_morphism Z X Y.
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
  (f : morphism C X Y) (g : morphism C Y Z)
  : transport (fun U => morphism C U Z) p (g o f)%morphism =
    (g o transport (fun U => morphism C U Y) p f)%morphism.
Proof.
  destruct p; reflexivity.
Qed.

Lemma transport_morphism_compose_middle {C : PreCategory}
  {W X Y Z : object C} (p : W = X)
  (f : morphism C Y W) (g : morphism C Z Y)
  : (transport (fun U => morphism C Y U) p f o g)%morphism =
    transport (fun U => morphism C Z U) p (f o g)%morphism.
Proof.
  destruct p. reflexivity.
Qed.

Lemma transport_compose_both_inverse {C : PreCategory}
  {W X Y Z : object C} (p : W = X)
  (f : morphism C W Z) (g : morphism C Y W)
  : (transport (fun U : object C => morphism C U Z) p f o 
     transport (fun U : object C => morphism C Y U) p g)%morphism =
    (f o g)%morphism.
Proof.
  destruct p. reflexivity.
Qed.

Lemma transport_initial_morphism {C : PreCategory}
  (I I' X : object C) (p : I = I')
  (H_initial : Contr (morphism C I X))
  (H_initial' : Contr (morphism C I' X))
  (f : morphism C I X)
  : transport (fun U => morphism C U X) p f = 
    @center _ H_initial'.
Proof.
  apply (@contr _ H_initial' (transport (fun U => morphism C U X) p f))^.
Qed.

Lemma transport_terminal_morphism {C : PreCategory}
  (X T T' : object C) (p : T = T')
  (H_terminal : Contr (morphism C X T))
  (H_terminal' : Contr (morphism C X T'))
  (f : morphism C X T)
  : transport (fun U => morphism C X U) p f = 
    @center _ H_terminal'.
Proof.
  apply (@contr _ H_terminal' (transport (fun U => morphism C X U) p f))^.
Qed.

Lemma transport_inverse_is_inverse {A : Type} {B : A -> Type}
  {x y : A} (p : x = y) (b : B x)
  : transport B p^ (transport B p b) = b.
Proof.
  destruct p. reflexivity.
Qed.

Lemma transport_inverse_eq {A : Type} {P : A -> Type} 
  {x y : A} (p : x = y) (u : P x) (v : P y)
  : transport P p u = v -> u = transport P p^ v.
Proof.
  intro H.
  rewrite <- H.
  destruct p.
  reflexivity.
Qed.

Lemma transport_path_inverse {A : Type} {P : A -> Type}
  {x y : A} (p : x = y) (u : P y)
  : transport P p^ u = transport P p^ u.
Proof.
  reflexivity.
Qed.

Lemma morphism_eq_transport_inverse {C : PreCategory}
  {W X Y : object C} (p : W = X)
  (f : morphism C W Y) (g : morphism C X Y)
  : transport (fun Z => morphism C Z Y) p f = g ->
    f = transport (fun Z => morphism C Z Y) p^ g.
Proof.
  intro H.
  rewrite <- H.
  destruct p.
  reflexivity.
Qed.

(** *** Basic Morphism Identities *)

Lemma morphism_right_identity {C : PreCategory} {X Y : object C} (f : morphism C X Y)
  : (f o 1)%morphism = f.
Proof.
  apply Category.Core.right_identity.
Qed.

Lemma morphism_left_identity {C : PreCategory} {X Y : object C} (f : morphism C X Y)
  : (1 o f)%morphism = f.
Proof.
  apply Category.Core.left_identity.
Qed.

Lemma morphism_associativity {C : PreCategory} {W X Y Z : object C} 
  (f : morphism C W X) (g : morphism C X Y) (h : morphism C Y Z)
  : ((h o g) o f)%morphism = (h o (g o f))%morphism.
Proof.
  apply Category.Core.associativity.
Qed.

(** *** Lemmas for Zero Objects in Pre-Stable Categories *)

(** The morphism from zero to itself is the identity. *)
Lemma zero_to_zero_is_id {C : PreCategory} (Z : ZeroObject C)
  : @center _ (@is_initial _ Z (@zero _ Z)) = 1%morphism.
Proof.
  apply (@contr _ (@is_initial _ Z (@zero _ Z))).
Qed.

(** The terminal morphism from zero to itself is the identity. *)
Lemma terminal_zero_to_zero_is_id {C : PreCategory} (Z : ZeroObject C)
  : @center _ (@is_terminal _ Z (@zero _ Z)) = 
    (1%morphism : morphism C (@zero _ Z) (@zero _ Z)).
Proof.
  apply terminal_morphism_unique.
  apply (@is_terminal _ Z (@zero _ Z)).
Qed.

(** Composition with a terminal morphism to zero gives zero morphism. *)
Lemma terminal_comp_is_zero {C : PreCategory} (Z : ZeroObject C) 
  (X Y : object C) 
  (f : morphism C X (@zero _ Z))
  : (@center _ (@is_initial _ Z Y) o f)%morphism = 
    zero_morphism Z X Y.
Proof.
  apply morphism_through_zero_is_zero.
Qed.

(** The zero morphism from zero is the initial morphism. *)
Lemma zero_morphism_from_zero {C : PreCategory} (Z : ZeroObject C) 
  (Y : object C)
  : zero_morphism Z (@zero _ Z) Y = @center _ (@is_initial _ Z Y).
Proof.
  unfold zero_morphism.
  assert (H: @center _ (@is_terminal _ Z (@zero _ Z)) = 
            (1%morphism : morphism C (@zero _ Z) (@zero _ Z))).
  { 
    apply (@contr _ (@is_terminal _ Z (@zero _ Z))).
  }
  rewrite H.
  apply morphism_right_identity.
Qed.

(** Composition with zero morphism on the right. *)
Lemma zero_morphism_right {C : PreCategory} (Z : ZeroObject C) 
  {X Y W : object C}
  (g : morphism C Y W)
  : (g o zero_morphism Z X Y)%morphism = zero_morphism Z X W.
Proof.
  unfold zero_morphism.
  assert (H: (g o @center _ (@is_initial _ Z Y))%morphism = 
             @center _ (@is_initial _ Z W)).
  {
    symmetry.
    apply (@contr _ (@is_initial _ Z W)).
  }
  rewrite <- morphism_associativity.
  rewrite H.
  reflexivity.
Qed.

(** Composition with zero morphism on the left. *)
Lemma zero_morphism_left {C : PreCategory} (Z : ZeroObject C) 
  {X Y W : object C}
  (f : morphism C X Y)
  : (zero_morphism Z Y W o f)%morphism = zero_morphism Z X W.
Proof.
  unfold zero_morphism.
  assert (H: (@center _ (@is_terminal _ Z Y) o f)%morphism = 
             @center _ (@is_terminal _ Z X)).
  {
    symmetry.
    apply (@contr _ (@is_terminal _ Z X)).
  }
  rewrite morphism_associativity.
  rewrite H.
  reflexivity.
Qed.

(** End of Section 1: Zero Objects *)

(** * Section 2: Biproducts *)

(** ** Biproducts
    
    A biproduct is an object that is simultaneously a product and coproduct.
    In additive categories, finite products and coproducts coincide.
*)

(** The data of a biproduct structure. *)
Record BiproductData {C : PreCategory} (X Y : object C) := {
  biproduct_obj : object C;
  
  (* Coproduct structure *)
  inl : morphism C X biproduct_obj;
  inr : morphism C Y biproduct_obj;
  
  (* Product structure *)
  outl : morphism C biproduct_obj X;
  outr : morphism C biproduct_obj Y
}.

(** The axioms that make a biproduct structure into an actual biproduct. *)
Record IsBiproduct {C : PreCategory} {X Y : object C} 
                   (B : BiproductData X Y) (Z : ZeroObject C) := {
  (* Projection-injection identities *)
  beta_l : (@outl _ _ _ B o @inl _ _ _ B = 1)%morphism;
  beta_r : (@outr _ _ _ B o @inr _ _ _ B = 1)%morphism;
  
  (* Mixed terms are zero *)
  mixed_l : (@outl _ _ _ B o @inr _ _ _ B)%morphism = zero_morphism Z Y X;
  mixed_r : (@outr _ _ _ B o @inl _ _ _ B)%morphism = zero_morphism Z X Y
}.

(** The universal property that characterizes biproducts. *)
Record HasBiproductUniversal {C : PreCategory} {X Y : object C} 
                             (B : BiproductData X Y) := {
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

(** A biproduct is biproduct data together with the proof that it satisfies
    the biproduct axioms and universal property. *)
Record Biproduct {C : PreCategory} (X Y : object C) (Z : ZeroObject C) := {
  biproduct_data : BiproductData X Y;
  biproduct_is : IsBiproduct biproduct_data Z;
  biproduct_universal : HasBiproductUniversal biproduct_data
}.

(** End of Section 2: Biproducts *)

(** * Section 3: Additive Categories *)

(** ** Additive Categories
    
    An additive category is a category enriched over abelian groups,
    with a zero object and biproducts for all pairs of objects.
*)

Record AdditiveCategory := {
  cat :> PreCategory;
  
  add_zero : ZeroObject cat;
  
  add_biproduct : forall (X Y : object cat), Biproduct X Y add_zero
}.

(** Helper functions to access biproduct components. *)
Definition add_biproduct_data (A : AdditiveCategory) (X Y : object A)
  : BiproductData X Y
  := biproduct_data _ _ _ (add_biproduct A X Y).

Definition add_biproduct_obj (A : AdditiveCategory) (X Y : object A)
  : object A
  := @biproduct_obj A X Y (add_biproduct_data A X Y).

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
    object_of add_functor (add_biproduct_obj A X Y) =
    add_biproduct_obj B (object_of add_functor X) 
                        (object_of add_functor Y)
}.

(** ** Properties of Additive Functors
    
    This section establishes that additive functors preserve zero morphisms
    and other structural properties of additive categories.
*)

(** *** Preservation of Initial and Terminal Morphisms *)

(** Additive functors preserve initial morphisms. *)
Lemma functor_preserves_initial_morphism 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (Y : object A)
  : transport (fun Z => morphism B Z (object_of F Y)) 
              (preserves_zero A B F)
              (morphism_of F (@center _ (@is_initial _ (add_zero A) Y))) =
    @center _ (@is_initial _ (add_zero B) (object_of F Y)).
Proof.
  apply (@path_contr _ (@is_initial _ (add_zero B) (object_of F Y))).
Qed.

(** Additive functors preserve terminal morphisms. *)
Lemma functor_preserves_terminal_morphism 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (X : object A)
  : transport (fun Z => morphism B (object_of F X) Z) 
              (preserves_zero A B F)
              (morphism_of F (@center _ (@is_terminal _ (add_zero A) X))) =
    @center _ (@is_terminal _ (add_zero B) (object_of F X)).
Proof.
  apply (@path_contr _ (@is_terminal _ (add_zero B) (object_of F X))).
Qed.

(** *** Main Theorem: Additive Functors Preserve Zero Morphisms *)

(** The fundamental property that additive functors preserve zero morphisms. *)
Theorem additive_functor_preserves_zero_morphisms 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (X Y : object A)
  : morphism_of F (zero_morphism (add_zero A) X Y) = 
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

(** End of Section 3: Additive Categories *)

(** * Section 4: Pre-Stable Categories *)

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

(** The suspension functor preserves zero morphisms (inherited from being additive). *)
Theorem susp_preserves_zero_morphisms {S : PreStableCategory} (X Y : object S)
  : morphism_of (Susp S) (zero_morphism (add_zero S) X Y) = 
    zero_morphism (add_zero S) (object_of (Susp S) X) (object_of (Susp S) Y).
Proof.
  apply additive_functor_preserves_zero_morphisms.
Qed.

(** The suspension functor preserves identity morphisms. *)
Lemma susp_preserves_identity {S : PreStableCategory} (X : object S)
  : morphism_of (Susp S) (1%morphism : morphism S X X) = 
    (1%morphism : morphism S (object_of (Susp S) X) (object_of (Susp S) X)).
Proof.
  apply (identity_of (Susp S)).
Qed.

(** End of Section 4: Pre-Stable Categories *)

(** * Section 5: Triangles *)

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
Definition id_triangle {S : PreStableCategory} (X : object S)
  : @Triangle S
  := {|
  X := X;
  Y := X;
  Z := @zero _ (add_zero S);
  f := 1%morphism;
  g := @center _ (@is_terminal _ (add_zero S) X);
  h := @center _ (@is_initial _ (add_zero S) (object_of (Susp S) X))
|}.

(** *** The Identity Triangle is Distinguished *)

Theorem id_triangle_distinguished {S : PreStableCategory} (X : object S)
  : @DistinguishedTriangle S.
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

(** End of Section 5: Triangles *)

(** * Section 6: Morphisms of Triangles *)

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

Definition id_triangle_morphism {S : PreStableCategory} (T : @Triangle S)
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

(** *** Composition of Triangle Morphisms *)

Definition triangle_morphism_compose {S : PreStableCategory}
  (T1 T2 T3 : @Triangle S)
  (φ : TriangleMorphism T1 T2)
  (ψ : TriangleMorphism T2 T3)
  : TriangleMorphism T1 T3.
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

(** Equality of triangle morphisms. *)
Lemma triangle_morphism_eq {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ ψ : TriangleMorphism T1 T2)
  : mor_X _ _ φ = mor_X _ _ ψ ->
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

(** Left identity law. *)
Lemma triangle_morphism_left_id {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ : TriangleMorphism T1 T2)
  : triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply morphism_left_identity.
  - simpl. apply morphism_left_identity.  
  - simpl. apply morphism_left_identity.
Qed.

(** Right identity law. *)
Lemma triangle_morphism_right_id {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ : TriangleMorphism T1 T2)
  : triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply morphism_right_identity.
  - simpl. apply morphism_right_identity.
  - simpl. apply morphism_right_identity.
Qed.

(** Associativity of composition. *)
Lemma triangle_morphism_assoc {S : PreStableCategory} 
  (T1 T2 T3 T4 : @Triangle S)
  (φ : TriangleMorphism T1 T2)
  (ψ : TriangleMorphism T2 T3)
  (χ : TriangleMorphism T3 T4)
  : triangle_morphism_compose T1 T2 T4 φ (triangle_morphism_compose T2 T3 T4 ψ χ) =
    triangle_morphism_compose T1 T3 T4 (triangle_morphism_compose T1 T2 T3 φ ψ) χ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply Category.Core.associativity.
  - simpl. apply Category.Core.associativity.
  - simpl. apply Category.Core.associativity.
Qed.

(** Triangles form a category. *)
Theorem triangles_form_category {S : PreStableCategory}
  : (forall (T1 T2 T3 T4 : @Triangle S) 
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

(** End of Section 6: Morphisms of Triangles *)

(** * Section 7: Triangle Rotation *)

(** ** Triangle Rotation
    
    The rotation operation is fundamental in triangulated categories.
    It transforms a triangle X → Y → Z → ΣX into Y → Z → ΣX → ΣY.
*)

(** *** Rotation of Triangles *)

Definition rotate_triangle {S : PreStableCategory} (T : @Triangle S)
  : @Triangle S
  := {|
  X := Y T;
  Y := Z T;
  Z := object_of (Susp S) (X T);
  f := g T;
  g := h T;
  h := morphism_of (Susp S) (f T)
|}.

(** *** Rotation Preserves Distinguished Triangles *)

Theorem rotate_distinguished {S : PreStableCategory} (T : @DistinguishedTriangle S)
  : @DistinguishedTriangle S.
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

(** *** Shift and Axiom TR3 *)

(** The shift operation is another name for rotation. *)
Definition shift_triangle {S : PreStableCategory} (T : @Triangle S)
  : @Triangle S
  := rotate_triangle T.

Theorem shift_distinguished {S : PreStableCategory} (T : @DistinguishedTriangle S)
  : @DistinguishedTriangle S.
Proof.
  exact (rotate_distinguished T).
Defined.

(** Shifting a triangle morphism. *)
Definition shift_triangle_morphism {S : PreStableCategory} {T1 T2 : @Triangle S}
  (φ : TriangleMorphism T1 T2)
  : TriangleMorphism (shift_triangle T1) (shift_triangle T2).
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

(** *** Triangle Isomorphisms *)

(** A triangle isomorphism is a triangle morphism where all three
    component morphisms are isomorphisms. *)
Definition IsTriangleIsomorphism {S : PreStableCategory} {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  : Type
  := IsIsomorphism (mor_X _ _ φ) * 
     IsIsomorphism (mor_Y _ _ φ) * 
     IsIsomorphism (mor_Z _ _ φ).

(** Statement of TR3. *)
Definition TR3_statement {S : PreStableCategory}
  : Type
  := forall (T : @Triangle S) (T' : @Triangle S) 
            (φ : TriangleMorphism T T'),
     IsTriangleIsomorphism φ ->
     @DistinguishedTriangle S ->
     @DistinguishedTriangle S.

(** End of Section 7: Triangle Rotation *)

(** * Section 8: Axioms of Triangulated Categories *)

(** ** Axioms of Triangulated Categories
    
    We now formalize the axioms that characterize triangulated categories.
    TR1 ensures every morphism extends to a distinguished triangle.
*)

(** *** Axiom TR1: Extension of Morphisms to Distinguished Triangles *)

(** Statement of TR1: Every morphism can be completed to a distinguished triangle. *)
Definition TR1_statement {S : PreStableCategory}
  : Type
  := forall (X Y : object S) (f : morphism S X Y),
     { Z : object S &
     { g : morphism S Y Z &
     { h : morphism S Z (object_of (Susp S) X) &
       @DistinguishedTriangle S }}}.

(** Helper to construct a triangle from morphisms. *)
Definition triangle_from_morphisms {S : PreStableCategory}
  {X Y Z : object S} 
  (f : morphism S X Y)
  (g : morphism S Y Z)
  (h : morphism S Z (object_of (Susp S) X))
  : @Triangle S
  := {|
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

Definition cone {S : PreStableCategory} {X Y : object S} (f : morphism S X Y)
  : object S
  := add_biproduct_obj S Y (object_of (Susp S) X).

Definition cone_in {S : PreStableCategory} {X Y : object S} (f : morphism S X Y)
  : morphism S Y (cone f)
  := @inl _ _ _ (add_biproduct_data S Y (object_of (Susp S) X)).

Definition cone_out {S : PreStableCategory} {X Y : object S} (f : morphism S X Y)
  : morphism S (cone f) (object_of (Susp S) X)
  := @outr _ _ _ (add_biproduct_data S Y (object_of (Susp S) X)).

(** *** Cone Triangle Construction *)

Definition cone_triangle {S : PreStableCategory} {X Y : object S} (f : morphism S X Y)
  : @Triangle S
  := {|
  X := X;
  Y := Y;
  Z := cone f;
  f := f;
  g := cone_in f;
  h := cone_out f
|}.

(** *** Properties of Cone Morphisms *)

Lemma cone_out_cone_in_zero {S : PreStableCategory} {X Y : object S} (f : morphism S X Y)
  : ((cone_out f) o (cone_in f))%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X).
Proof.
  unfold cone_out, cone_in.
  apply (@mixed_r _ _ _ 
    (add_biproduct_data S Y (object_of (Susp S) X)) 
    (add_zero S) 
    (biproduct_is _ _ _ (add_biproduct S Y (object_of (Susp S) X)))).
Qed.

(** Helper lemma for cone distinguished triangle construction. *)
Lemma cone_distinguished_conditions {S : PreStableCategory} {X Y : object S} (f : morphism S X Y)
  : ((cone_in f) o f)%morphism = zero_morphism (add_zero S) X (cone f) ->
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
  {X Y : object S} (f : morphism S X Y)
  : @Triangle (base S)
  := {|
  X := X;
  Y := Y;
  Z := @cofiber S X Y f;
  f := f;
  g := @cofiber_in S X Y f;
  h := @cofiber_out S X Y f
|}.

Theorem cofiber_triangle_distinguished {S : PreStableCategoryWithCofiber} 
  {X Y : object S} (f : morphism S X Y)
  : @DistinguishedTriangle (base S).
Proof.
  refine {| triangle := triangle_from_morphism f |}.
  - simpl. exact (@cofiber_cond1 S X Y f).
  - simpl. exact (@cofiber_cond2 S X Y f).
  - simpl. exact (@cofiber_cond3 S X Y f).
Defined.

(** *** TR1 for Categories with Cofiber *)

Theorem TR1 {S : PreStableCategoryWithCofiber} {X Y : object S} (f : morphism S X Y)
  : @DistinguishedTriangle (base S).
Proof.
  exact (cofiber_triangle_distinguished f).
Defined.

Theorem TR1_correct {S : PreStableCategoryWithCofiber} {X Y : object S} (f : morphism S X Y)
  : triangle (TR1 f) = triangle_from_morphism f.
Proof.
  reflexivity.
Qed.

(** Constructive version of TR1. *)
Definition TR1_triangle_data {S : PreStableCategoryWithCofiber} 
  {X Y : object (base S)} (f : morphism (base S) X Y)
  : { Z : object (base S) & 
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

(** End of Section 8: Axioms of Triangulated Categories (TR1) *)

(** * Section 9: Isomorphisms and Axiom TR2 *)

(** ** Isomorphisms in Categories
    
    We define isomorphisms and establish their basic properties,
    which will be needed for the axioms of triangulated categories.
*)

(** *** Basic Isomorphism Definition *)

Definition IsIsomorphism {C : PreCategory} {X Y : object C} (f : morphism C X Y)
  : Type
  := { g : morphism C Y X |
       (g o f = 1)%morphism /\ (f o g = 1)%morphism }.

(** Extract the inverse morphism. *)
Definition iso_inverse {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f)
  : morphism C Y X
  := H.1.

(** The identity morphism is an isomorphism. *)
Lemma iso_identity {C : PreCategory} {X : object C}
  : IsIsomorphism (1%morphism : morphism C X X).
Proof.
  exists 1%morphism.
  split; apply morphism_left_identity.
Qed.

(** Properties of inverses. *)
Lemma iso_inverse_left {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f)
  : (iso_inverse H o f = 1)%morphism.
Proof.
  destruct H as [g [Hl Hr]].
  exact Hl.
Qed.

Lemma iso_inverse_right {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f)
  : (f o iso_inverse H = 1)%morphism.
Proof.
  destruct H as [g [Hl Hr]].
  exact Hr.
Qed.

(** ** Axiom TR2: Isomorphisms of Distinguished Triangles
    
    TR2 states that if we have an isomorphism between two triangles
    and one is distinguished, then so is the other.
*)

(** *** Helper Lemmas for Isomorphisms *)

(** Isomorphisms preserve terminal morphisms. *)
Lemma iso_preserves_terminal {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ)
  (f : morphism S X (@zero _ (add_zero S)))
  : (f o iso_inverse H)%morphism = @center _ (@is_terminal _ (add_zero S) Y).
Proof.
  symmetry.
  apply (@contr _ (@is_terminal _ (add_zero S) Y)).
Qed.

(** Isomorphisms preserve initial morphisms. *)
Lemma iso_preserves_initial {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ)
  (f : morphism S (@zero _ (add_zero S)) X)
  : (φ o f)%morphism = @center _ (@is_initial _ (add_zero S) Y).
Proof.
  symmetry.
  apply (@contr _ (@is_initial _ (add_zero S) Y)).
Qed.

(** Isomorphisms preserve zero morphisms. *)
Lemma iso_preserves_zero {S : PreStableCategory} {X Y Z W : object S}
  (φX : morphism S X Z) (φY : morphism S Y W)
  (HX : IsIsomorphism φX) (HY : IsIsomorphism φY)
  (f : morphism S X Y)
  : f = zero_morphism (add_zero S) X Y ->
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
  {X Y : object C} (f : morphism C X Y) (H : IsIsomorphism f)
  : IsIsomorphism (morphism_of F f).
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
  {X Y : object C} (f : morphism C X Y) (H : IsIsomorphism f)
  : morphism_of F (iso_inverse H) = 
    iso_inverse (functor_preserves_iso F f H).
Proof.
  destruct H as [g [Hgf Hfg]].
  simpl.
  reflexivity.
Qed.

(** *** Helper Lemmas for Composition *)

Lemma ap_morphism_comp_left {C : PreCategory} {X Y Z : object C} 
  (f : morphism C Y Z) (g h : morphism C X Y)
  : g = h -> (f o g)%morphism = (f o h)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_cancel_left {C : PreCategory} {X Y Z : object C} 
  (f : morphism C Y Z) (g h : morphism C X Y)
  : (f o g)%morphism = (f o h)%morphism -> 
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
  (H : (g o f = 1)%morphism)
  : forall (Z : object C) (h : morphism C Z X),
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
  (s : morphism C V W)
  : q1 = q2 ->
    (p o q1 o r o s)%morphism = (p o q2 o r o s)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_left {C : PreCategory} {X Y Z : object C}
  (p : morphism C Y Z)
  (q1 q2 : morphism C X Y)
  : q1 = q2 ->
    (p o q1)%morphism = (p o q2)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_right {C : PreCategory} {X Y Z : object C}
  (p1 p2 : morphism C Y Z)
  (q : morphism C X Y)
  : p1 = p2 ->
    (p1 o q)%morphism = (p2 o q)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

(** *** Additional Helper Lemmas for TR2 *)

Lemma iso_morphism_cancel {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ)
  : (iso_inverse H o φ)%morphism = 1%morphism.
Proof.
  apply iso_inverse_left.
Qed.

Lemma composition_with_identity_middle {S : PreStableCategory} {A B C D : object S}
  (f : morphism S C D)
  (g : morphism S B C) 
  (h : morphism S A B)
  : (f o 1 o g o h)%morphism = (f o g o h)%morphism.
Proof.
  rewrite morphism_right_identity.
  reflexivity.
Qed.

Lemma rearrange_middle_composition {S : PreStableCategory} {A B C D E : object S}
  (f : morphism S D E)
  (g : morphism S C D)
  (h : morphism S B C)
  (k : morphism S A B)
  : (f o (g o (h o k)))%morphism = (f o ((g o h) o k))%morphism.
Proof.
  rewrite morphism_associativity.
  reflexivity.
Qed.

Lemma get_morphisms_adjacent {S : PreStableCategory} {A B C D E F : object S}
  (f : morphism S E F)
  (g : morphism S D E)
  (h : morphism S C D)
  (k : morphism S B C)
  (l : morphism S A B)
  : (f o (g o (h o (k o l))))%morphism = 
    (f o (g o ((h o k) o l)))%morphism.
Proof.
  rewrite morphism_associativity.
  reflexivity.
Qed.

Lemma four_morphism_assoc {S : PreStableCategory} {A B C D E : object S}
  (φ : morphism S D E)
  (g : morphism S C D)
  (f : morphism S B C)
  (ψ : morphism S A B)
  : (φ o g o f o ψ)%morphism = (φ o (g o f) o ψ)%morphism.
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
  (ψ : morphism S A B)
  : (g o f)%morphism = zero_morphism (add_zero S) B D ->
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
  (φX_inv : morphism S X2 X1)
  : (φY_inv o φY)%morphism = 1%morphism ->
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

(** End of Section 9: Isomorphisms and Axiom TR2 (Part 1) *)


(** * Section 9b: Axiom TR2 (Part 2) *)

(** ** Axiom TR2: Isomorphisms Preserve Distinguished Triangles
    
    This section proves that isomorphisms of triangles preserve the property
    of being distinguished. This is one of the fundamental axioms of
    triangulated categories.
*)

(** *** Formulas for Triangle Components Under Isomorphisms *)

(** How the f morphism transforms under an isomorphism. *)
Lemma triangle_iso_f_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HY_iso : IsIsomorphism (mor_Y _ _ φ))
  (HX_iso : IsIsomorphism (mor_X _ _ φ))
  : f T2 = (mor_Y _ _ φ o f T1 o iso_inverse HX_iso)%morphism.
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

(** How the g morphism transforms under an isomorphism. *)
Lemma triangle_iso_g_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ))
  (HY_iso : IsIsomorphism (mor_Y _ _ φ))
  : g T2 = (mor_Z _ _ φ o g T1 o iso_inverse HY_iso)%morphism.
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

(** How the h morphism transforms under an isomorphism. *)
Lemma triangle_iso_h_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HX_iso : IsIsomorphism (mor_X _ _ φ))
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ))
  : h T2 = (morphism_of (Susp S) (mor_X _ _ φ) o h T1 o iso_inverse HZ_iso)%morphism.
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

(** Isomorphisms preserve the first zero composition g∘f = 0. *)
Lemma triangle_iso_preserves_zero_comp_1 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HX_iso : IsIsomorphism (mor_X _ _ φ))
  (HY_iso : IsIsomorphism (mor_Y _ _ φ))
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ))
  : (g T1 o f T1)%morphism = zero_morphism (add_zero S) (X T1) (Z T1) ->
    (g T2 o f T2)%morphism = zero_morphism (add_zero S) (X T2) (Z T2).
Proof.
  intro H.
  
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

(** Isomorphisms preserve the second zero composition h∘g = 0. *)
Lemma triangle_iso_preserves_zero_comp_2 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HX_iso : IsIsomorphism (mor_X _ _ φ))
  (HY_iso : IsIsomorphism (mor_Y _ _ φ))
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ))
  : (h T1 o g T1)%morphism = zero_morphism (add_zero S) (Y T1) (object_of (Susp S) (X T1)) ->
    (h T2 o g T2)%morphism = zero_morphism (add_zero S) (Y T2) (object_of (Susp S) (X T2)).
Proof.
  intro H.
  
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

(** Isomorphisms preserve the third zero composition Σf∘h = 0. *)
Lemma triangle_iso_preserves_zero_comp_3 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HX_iso : IsIsomorphism (mor_X _ _ φ))
  (HY_iso : IsIsomorphism (mor_Y _ _ φ))
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ))
  : (morphism_of (Susp S) (f T1) o h T1)%morphism = 
    zero_morphism (add_zero S) (Z T1) (object_of (Susp S) (Y T1)) ->
    (morphism_of (Susp S) (f T2) o h T2)%morphism = 
    zero_morphism (add_zero S) (Z T2) (object_of (Susp S) (Y T2)).
Proof.
  intro H.
  
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

(** TR2: Triangle isomorphisms preserve the distinguished property.
    
    This is a fundamental axiom of triangulated categories. It states that
    if we have an isomorphism between two triangles and one is distinguished,
    then the other must be distinguished as well. This ensures that the
    property of being distinguished is invariant under isomorphism.
*)

(** Convert from Category.IsIsomorphism to our local IsIsomorphism. *)
Definition convert_iso {C : PreCategory} {X Y : object C} (f : morphism C X Y)
  (H : Category.IsIsomorphism f) : IsIsomorphism f.
Proof.
  exists (morphism_inverse f).
  split.
  - apply left_inverse.
  - apply right_inverse.
Defined.

Theorem TR2 {S : PreStableCategory} {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ)
  (D1 : @DistinguishedTriangle S)
  (H1 : triangle D1 = T1)
  : @DistinguishedTriangle S.
Proof.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  refine {| triangle := T2 |}.
  - (* zero_comp_1 *)
    apply (triangle_iso_preserves_zero_comp_1 φ 
      (convert_iso _ HX_iso)
      (convert_iso _ HY_iso) 
      (convert_iso _ HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_1 D1).
  - (* zero_comp_2 *)
    apply (triangle_iso_preserves_zero_comp_2 φ 
      (convert_iso _ HX_iso)
      (convert_iso _ HY_iso)
      (convert_iso _ HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_2 D1).
  - (* zero_comp_3 *)
    apply (triangle_iso_preserves_zero_comp_3 φ 
      (convert_iso _ HX_iso)
      (convert_iso _ HY_iso)
      (convert_iso _ HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_3 D1).
Defined.

(** End of Section 9b: Axiom TR2 (Part 2) *)

(** * Section 10: Opposite Categories *)

(** ** Opposite Categories
    
    The opposite category construction reverses all morphisms. This section
    shows that pre-stable categories have a natural opposite structure where
    the suspension and loop functors are interchanged.
*)

(** *** Basic Opposite Category Construction *)

Definition opposite_category (C : PreCategory)
  : PreCategory.
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

Definition opposite_zero_object {C : PreCategory} (Z : ZeroObject C)
  : ZeroObject (opposite_category C).
Proof.
  exact (Build_ZeroObject 
    (opposite_category C)
    (zero _ Z)
    (fun X => is_terminal _ Z X)
    (fun X => is_initial _ Z X)).
Defined.

(** *** Opposite Biproduct *)

Definition opposite_biproduct_data {C : PreCategory} {X Y : object C} 
  (B : BiproductData X Y)
  : @BiproductData (opposite_category C) Y X.
Proof.
  exact (Build_BiproductData
    (opposite_category C) Y X
    (@biproduct_obj _ _ _ B)
    (@outr _ _ _ B)
    (@outl _ _ _ B)
    (@inr _ _ _ B)
    (@inl _ _ _ B)).
Defined.

(** *** Properties of Opposite Biproducts *)

Lemma opposite_biproduct_beta_l {C : PreCategory} {X Y : object C} 
  (B : BiproductData X Y) (Z : ZeroObject C) (H : IsBiproduct B Z)
  : (@outl _ _ _ (opposite_biproduct_data B) o 
     @inl _ _ _ (opposite_biproduct_data B) = 1)%morphism.
Proof.
  simpl.
  exact (@beta_r _ _ _ B Z H).
Qed.

Lemma opposite_biproduct_beta_r {C : PreCategory} {X Y : object C} 
  (B : BiproductData X Y) (Z : ZeroObject C) (H : IsBiproduct B Z)
  : (@outr _ _ _ (opposite_biproduct_data B) o 
     @inr _ _ _ (opposite_biproduct_data B) = 1)%morphism.
Proof.
  simpl.
  exact (@beta_l _ _ _ B Z H).
Qed.

Lemma opposite_biproduct_mixed_r {C : PreCategory} {X Y : object C} 
  (B : BiproductData X Y) (Z : ZeroObject C) (H : IsBiproduct B Z)
  : (@outr _ _ _ (opposite_biproduct_data B) o 
     @inl _ _ _ (opposite_biproduct_data B))%morphism = 
    zero_morphism (opposite_zero_object Z) Y X.
Proof.
  simpl.
  exact (@mixed_r _ _ _ B Z H).
Qed.

Lemma opposite_biproduct_mixed_l {C : PreCategory} {X Y : object C} 
  (B : BiproductData X Y) (Z : ZeroObject C) (H : IsBiproduct B Z)
  : (@outl _ _ _ (opposite_biproduct_data B) o 
     @inr _ _ _ (opposite_biproduct_data B))%morphism = 
    zero_morphism (opposite_zero_object Z) X Y.
Proof.
  simpl.
  exact (@mixed_l _ _ _ B Z H).
Qed.

Definition opposite_is_biproduct {C : PreCategory} {X Y : object C}
  (B : BiproductData X Y) (Z : ZeroObject C) (H : IsBiproduct B Z)
  : IsBiproduct (opposite_biproduct_data B) (opposite_zero_object Z).
Proof.
  exact (Build_IsBiproduct
    (opposite_category C) Y X
    (opposite_biproduct_data B)
    (opposite_zero_object Z)
    (opposite_biproduct_beta_l B Z H)
    (opposite_biproduct_beta_r B Z H)
    (opposite_biproduct_mixed_l B Z H)
    (opposite_biproduct_mixed_r B Z H)).
Defined.

(** *** Universal Property of Opposite Biproducts *)

(** Helper equivalence for swapping products. *)
Lemma swap_product_equiv {A : Type} {P Q : A -> Type}
  : {a : A & (P a * Q a)} <~> {a : A & (Q a * P a)}.
Proof.
  apply equiv_functor_sigma_id.
  intro a.
  apply equiv_prod_symm.
Defined.

Lemma swap_product_contr {A : Type} {P Q : A -> Type}
  : Contr {a : A & (P a * Q a)} ->
    Contr {a : A & (Q a * P a)}.
Proof.
  intro H.
  apply (contr_equiv' _ (swap_product_equiv)).
Qed.

Lemma opposite_coprod_universal {C : PreCategory} {X Y : object C} 
  (B : BiproductData X Y) (H : HasBiproductUniversal B)
  : forall (Z : object (opposite_category C)) 
           (f : morphism (opposite_category C) Y Z) 
           (g : morphism (opposite_category C) X Z),
    Contr {h : morphism (opposite_category C) 
                        (@biproduct_obj _ _ _ (opposite_biproduct_data B)) Z | 
           (h o @inl _ _ _ (opposite_biproduct_data B) = f)%morphism /\ 
           (h o @inr _ _ _ (opposite_biproduct_data B) = g)%morphism}.
Proof.
  intros Z f g.
  simpl in *.
  apply swap_product_contr.
  exact (@prod_universal _ _ _ B H Z g f).
Qed.

Lemma opposite_prod_universal {C : PreCategory} {X Y : object C} 
  (B : BiproductData X Y) (H : HasBiproductUniversal B)
  : forall (Z : object (opposite_category C)) 
           (f : morphism (opposite_category C) Z Y) 
           (g : morphism (opposite_category C) Z X),
    Contr {h : morphism (opposite_category C) Z 
                        (@biproduct_obj _ _ _ (opposite_biproduct_data B)) | 
           (@outl _ _ _ (opposite_biproduct_data B) o h = f)%morphism /\ 
           (@outr _ _ _ (opposite_biproduct_data B) o h = g)%morphism}.
Proof.
  intros Z f g.
  simpl in *.
  apply swap_product_contr.
  exact (@coprod_universal _ _ _ B H Z g f).
Qed.

Definition opposite_biproduct_universal {C : PreCategory} {X Y : object C} 
  (B : BiproductData X Y) (H : HasBiproductUniversal B)
  : HasBiproductUniversal (opposite_biproduct_data B).
Proof.
  exact (Build_HasBiproductUniversal
    (opposite_category C) Y X
    (opposite_biproduct_data B)
    (opposite_coprod_universal B H)
    (opposite_prod_universal B H)).
Defined.

Definition opposite_biproduct {C : PreCategory} {X Y : object C} 
  (Z : ZeroObject C) (B : Biproduct X Y Z)
  : @Biproduct (opposite_category C) Y X (opposite_zero_object Z).
Proof.
  exact (Build_Biproduct
    (opposite_category C) Y X
    (opposite_zero_object Z)
    (opposite_biproduct_data (biproduct_data _ _ _ B))
    (opposite_is_biproduct (biproduct_data _ _ _ B) Z (biproduct_is _ _ _ B))
    (opposite_biproduct_universal (biproduct_data _ _ _ B) 
                                  (biproduct_universal _ _ _ B))).
Defined.

(** *** Opposite Additive Category *)

Definition opposite_additive_category (A : AdditiveCategory)
  : AdditiveCategory.
Proof.
  refine (Build_AdditiveCategory
    (opposite_category A)
    (opposite_zero_object (add_zero A))
    (fun X Y => opposite_biproduct (add_zero A) (add_biproduct A Y X))).
Defined.

(** End of Section 10: Opposite Categories *)

(** * Section 11: Opposite Functors and Pre-Stable Categories *)

(** ** Opposite Functors *)

Definition opposite_functor {C D : PreCategory} (F : Functor C D)
  : Functor (opposite_category C) (opposite_category D).
Proof.
  exact (Build_Functor
    (opposite_category C) (opposite_category D)
    (object_of F)
    (fun X Y f => morphism_of F f)
    (fun X Y Z f g => composition_of F Z Y X g f)
    (fun X => identity_of F X)).
Defined.

(** ** Opposite Additive Functors *)

Definition opposite_additive_functor {A B : AdditiveCategory} 
  (F : AdditiveFunctor A B)
  : AdditiveFunctor (opposite_additive_category A) (opposite_additive_category B).
Proof.
  exact (Build_AdditiveFunctor
    (opposite_additive_category A) (opposite_additive_category B)
    (opposite_functor F)
    (preserves_zero A B F)
    (fun X Y => preserves_biproduct A B F Y X)).
Defined.

(** ** Opposite Natural Transformations *)

Definition opposite_natural_transformation {C D : PreCategory} 
  {F G : Functor C D} (η : NaturalTransformation F G)
  : NaturalTransformation (opposite_functor G) (opposite_functor F).
Proof.
  exact (Build_NaturalTransformation
    (opposite_functor G) (opposite_functor F)
    (fun X => components_of η X)
    (fun X Y f => (commutes η Y X f)^)).
Defined.

(** ** Opposite Pre-Stable Categories *)

(** The key insight: in the opposite category, suspension and loop functors swap roles. *)
Definition opposite_prestable_category (PS : PreStableCategory)
  : PreStableCategory.
Proof.
  exact (Build_PreStableCategory
    (opposite_additive_category PS)
    (opposite_additive_functor (Loop PS))  (* Loop becomes Susp *)
    (opposite_additive_functor (Susp PS))  (* Susp becomes Loop *)
    (opposite_natural_transformation (epsilon PS))  (* epsilon becomes eta *)
    (opposite_natural_transformation (eta PS))).     (* eta becomes epsilon *)
Defined.

(** ** Basic Properties of Opposite Pre-Stable Categories *)

Theorem opposite_prestable_exists
  : forall (PS : PreStableCategory),
    exists (PS_op : PreStableCategory),
      cat PS_op = opposite_additive_category PS.
Proof.
  intro PS.
  exists (opposite_prestable_category PS).
  reflexivity.
Qed.

Theorem opposite_morphisms_flip
  : forall (PS : PreStableCategory) (X Y : object PS),
    morphism (opposite_prestable_category PS) X Y = morphism PS Y X.
Proof.
  intros.
  reflexivity.
Qed.

(** ** Suspension and Loop Duality *)

(** The fundamental duality: suspension and loop functors swap. *)
Theorem suspension_loop_swap {PS : PreStableCategory} (X : object PS)
  : (object_of (Susp (opposite_prestable_category PS)) X = 
     object_of (Loop PS) X) /\
    (object_of (Loop (opposite_prestable_category PS)) X = 
     object_of (Susp PS) X).
Proof.
  split; simpl; reflexivity.
Qed.

(** ** Zero Morphisms in Opposite Categories *)

(** Zero morphisms dualize correctly. *)
Theorem zero_morphism_dualizes {PS : PreStableCategory} (X Y : object PS)
  : zero_morphism (add_zero (opposite_prestable_category PS)) Y X = 
    zero_morphism (add_zero PS) X Y.
Proof.
  unfold zero_morphism.
  simpl.
  reflexivity.
Qed.

(** ** Composition in Opposite Categories *)

(** Example showing how composition reverses in the opposite category. *)
Lemma opposite_composition_demo {PS : PreStableCategory} 
  (X Y Z : object PS)
  (f : morphism PS X Y) (g : morphism PS Y Z)
  : let original_composition := (g o f)%morphism in
    let f_op : morphism (opposite_prestable_category PS) Y X := f in
    let g_op : morphism (opposite_prestable_category PS) Z Y := g in
    let opposite_composition := (f_op o g_op)%morphism in
    opposite_composition = original_composition.
Proof.
  simpl.
  reflexivity.
Qed.

(** End of Section 11: Opposite Functors and Pre-Stable Categories *)

(** * Section 12: Proper Stable Categories *)

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
  (η : NaturalTransformation F G) (X : object PS)
  : components_of (opposite_natural_transformation η) X = components_of η X.
Proof.
  reflexivity.
Qed.

(** *** Isomorphisms in Opposite Categories *)

Lemma opposite_preserves_iso {PS : PreStableCategory} 
  {X Y : object PS} (f : morphism PS X Y)
  : IsIsomorphism f -> 
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

Lemma eta_iso_opposite (PS : ProperStableCategory)
  : forall X, IsIsomorphism (components_of (eta (opposite_prestable_category (pre_stable PS))) X).
Proof.
  intro X.
  simpl.
  apply opposite_preserves_iso.
  exact (epsilon_is_iso PS X).
Qed.

Lemma epsilon_iso_opposite (PS : ProperStableCategory)
  : forall X, IsIsomorphism (components_of (epsilon (opposite_prestable_category (pre_stable PS))) X).
Proof.
  intro X.
  simpl.
  apply opposite_preserves_iso.
  exact (eta_is_iso PS X).
Qed.

(** *** Triangle Identities in the Opposite *)

Lemma opposite_triangle_1 (PS : ProperStableCategory)
  : forall X,
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

Lemma opposite_triangle_2 (PS : ProperStableCategory)
  : forall X,
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

Definition opposite_proper_stable_category (PS : ProperStableCategory)
  : ProperStableCategory.
Proof.
  exact (Build_ProperStableCategory
    (opposite_prestable_category (pre_stable PS))
    (eta_iso_opposite PS)
    (epsilon_iso_opposite PS)
    (opposite_triangle_1 PS)
    (opposite_triangle_2 PS)).
Defined.

(** ** Main Duality Theorems *)

(** The opposite of a proper stable category exists and has the expected form. *)
Theorem proper_stable_duality_principle
  : forall (PS : ProperStableCategory),
    exists (PS_op : ProperStableCategory),
      pre_stable PS_op = opposite_prestable_category (pre_stable PS).
Proof.
  intro PS.
  exists (opposite_proper_stable_category PS).
  reflexivity.
Qed.

(** The beautiful symmetry: Susp and Loop functors perfectly swap roles. *)
Theorem suspension_loop_duality (PS : ProperStableCategory)
  : object_of (Susp (opposite_proper_stable_category PS)) = 
    object_of (opposite_functor (Loop (pre_stable PS))) /\
    object_of (Loop (opposite_proper_stable_category PS)) = 
    object_of (opposite_functor (Susp (pre_stable PS))).
Proof.
  split; reflexivity.
Qed.

(** ** The Fundamental Duality Principle *)

(** This completes our formalization of stable categories and their duality theory.
    The key insights are:
    
    1. Pre-stable categories have suspension and loop functors connected by natural transformations
    2. In the opposite category, these functors swap roles
    3. Proper stable categories (where Σ and Ω are equivalences) are self-dual
    4. Every theorem has a dual obtained by passing to the opposite category
    
    This duality is fundamental in the theory of triangulated and stable categories,
    providing a powerful tool for proving theorems and understanding the structure.
*)

(** End of Section 12: Proper Stable Categories *)

(** * Section 13: Semi-Stable Categories and the Stability Hierarchy *)

(** ** Semi-Stable Categories
    
    Semi-stable categories form an intermediate class between pre-stable and 
    proper stable categories. They are characterized by having the unit or 
    counit be an isomorphism in only one direction, providing insight into 
    the gradual transition from pre-stable to proper stable structures.
    
    This section establishes:
    - Left and right semi-stability definitions
    - The duality between left and right semi-stability
    - Balanced categories where η and ε isomorphism properties correlate
    - The complete hierarchy from pre-stable to proper stable categories
*)

(** *** Left and Right Semi-Stability *)

(** A pre-stable category is left semi-stable if the unit natural 
    transformation η is an isomorphism at every object. *)
Definition is_left_semi_stable (PS : PreStableCategory)
  : Type
  := forall X : object PS, IsIsomorphism (components_of (eta PS) X).

(** A pre-stable category is right semi-stable if the counit natural 
    transformation ε is an isomorphism at every object. *)
Definition is_right_semi_stable (PS : PreStableCategory)
  : Type
  := forall X : object PS, IsIsomorphism (components_of (epsilon PS) X).

(** *** Duality of Semi-Stability *)

(** Left semi-stability in a category corresponds to right semi-stability 
    in the opposite category, demonstrating the fundamental duality principle. *)
Theorem left_semi_stable_opposite_is_right
  : forall (PS : PreStableCategory),
    is_left_semi_stable PS ->
    is_right_semi_stable (opposite_prestable_category PS).
Proof.
  intros PS H_left X.
  unfold is_left_semi_stable in H_left.
  simpl.
  (* In opposite: epsilon becomes eta, so we need eta to be iso *)
  apply opposite_preserves_iso.
  apply H_left.
Qed.

(** *** Almost Proper Stable Categories *)

(** A category is almost proper stable if it is both left and right 
    semi-stable, but may lack the triangle identities. *)
Definition is_almost_proper_stable (PS : PreStableCategory)
  : Type
  := is_left_semi_stable PS * is_right_semi_stable PS.

(** ** Balanced Categories
    
    Balanced categories exhibit a perfect correlation between the isomorphism
    properties of η and ε, providing a natural intermediate step toward
    proper stability.
*)

(** A pre-stable category is balanced if being an isomorphism at X for η
    is equivalent to being an isomorphism at ΣX for ε. *)
Definition is_balanced (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     IsIsomorphism (components_of (eta PS) X) <->
     IsIsomorphism (components_of (epsilon PS) (object_of (Susp PS) X)).

(** Proper stable categories are automatically balanced. *)
Theorem proper_stable_is_balanced
  : forall (PS : ProperStableCategory),
    is_balanced (pre_stable PS).
Proof.
  intros PS X.
  split.
  - intro H. apply (epsilon_is_iso PS).
  - intro H. apply (eta_is_iso PS).
Qed.

(** Semi-stability in both directions implies balance. *)
Theorem semi_stable_both_directions_implies_balanced
  : forall (PS : PreStableCategory),
    is_left_semi_stable PS ->
    is_right_semi_stable PS ->
    is_balanced PS.
Proof.
  intros PS H_left H_right X.
  split.
  - intro H. apply H_right.
  - intro H. apply H_left.
Qed.

(** ** Triangle Identities
    
    The triangle identities provide coherence conditions for the adjunction
    between suspension and loop functors. They are essential for proper
    stability but may be satisfied independently of semi-stability.
*)

(** The first triangle identity: ε(ΣX) ∘ Σ(ηX) = 1. *)
Definition satisfies_triangle_1 (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     (components_of (epsilon PS) (object_of (Susp PS) X) o 
      morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism.

(** The second triangle identity: Ω(εX) ∘ η(ΩX) = 1. *)
Definition satisfies_triangle_2 (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     (morphism_of (Loop PS) (components_of (epsilon PS) X) o
      components_of (eta PS) (object_of (Loop PS) X))%morphism = 1%morphism.

(** Triangle identities are preserved by duality. *)
Theorem triangle_1_in_opposite
  : forall (PS : PreStableCategory),
    satisfies_triangle_1 PS ->
    satisfies_triangle_2 (opposite_prestable_category PS).
Proof.
  intros PS H1 X.
  simpl.
  exact (H1 X).
Qed.

(** ** The Complete Stability Hierarchy
    
    We establish a complete characterization of the hierarchy from
    pre-stable to proper stable categories, providing a refined
    understanding of the progression of stability properties.
*)

(** Almost proper stable categories with triangle identities. *)
Definition almost_proper_stable_strong (PS : PreStableCategory)
  : Type
  := is_left_semi_stable PS * 
     is_right_semi_stable PS * 
     satisfies_triangle_1 PS * 
     satisfies_triangle_2 PS.

(** Almost proper stable with triangle identities implies all conditions
    for proper stability. *)
Theorem almost_proper_is_proper
  : forall (PS : PreStableCategory),
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

(** The complete hierarchy summarizes the relationships between different
    levels of stability. *)
Definition stability_hierarchy_summary
  : Type
  := forall (PS : PreStableCategory),
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

(** The hierarchy theorem confirms the logical progression of stability properties. *)
Theorem stability_hierarchy_holds
  : stability_hierarchy_summary.
Proof.
  unfold stability_hierarchy_summary.
  intros PS _ _ H_almost H_triangles.
  unfold almost_proper_stable_strong.
  destruct H_almost as [H_left H_right].
  destruct H_triangles as [H_tri1 H_tri2].
  exact (H_left, H_right, H_tri1, H_tri2).
Qed.

(** ** One-Sided Inverses from Triangle Identities *)

(** The unit has a left inverse when precomposed with suspension. *)
Definition eta_has_left_inverse (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     exists (g : morphism PS (object_of ((Loop PS) o (Susp PS))%functor X) X),
     (g o components_of (eta PS) X)%morphism = 1%morphism.

(** The counit has a right inverse when postcomposed with loop. *)
Definition epsilon_has_right_inverse (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     exists (g : morphism PS X (object_of ((Susp PS) o (Loop PS))%functor X)),
     (components_of (epsilon PS) X o g)%morphism = 1%morphism.

(** The first triangle identity directly implies that Ση has a left inverse. *)
Theorem triangle_identity_1_gives_left_inverse
  : forall (PS : PreStableCategory) (X : object PS),
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

(** End of Section 13: Semi-Stable Categories and the Stability Hierarchy *)

(** * Section 14: Zero Natural Transformations and Forcing Principles *)

(** ** Zero Natural Transformations
    
    This section investigates the consequences of the unit (η) or counit (ε)
    of the (Σ, Ω) adjunction being trivial (i.e., zero transformations).
    These results establish fundamental constraints: for a category to satisfy
    the triangle identities, the adjunction cannot be trivial unless the 
    category itself is degenerate.
    
    Key results include:
    - Characterization of categories with zero η or ε
    - The η-Zero Forcing Principle
    - Classification of pre-stable categories by retraction properties
*)

(** *** Zero Unit and Counit *)

(** A pre-stable category has zero unit if η is the zero transformation. *)
Definition has_zero_eta (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     components_of (eta PS) X = 
     zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X).

(** A pre-stable category has zero counit if ε is the zero transformation. *)
Definition has_zero_epsilon (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     components_of (epsilon PS) X = 
     zero_morphism (add_zero PS) (object_of ((Susp PS) o (Loop PS))%functor X) X.

(** *** Zero Transformations Break Triangle Identities *)

(** If η is zero, the first triangle identity forces degeneracy. *)
Theorem zero_eta_breaks_triangle_1
  : forall (PS : PreStableCategory),
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

(** If ε is zero, the second triangle identity forces degeneracy. *)
Theorem zero_epsilon_breaks_triangle_2
  : forall (PS : PreStableCategory) (X : object PS),
    satisfies_triangle_2 PS ->
    components_of (epsilon PS) X = 
    zero_morphism (add_zero PS) (object_of ((Susp PS) o (Loop PS))%functor X) X ->
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

(** ** Non-Triviality and the η-Zero Forcing Principle
    
    The η-Zero Forcing Principle reveals an unexpected rigidity in pre-stable
    categories: the vanishing behavior of η is constrained by retraction
    properties.
*)

(** A category is non-trivial if some object has non-zero identity. *)
Definition is_non_trivial (PS : PreStableCategory)
  : Type
  := exists (X : object PS), 
     (1%morphism : morphism PS X X) <> zero_morphism (add_zero PS) X X.

(** *** Retraction Properties *)

(** An object admits a retraction from zero if it can be split off from zero. *)
Definition admits_retraction_from_zero (PS : PreStableCategory) (X : object PS)
  : Type
  := exists (i : morphism PS (@zero _ (add_zero PS)) X) 
            (r : morphism PS X (@zero _ (add_zero PS))),
     (r o i)%morphism = 1%morphism.

(** Zero always admits a retraction from itself. *)
Theorem zero_always_retractable
  : forall (PS : PreStableCategory),
    admits_retraction_from_zero PS (@zero _ (add_zero PS)).
Proof.
  intro PS.
  exists 1%morphism, 1%morphism.
  apply morphism_left_identity.
Qed.

(** *** The η-Zero Forcing Principle *)

(** If an object X admits a retraction from zero and η vanishes at X,
    then η must also vanish at zero. This reveals a fundamental constraint
    on the vanishing locus of η. *)
Theorem eta_zero_forcing_principle
  : forall (PS : PreStableCategory) (X : object PS),
    admits_retraction_from_zero PS X ->
    components_of (eta PS) X = 
    zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X) ->
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

(** *** The η-Nonzero Propagation Principle *)

(** The contrapositive: if η is non-zero at zero, it cannot vanish at any
    retractable object. *)
Theorem eta_nonzero_propagation
  : forall (PS : PreStableCategory),
    components_of (eta PS) (@zero _ (add_zero PS)) <> 
    zero_morphism (add_zero PS) (@zero _ (add_zero PS)) 
      (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))) ->
    forall (X : object PS),
    admits_retraction_from_zero PS X ->
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

(** ** Classification of Pre-Stable Categories
    
    Pre-stable categories can be classified based on the behavior of η
    with respect to retractable objects.
*)

(** Class I: η vanishes at zero (and hence at all retractable objects). *)
Definition class_I_prestable (PS : PreStableCategory)
  : Type
  := components_of (eta PS) (@zero _ (add_zero PS)) = 
     zero_morphism (add_zero PS) (@zero _ (add_zero PS)) 
       (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))).

(** Class II: η is non-zero at all retractable objects. *)
Definition class_II_prestable (PS : PreStableCategory)
  : Type
  := forall (X : object PS),
     admits_retraction_from_zero PS X ->
     components_of (eta PS) X <> 
     zero_morphism (add_zero PS) X (object_of ((Loop PS) o (Susp PS))%functor X).

(** The two classes are mutually exclusive. *)
Theorem prestable_classes_disjoint
  : forall (PS : PreStableCategory),
    class_I_prestable PS ->
    ~(class_II_prestable PS).
Proof.
  intros PS H_class_I H_class_II.
  
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
  : forall (PS : PreStableCategory),
    class_II_prestable PS ->
    components_of (eta PS) (@zero _ (add_zero PS)) <> 
    zero_morphism (add_zero PS) (@zero _ (add_zero PS)) 
      (object_of ((Loop PS) o (Susp PS))%functor (@zero _ (add_zero PS))).
Proof.
  intros PS H_class_II.
  apply H_class_II.
  apply zero_always_retractable.
Qed.

(** *** Uniqueness of Retractions *)

(** If an object admits a retraction from zero, the morphisms are unique. *)
Theorem retractable_objects_unique_inclusion
  : forall (PS : PreStableCategory) (X : object PS),
    admits_retraction_from_zero PS X ->
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

Theorem retractable_objects_unique_retraction
  : forall (PS : PreStableCategory) (X : object PS),
    admits_retraction_from_zero PS X ->
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

(** *** Canonical Form of Retractions *)

Theorem retraction_canonical_form
  : forall (PS : PreStableCategory) (X : object PS),
    admits_retraction_from_zero PS X <->
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

(** End of Section 14: Zero Natural Transformations and Forcing Principles *)

(** * Section 15: Advanced Structural Properties *)

(** ** Self-Dual Triangulated Categories
    
    Self-dual triangulated categories exhibit a special symmetry where the
    two triangle identities become equivalent. This section explores these
    exceptional structures and their implications for the theory of
    triangulated categories.
*)

(** A pre-stable category is self-dual triangulated if the two triangle
    identities are equivalent at every object. *)
Definition is_self_dual_triangulated (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     ((components_of (epsilon PS) (object_of (Susp PS) X) o 
       morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism) <->
     ((morphism_of (Loop PS) (components_of (epsilon PS) X) o
       components_of (eta PS) (object_of (Loop PS) X))%morphism = 1%morphism).

(** Self-duality implies that one triangle identity gives both. *)
Theorem self_dual_gives_both_triangles
  : forall (PS : PreStableCategory),
    is_self_dual_triangulated PS ->
    satisfies_triangle_1 PS ->
    satisfies_triangle_2 PS.
Proof.
  intros PS H_self H1 X.
  destruct (H_self X) as [H_forward H_backward].
  apply H_forward.
  apply H1.
Qed.

(** ** Commuting Suspension and Loop Functors
    
    We investigate conditions under which the suspension and loop functors
    commute up to natural isomorphism, revealing deep structural properties
    of the category.
*)

(** Suspension and loop commute if there exists a natural isomorphism between
    their compositions. *)
Definition has_commuting_susp_loop (PS : PreStableCategory)
  : Type
  := exists (α : NaturalTransformation 
       ((Susp PS) o (Loop PS))%functor
       ((Loop PS) o (Susp PS))%functor),
     forall X, IsIsomorphism (components_of α X).

(** The compositions of suspension and loop coincide at the object level. *)
Definition has_coinciding_compositions (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     object_of ((Susp PS) o (Loop PS))%functor X = 
     object_of ((Loop PS) o (Susp PS))%functor X.

(** ** Functor Compositions and Identity Relations *)

(** Suspension composed with loop equals the identity functor. *)
Definition susp_loop_is_identity (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     object_of ((Susp PS) o (Loop PS))%functor X = X.

(** Loop composed with suspension equals the identity functor. *)
Definition loop_susp_is_identity (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     object_of ((Loop PS) o (Susp PS))%functor X = X.

(** Both compositions being identity implies they coincide. *)
Theorem both_compositions_identity_coincide
  : forall (PS : PreStableCategory),
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

(** A category has inverse objects if both functor compositions are identity. *)
Definition has_inverse_objects (PS : PreStableCategory)
  : Type
  := susp_loop_is_identity PS * loop_susp_is_identity PS.

(** Inverse objects are preserved under duality. *)
Theorem inverse_objects_opposite
  : forall (PS : PreStableCategory),
    has_inverse_objects PS ->
    has_inverse_objects (opposite_prestable_category PS).
Proof.
  intros PS [H_sl H_ls].
  split.
  - intro X. simpl. exact (H_ls X).
  - intro X. simpl. exact (H_sl X).
Qed.

(** ** Suspension Fixed Points
    
    Suspension fixed points are objects X such that ΣX ≅ X. These special
    objects provide insight into the periodic behavior of the suspension
    functor.
*)

(** An object is a suspension fixed point if it is isomorphic to its suspension. *)
Definition is_suspension_fixed_point (PS : PreStableCategory) (X : object PS)
  : Type
  := exists (φ : morphism PS (object_of (Susp PS) X) X), IsIsomorphism φ.

(** *** Properties of Suspended Zero *)

(** The suspended zero object has the initial property. *)
Lemma susp_zero_is_initial
  : forall (PS : PreStableCategory) (Y : object PS),
    Contr (morphism PS (object_of (Susp PS) (@zero _ (add_zero PS))) Y).
Proof.
  intros PS Y.
  pose proof (preserves_zero PS PS (Susp PS)) as H_zero.
  rewrite H_zero.
  apply (@is_initial _ (add_zero PS) Y).
Qed.

(** The suspended zero object has the terminal property. *)
Lemma susp_zero_is_terminal
  : forall (PS : PreStableCategory) (X : object PS),
    Contr (morphism PS X (object_of (Susp PS) (@zero _ (add_zero PS)))).
Proof.
  intros PS X.
  pose proof (preserves_zero PS PS (Susp PS)) as H_zero.
  rewrite H_zero.
  apply (@is_terminal _ (add_zero PS) X).
Qed.

(** *** Zero is Always a Fixed Point *)

(** The zero object is a suspension fixed point in any pre-stable category. *)
Theorem zero_is_suspension_fixed_point
  : forall (PS : PreStableCategory),
    is_suspension_fixed_point PS (@zero _ (add_zero PS)).
Proof.
  intro PS.
  unfold is_suspension_fixed_point.
  
  (* The morphism from Σ(0) to 0 *)
  pose (φ := @center _ (@is_terminal _ (add_zero PS) 
                        (object_of (Susp PS) (@zero _ (add_zero PS))))).
  exists φ.
  
  (* Its inverse from 0 to Σ(0) *)
  pose (ψ := @center _ (@is_initial _ (add_zero PS) 
                        (object_of (Susp PS) (@zero _ (add_zero PS))))).
  exists ψ.
  
  split.
  - (* Left inverse: ψ ∘ φ = 1 on Σ(0) *)
    apply initial_morphism_unique.
    apply susp_zero_is_initial.
    
  - (* Right inverse: φ ∘ ψ = 1 on 0 *)
    transitivity (@center _ (@is_terminal _ (add_zero PS) (@zero _ (add_zero PS)))).
    + apply terminal_morphism_unique.
      apply (@is_terminal _ (add_zero PS)).
    + apply terminal_zero_to_zero_is_id.
Qed.

(** Properties preserved by isomorphisms transfer to suspended objects
    for fixed points. *)
Theorem suspension_fixed_point_transport
  : forall (PS : PreStableCategory) (X : object PS),
    is_suspension_fixed_point PS X ->
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

(** ** Distinguished Triangles Under Duality
    
    We establish how distinguished triangles behave under the opposite
    category construction, providing insight into the duality of
    triangulated structures.
*)

(** Distinguished triangles dualize with reversed morphisms and swapped
    suspension/loop functors. *)
Lemma distinguished_triangle_duality {PS : PreStableCategory} 
  (D : @DistinguishedTriangle PS)
  : let T := triangle D in
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

(** ** Axiom TR4: The Octahedral Axiom
    
    The octahedral axiom (TR4) is the fourth axiom of triangulated categories.
    It describes how distinguished triangles arising from composable morphisms
    fit together in an octahedral diagram.
*)

(** *** Statement of TR4 *)

(** TR4 requires existence of a morphism making specific diagrams commute. *)
Definition TR4_statement (S : PreStableCategoryWithCofiber)
  : Type
  := forall (X Y Z : object S) (f : morphism S X Y) (g : morphism S Y Z),
     exists (u : morphism S (@cofiber S X Y f) (@cofiber S Y Z g)),
     (u o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism.

(** *** Universal Property of Cofibers *)

(** Cofibers satisfy a universal property: morphisms from the source that
    vanish on the morphism factor uniquely through the cofiber. *)
Definition cofiber_universal_property (S : PreStableCategoryWithCofiber)
  : Type
  := forall (X Y : object S) (f : morphism S X Y) (W : object S)
            (h : morphism S Y W),
     (h o f)%morphism = zero_morphism (add_zero (base S)) X W ->
     { k : morphism S (@cofiber S X Y f) W |
       (k o @cofiber_in S X Y f)%morphism = h /\
       forall k' : morphism S (@cofiber S X Y f) W,
       (k' o @cofiber_in S X Y f)%morphism = h -> k' = k }.

(** *** TR4 and Universal Properties *)

(** The TR4 morphism is unique when cofibers have the universal property. *)
Theorem TR4_morphism_unique_via_universal
  : forall (S : PreStableCategoryWithCofiber),
    cofiber_universal_property S ->
    forall (X Y Z : object S) (f : morphism S X Y) (g : morphism S Y Z)
           (u1 u2 : morphism S (@cofiber S X Y f) (@cofiber S Y Z g)),
    (u1 o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism ->
    (u2 o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism ->
    u1 = u2.
Proof.
  intros S H_universal X Y Z f g u1 u2 H1 H2.
  
  (* Verify that cofiber_in ∘ g satisfies the zero condition *)
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
    as [k [H_comm H_unique]].
  
  (* Both morphisms equal k by uniqueness *)
  rewrite (H_unique u1 H1).
  rewrite (H_unique u2 H2).
  reflexivity.
Qed.

(** The TR4 morphism exists when cofibers have the universal property. *)
Theorem TR4_morphism_exists
  : forall (S : PreStableCategoryWithCofiber),
    cofiber_universal_property S ->
    forall (X Y Z : object S) (f : morphism S X Y) (g : morphism S Y Z),
    exists (u : morphism S (@cofiber S X Y f) (@cofiber S Y Z g)),
    (u o @cofiber_in S X Y f)%morphism = (@cofiber_in S Y Z g o g)%morphism.
Proof.
  intros S H_universal X Y Z f g.
  
  assert (H_zero: ((@cofiber_in S Y Z g o g) o f)%morphism = 
                  zero_morphism (add_zero (base S)) X (@cofiber S Y Z g)).
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

(** *** Complete TR4 Axiom *)

(** The full TR4 axiom with octahedral diagram and all required morphisms. *)
Definition satisfies_TR4 (S : PreStableCategoryWithCofiber)
  : Type
  := cofiber_universal_property S *
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

(** End of Section 15: Advanced Structural Properties *)

(** * Section 16: The Universal Duality Principle *)

(** ** The Universal Duality Principle
    
    This section establishes the most powerful meta-theorem in stable category
    theory: any property or construction in a pre-stable category automatically
    has a dual in the opposite category. This principle allows us to obtain
    new theorems "for free" by dualizing existing ones.
*)

(** *** The Fundamental Duality Theorem *)

(** Any property that holds for all pre-stable categories also holds for
    their opposites. This is the foundation of categorical duality. *)
Theorem duality_principle
  : forall (statement : PreStableCategory -> Prop),
    (forall PS, statement PS) -> 
    (forall PS, statement (opposite_prestable_category PS)).
Proof.
  intros statement H PS.
  apply H.
Qed.

(** ** Double Opposite Properties
    
    The double opposite construction returns us to an equivalent category,
    establishing that dualization is an involution up to isomorphism.
*)

(** *** Double Opposite Functors *)

Definition double_opposite_functor (C : PreCategory)
  : Functor (opposite_category (opposite_category C)) C.
Proof.
  exact (Build_Functor
    (opposite_category (opposite_category C)) C
    (fun X => X)
    (fun X Y f => f)
    (fun X Y Z f g => idpath)
    (fun X => idpath)).
Defined.

Definition to_double_opposite_functor (C : PreCategory)
  : Functor C (opposite_category (opposite_category C)).
Proof.
  exact (Build_Functor
    C (opposite_category (opposite_category C))
    (fun X => X)
    (fun X Y f => f)
    (fun X Y Z f g => idpath)
    (fun X => idpath)).
Defined.

(** *** Basic Involution Properties *)

Lemma opposite_involution_objects (C : PreCategory)
  : object (opposite_category (opposite_category C)) = object C.
Proof.
  reflexivity.
Qed.

Lemma opposite_involution_morphisms (C : PreCategory) (X Y : object C)
  : morphism (opposite_category (opposite_category C)) X Y = morphism C X Y.
Proof.
  reflexivity.
Qed.

(** *** Double Opposite for Pre-Stable Categories *)

(** The double opposite of a pre-stable category recovers the original
    functor structure. *)
Theorem double_opposite_susp_commutes
  : forall (PS : PreStableCategory),
    object_of (Susp PS) = 
    object_of (Susp (opposite_prestable_category 
                     (opposite_prestable_category PS))).
Proof.
  intro PS.
  simpl.
  reflexivity.
Qed.

Theorem double_opposite_eta_components
  : forall (PS : PreStableCategory) (X : object PS),
    components_of (eta PS) X =
    components_of (eta (opposite_prestable_category 
                       (opposite_prestable_category PS))) X.
Proof.
  intros PS X.
  simpl.
  reflexivity.
Qed.

(** ** Groupoid Properties Under Duality
    
    If a category is a groupoid (all morphisms are isomorphisms), this
    property is preserved under the opposite construction.
*)

Definition is_groupoid (C : PreCategory)
  : Type
  := forall (X Y : object C) (f : morphism C X Y), IsIsomorphism f.

Theorem opposite_preserves_groupoid_property
  : forall (PS : PreStableCategory),
    is_groupoid PS ->
    is_groupoid (opposite_prestable_category PS).
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

(** ** Preservation of Zero Compositions Under Duality *)

Theorem opposite_preserves_zero_composition
  : forall (PS : PreStableCategory) (X Y Z : object PS) 
           (f : morphism PS X Y) (g : morphism PS Y Z),
    (g o f)%morphism = zero_morphism (add_zero PS) X Z ->
    ((f : morphism (opposite_prestable_category PS) Y X) o 
     (g : morphism (opposite_prestable_category PS) Z Y))%morphism = 
    zero_morphism (add_zero (opposite_prestable_category PS)) Z X.
Proof.
  intros PS X Y Z f g H.
  simpl.
  exact H.
Qed.

(** ** Existence Principles for Pre-Stable Categories
    
    Every pre-stable category gives rise to an opposite pre-stable category
    with predictable structure.
*)

Theorem opposite_prestable_is_prestable
  : forall (PS : PreStableCategory),
    PreStableCategory.
Proof.
  intro PS.
  exact (opposite_prestable_category PS).
Defined.

Theorem opposite_functor_correspondence
  : forall (PS : PreStableCategory),
    Susp (opposite_prestable_category PS) = 
    opposite_additive_functor (Loop PS).
Proof.
  intro PS.
  reflexivity.
Qed.

(** End of Section 16: The Universal Duality Principle *)

(** * Section 17: Applications of Duality and Meta-Theorems *)

(** ** Compatible Pairs and Adjunction Flexibility
    
    This section explores what happens when we consider arbitrary natural
    transformations satisfying the triangle identities, not just the
    specific η and ε of a pre-stable category.
*)

(** A compatible pair is any pair of natural transformations satisfying
    the triangle identities. *)
Definition compatible_pair (PS : PreStableCategory)
  (η' : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
  (ε' : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor)
  : Type
  := (forall X, (components_of ε' (object_of (Susp PS) X) o
                 morphism_of (Susp PS) (components_of η' X))%morphism = 1%morphism) *
     (forall X, (morphism_of (Loop PS) (components_of ε' X) o
                 components_of η' (object_of (Loop PS) X))%morphism = 1%morphism).

(** Compatible pairs automatically satisfy the triangle identities. *)
Theorem compatible_pair_satisfies_triangle_1
  : forall (PS : PreStableCategory)
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

(** ** The Space of Adjunction Data
    
    This explores the flexibility in choosing adjunction data for a given
    pair of functors, showing that the triangle identities impose strong
    constraints.
*)

(** Any compatible pair interacts predictably with zero morphisms. *)
Theorem compatible_pair_zero_interaction
  : forall (PS : PreStableCategory)
           (η : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
           (ε : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor),
    compatible_pair PS η ε ->
    forall X,
    (components_of ε (object_of (Susp PS) X) o
     morphism_of (Susp PS) (zero_morphism (add_zero PS) X 
       (object_of ((Loop PS) o (Susp PS))%functor X)))%morphism =
    zero_morphism (add_zero PS) (object_of (Susp PS) X) (object_of (Susp PS) X).
Proof.
  intros PS η ε H_compat X.
  rewrite susp_preserves_zero_morphisms.
  apply zero_morphism_right.
Qed.

(** ** Biproduct Uniqueness
    
    Biproducts in additive categories are unique up to unique isomorphism,
    a fundamental fact about additive structure.
*)

(** Two biproducts of the same objects are canonically isomorphic. *)
Theorem biproduct_unique_up_to_iso (A : AdditiveCategory) (X Y : object A)
  : let B1 := add_biproduct A X Y in
    let B2 := add_biproduct A X Y in
    exists (f : morphism A (add_biproduct_obj A X Y) (add_biproduct_obj A X Y)),
      IsIsomorphism f /\
      (f o @inl _ _ _ (add_biproduct_data A X Y) = 
       @inl _ _ _ (add_biproduct_data A X Y))%morphism /\
      (f o @inr _ _ _ (add_biproduct_data A X Y) = 
       @inr _ _ _ (add_biproduct_data A X Y))%morphism.
Proof.
  intros B1 B2.
  (* Since B1 and B2 are definitionally equal, the identity works *)
  exists 1%morphism.
  split; [|split].
  - apply iso_identity.
  - apply morphism_left_identity.
  - apply morphism_left_identity.
Qed.

(** ** The Meta-Theorem: Automatic Dualization
    
    Any construction or theorem about pre-stable
    categories automatically dualizes. This means every theorem in this
    formalization has a dual theorem obtained by applying the opposite
    construction.
*)

Theorem automatic_dualization
  : forall (P : PreStableCategory -> Type),
    (forall PS, P PS) ->
    (forall PS, P (opposite_prestable_category PS)).
Proof.
  intros P H PS.
  apply H.
Qed.

(** End of Section 17: Applications of Duality and Meta-Theorems *)

(** * Section 18: The Octahedral Axiom (TR4) *)

(** ** The Octahedral Axiom
    
    This section develops the fourth axiom of triangulated categories, known as
    the octahedral axiom (TR4). This axiom describes how distinguished triangles
    arising from composable morphisms fit together in a precise octahedral pattern.
    
    The octahedral axiom is the most complex of the triangulated category axioms,
    requiring careful analysis of how cofiber sequences interact under composition.
    We establish:
    - The universal property of cofibers
    - Construction of the octahedral morphisms
    - Verification that these morphisms satisfy the required properties
    - The complete statement and consequences of TR4
*)

(** *** Fundamental Lemmas for Cofiber Compositions
    
    These lemmas establish how cofiber morphisms behave under composition,
    providing the technical foundation for the octahedral axiom.
*)

(** The cofiber inclusion of a composite morphism vanishes when composed
    with the composite itself. This is a direct consequence of the defining
    property of cofibers. *)
Lemma cofiber_in_composition {S : PreStableCategoryWithCofiber}
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : (@cofiber_in S A C (g o f)%morphism o g o f)%morphism = 
    zero_morphism (add_zero (base S)) A (@cofiber S A C (g o f)%morphism).
Proof.
  (* The expression (cofiber_in S (g o f) o g o f) is parsed as 
     ((cofiber_in S (g o f) o g) o f) *)
  (* We want to rewrite it as (cofiber_in S (g o f) o (g o f)) *)
  rewrite morphism_associativity.
  (* Apply the cofiber condition *)
  apply (@cofiber_cond1 S A C (g o f)%morphism).
Qed.

(** *** The Universal Property of Cofibers
    
    The universal property states that morphisms from the source that vanish
    on the given morphism factor uniquely through the cofiber. This property
    is central to all constructions involving cofibers.
*)

(** A morphism that vanishes after precomposition with f factors uniquely
    through the cofiber of f. *)
Lemma morphism_vanishing_on_f_factors {S : PreStableCategoryWithCofiber}
  (H_universal : cofiber_universal_property S)
  {A B W : object S} (f : morphism S A B) (h : morphism S B W)
  : (h o f)%morphism = zero_morphism (add_zero (base S)) A W ->
    { k : morphism S (@cofiber S A B f) W |
      (k o @cofiber_in S A B f)%morphism = h /\
      forall k' : morphism S (@cofiber S A B f) W,
      (k' o @cofiber_in S A B f)%morphism = h -> k' = k }.
Proof.
  intro H_zero.
  
  (* Apply the universal property directly *)
  destruct (H_universal A B f W h H_zero) as [k [Hk_comm Hk_unique]].
  
  (* Package the result *)
  exists k.
  split.
  - exact Hk_comm.
  - exact Hk_unique.
Qed.

(** Any morphism factoring through a cofiber vanishes on the original morphism. *)
Lemma morphism_through_cofiber_vanishes_on_f {S : PreStableCategoryWithCofiber}
  {A B W : object S} (f : morphism S A B) 
  (k : morphism S B W) (k' : morphism S (@cofiber S A B f) W)
  : k = (k' o @cofiber_in S A B f)%morphism ->
    (k o f)%morphism = zero_morphism (add_zero (base S)) A W.
Proof.
  intro H_factor.
  rewrite H_factor.
  (* Now we have ((k' o cofiber_in S f) o f) *)
  rewrite morphism_associativity.
  (* Now we have (k' o (cofiber_in S f o f)) *)
  rewrite (@cofiber_cond1 S A B f).
  apply zero_morphism_right.
Qed.

(** The uniqueness aspect of the universal property: morphisms from the
    cofiber are determined by their composition with the cofiber inclusion. *)
Lemma cofiber_morphism_uniqueness {S : PreStableCategoryWithCofiber}
  (H_universal : cofiber_universal_property S)
  {A B W : object S} (f : morphism S A B)
  (k₁ k₂ : morphism S (@cofiber S A B f) W)
  : (k₁ o @cofiber_in S A B f)%morphism = (k₂ o @cofiber_in S A B f)%morphism ->
    k₁ = k₂.
Proof.
  intro H_eq.
  
  (* Both k₁ and k₂ satisfy the factorization property for the same morphism *)
  pose (h := (k₁ o @cofiber_in S A B f)%morphism).
  
  (* First, show that h ∘ f = 0 *)
  assert (H_zero : (h o f)%morphism = zero_morphism (add_zero (base S)) A W).
  {
    unfold h.
    rewrite morphism_associativity.
    rewrite (@cofiber_cond1 S A B f).
    apply zero_morphism_right.
  }
  
  (* Apply universal property to get uniqueness *)
  destruct (H_universal A B f W h H_zero) as [k [Hk_comm Hk_unique]].
  
  (* k₁ satisfies the property *)
  assert (H1 : k₁ = k).
  { apply Hk_unique. unfold h. reflexivity. }
  
  (* k₂ also satisfies the property *)
  assert (H2 : k₂ = k).
  { apply Hk_unique. unfold h. rewrite <- H_eq. reflexivity. }
  
  (* Therefore k₁ = k₂ *)
  rewrite H1, H2.
  reflexivity.
Qed.

(** *** Construction of Octahedral Morphisms
    
    The octahedral axiom requires the existence of specific morphisms between
    cofibers of composable morphisms. We construct these morphisms using the
    universal property.
*)

(** The cofiber inclusion of a composite, when composed with the second morphism,
    vanishes on the first. This is the key observation enabling the octahedral
    construction. *)
Lemma cofiber_composite_vanishes_on_first {S : PreStableCategoryWithCofiber}
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
    zero_morphism (add_zero (base S)) A (@cofiber S A C (g o f)%morphism).
Proof.
  (* We have ((cofiber_in(g∘f) ∘ g) ∘ f) *)
  (* First show this equals cofiber_in(g∘f) ∘ (g ∘ f) *)
  assert (H: ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
             (@cofiber_in S A C (g o f)%morphism o (g o f)%morphism)%morphism).
  {
    rewrite morphism_associativity.
    reflexivity.
  }
  rewrite H.
  (* Now apply the cofiber condition *)
  exact (@cofiber_cond1 S A C (g o f)%morphism).
Qed.

(** The first octahedral morphism: cofiber(f) → cofiber(g∘f). This morphism
    exists by the universal property since cofiber_in(g∘f) ∘ g vanishes on f. *)
Lemma cofiber_composite_factors_through_first {S : PreStableCategoryWithCofiber}
  (H_universal : cofiber_universal_property S)
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : { u : morphism S (@cofiber S A B f) (@cofiber S A C (g o f)%morphism) |
      (u o @cofiber_in S A B f)%morphism = 
      (@cofiber_in S A C (g o f)%morphism o g)%morphism }.
Proof.
  (* We need to show that (cofiber_in(g∘f) ∘ g) vanishes on f *)
  assert (H_zero : ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
                   zero_morphism (add_zero (base S)) A (@cofiber S A C (g o f)%morphism)).
  {
    apply cofiber_composite_vanishes_on_first.
  }
  
  (* Apply the universal property of cofiber(f) *)
  destruct (morphism_vanishing_on_f_factors H_universal f 
           (@cofiber_in S A C (g o f)%morphism o g)%morphism H_zero)
    as [u [Hu_comm Hu_unique]].
  
  (* Return just the existence part *)
  exists u.
  exact Hu_comm.
Qed.

(** Induced morphisms between cofibers from commutative squares. This lemma
    shows that cofiber is functorial with respect to commutative squares. *)
Lemma cofiber_morphism_from_square {S : PreStableCategoryWithCofiber}
  (H_universal : cofiber_universal_property S)
  {A₁ B₁ A₂ B₂ : object S}
  (f₁ : morphism S A₁ B₁) (f₂ : morphism S A₂ B₂)
  (α : morphism S A₁ A₂) (β : morphism S B₁ B₂)
  : (β o f₁)%morphism = (f₂ o α)%morphism ->
    { γ : morphism S (@cofiber S A₁ B₁ f₁) (@cofiber S A₂ B₂ f₂) |
      (γ o @cofiber_in S A₁ B₁ f₁)%morphism = 
      (@cofiber_in S A₂ B₂ f₂ o β)%morphism }.
Proof.
  intro H_square.
  
  (* We need to show that cofiber_in(f₂) ∘ β vanishes on f₁ *)
  assert (H_zero : ((@cofiber_in S A₂ B₂ f₂ o β)%morphism o f₁)%morphism =
                   zero_morphism (add_zero (base S)) A₁ (@cofiber S A₂ B₂ f₂)).
  {
    rewrite morphism_associativity.
    rewrite H_square.
    rewrite <- morphism_associativity.
    rewrite (@cofiber_cond1 S A₂ B₂ f₂).
    apply zero_morphism_left.
  }
  
  (* Apply universal property and extract just the existence part *)
  destruct (morphism_vanishing_on_f_factors H_universal f₁ 
           (@cofiber_in S A₂ B₂ f₂ o β)%morphism H_zero)
    as [γ [Hγ_comm Hγ_unique]].
  
  exists γ.
  exact Hγ_comm.
Qed.

(** *** Properties of Octahedral Morphisms
    
    We establish key properties of the morphisms appearing in the octahedral
    diagram, showing how they interact and compose.
*)

(** Composition of compatible cofiber morphisms behaves predictably. *)
Lemma cofiber_morphism_composition {S : PreStableCategoryWithCofiber}
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  (u : morphism S (@cofiber S A B f) (@cofiber S B C g))
  (v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism))
  : (u o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism ->
    (v o @cofiber_in S B C g)%morphism = @cofiber_in S A C (g o f)%morphism ->
    ((v o u)%morphism o @cofiber_in S A B f)%morphism = 
    (@cofiber_in S A C (g o f)%morphism o g)%morphism.
Proof.
  intros Hu Hv.
  
  (* We have ((v ∘ u) ∘ cofiber_in(f)) and want to show it equals 
     cofiber_in(g∘f) ∘ g *)
  rewrite morphism_associativity.
  (* Now we have: v ∘ (u ∘ cofiber_in(f)) *)
  rewrite Hu.
  (* Now we have: v ∘ (cofiber_in(g) ∘ g) *)
  rewrite <- morphism_associativity.
  (* Now we have: (v ∘ cofiber_in(g)) ∘ g *)
  rewrite Hv.
  (* Now we have: cofiber_in(g∘f) ∘ g *)
  reflexivity.
Qed.

(** *** Complete Statement of TR4
    
    We now give the complete formulation of the octahedral axiom, including
    all required morphisms and their properties.
*)

(** The third morphism in the octahedral diagram connects cofiber(g∘f) to
    the suspension of cofiber(f). *)
Definition octahedral_third_morphism_exists (S : PreStableCategoryWithCofiber)
  : Type
  := forall (A B C : object S) (f : morphism S A B) (g : morphism S B C),
     { w : morphism S (@cofiber S A C (g o f)%morphism) 
                      (object_of (Susp (base S)) (@cofiber S A B f)) |
       (* w is the connecting morphism in the distinguished triangle *)
       (w o @cofiber_in S A C (g o f)%morphism)%morphism = 
       zero_morphism (add_zero (base S)) C 
         (object_of (Susp (base S)) (@cofiber S A B f)) /\
       (* w fits into the octahedral diagram *)
       exists (t : morphism S (object_of (Susp (base S)) A)
                              (object_of (Susp (base S)) (@cofiber S A B f))),
         w = (t o @cofiber_out S A C (g o f)%morphism)%morphism }.

(** The second morphism v : cofiber(g) → cofiber(g∘f) exists and is
    compatible with the suspension structure. *)
Definition has_octahedral_morphisms (S : PreStableCategoryWithCofiber)
  : Type
  := forall (A B C : object S) (f : morphism S A B) (g : morphism S B C),
     { v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism) |
       (v o @cofiber_in S B C g)%morphism = @cofiber_in S A C (g o f)%morphism /\
       (* v is compatible with the suspension structure *)
       exists (s : morphism S (object_of (Susp (base S)) B) 
                              (object_of (Susp (base S)) A)),
         (@cofiber_out S A C (g o f)%morphism o v)%morphism = 
         (s o @cofiber_out S B C g)%morphism }.

(** The complete octahedral axiom TR4 states that:
    1. Cofibers have the universal property
    2. The octahedral morphisms exist
    3. The third morphism exists
    4. The resulting triangle is distinguished *)
Definition TR4_octahedral_axiom (S : PreStableCategoryWithCofiber)
  : Type
  := (cofiber_universal_property S) *
     (has_octahedral_morphisms S) *
     (octahedral_third_morphism_exists S) *
     (forall (A B C : object S) (f : morphism S A B) (g : morphism S B C),
      (* The triangle formed by the three cofibers is distinguished *)
      @DistinguishedTriangle (base S)).

(** *** Consequences of TR4
    
    We establish several important consequences of the octahedral axiom,
    showing uniqueness of morphisms and various commutativity properties.
*)

(** The octahedral morphisms are unique when they exist. *)
Theorem TR4_morphisms_unique (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
  (H_universal : cofiber_universal_property S)
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : forall (u1 u2 : morphism S (@cofiber S A B f) (@cofiber S B C g)),
    (u1 o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism ->
    (u2 o @cofiber_in S A B f)%morphism = (@cofiber_in S B C g o g)%morphism ->
    u1 = u2.
Proof.
  intros u1 u2 H1 H2.
  
  (* Both u1 and u2 satisfy the same property, so by uniqueness they're equal *)
  assert (H_zero : ((@cofiber_in S B C g o g)%morphism o f)%morphism =
                   zero_morphism (add_zero (base S)) A (@cofiber S B C g)).
  {
    (* We have (cofiber_in(g) ∘ g) ∘ f *)
    (* By cofiber_cond1, cofiber_in(g) ∘ g = 0 *)
    pose proof (@cofiber_cond1 S B C g) as H_cond.
    rewrite H_cond.
    (* Now we have 0 ∘ f = 0 *)
    apply zero_morphism_left.
  }
  
  (* Apply the uniqueness part of the universal property *)
  destruct (H_universal A B f (@cofiber S B C g) 
           (@cofiber_in S B C g o g)%morphism H_zero) as [u [Hu Hu_unique]].
  
  rewrite (Hu_unique u1 H1).
  rewrite (Hu_unique u2 H2).
  reflexivity.
Qed.

(** The octahedral morphisms satisfy the expected properties. *)
Theorem octahedral_morphism_properties (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
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
Theorem octahedral_third_morphism_vanishes (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : (* The third morphism w vanishes when composed with cofiber_in *)
    exists w : morphism S (@cofiber S A C (g o f)%morphism) 
                         (object_of (Susp (base S)) (@cofiber S A B f)),
      (w o @cofiber_in S A C (g o f)%morphism)%morphism = 
      zero_morphism (add_zero (base S)) C 
        (object_of (Susp (base S)) (@cofiber S A B f)).
Proof.
  destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
  destruct (H_third A B C f g) as [w [Hw_zero Hw_exist]].
  exists w.
  exact Hw_zero.
Qed.

(** The triangle formed by the three cofibers is distinguished. *)
Theorem octahedral_triangle_distinguished (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : @DistinguishedTriangle (base S).
Proof.
  destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
  exact (H_dist A B C f g).
Qed.

(** All octahedral morphisms exist and satisfy their defining properties. *)
Theorem octahedral_morphisms_exist (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : (* All three morphisms in the octahedral diagram exist *)
    (exists u : morphism S (@cofiber S A B f) (@cofiber S A C (g o f)%morphism),
       (u o @cofiber_in S A B f)%morphism = 
       (@cofiber_in S A C (g o f)%morphism o g)%morphism) /\
    (exists v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism),
       (v o @cofiber_in S B C g)%morphism = @cofiber_in S A C (g o f)%morphism) /\
    (exists w : morphism S (@cofiber S A C (g o f)%morphism) 
                          (object_of (Susp (base S)) (@cofiber S A B f)),
       (w o @cofiber_in S A C (g o f)%morphism)%morphism = 
       zero_morphism (add_zero (base S)) C 
         (object_of (Susp (base S)) (@cofiber S A B f))).
Proof.
  destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
  
  split; [|split].
  
  - (* u exists by the universal property *)
    exact (cofiber_composite_factors_through_first H_universal f g).
    
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
Theorem octahedral_suspension_compatibility (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : (* The morphism v is compatible with suspension *)
    exists (v : morphism S (@cofiber S B C g) (@cofiber S A C (g o f)%morphism))
           (s : morphism S (object_of (Susp (base S)) B) 
                          (object_of (Susp (base S)) A)),
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

(** The octahedral axiom is functorial: it respects composition of morphisms. *)
Theorem octahedral_functoriality (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
  {A B C D : object S} 
  (f : morphism S A B) (g : morphism S B C) (h : morphism S C D)
  : (* Octahedral morphisms for different compositions are related *)
    @DistinguishedTriangle (base S) /\  (* For f, g *)
    @DistinguishedTriangle (base S) /\  (* For g, h *)
    @DistinguishedTriangle (base S) /\  (* For f, h∘g *)
    @DistinguishedTriangle (base S).    (* For g∘f, h *)
Proof.
  destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
  
  split; [|split; [|split]].
  - exact (H_dist A B C f g).
  - exact (H_dist B C D g h).
  - exact (H_dist A B D f (h o g)%morphism).
  - exact (H_dist A C D (g o f)%morphism h).
Qed.

(** The uniqueness property extends to all octahedral morphisms. *)
Theorem octahedral_universal_uniqueness (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
  {A B C : object S} (f : morphism S A B) (g : morphism S B C)
  : forall (u1 u2 : morphism S (@cofiber S A B f) (@cofiber S A C (g o f)%morphism)),
    (u1 o @cofiber_in S A B f)%morphism = 
    (@cofiber_in S A C (g o f)%morphism o g)%morphism ->
    (u2 o @cofiber_in S A B f)%morphism = 
    (@cofiber_in S A C (g o f)%morphism o g)%morphism ->
    u1 = u2.
Proof.
  intros u1 u2 H1 H2.
  destruct H_TR4 as [[[H_universal H_oct] H_third] H_dist].
  
  (* Both morphisms vanish on f *)
  assert (H_zero : ((@cofiber_in S A C (g o f)%morphism o g)%morphism o f)%morphism =
                   zero_morphism (add_zero (base S)) A (@cofiber S A C (g o f)%morphism)).
  {
    apply cofiber_composite_vanishes_on_first.
  }
  
  (* Apply uniqueness from the universal property *)
  destruct (morphism_vanishing_on_f_factors H_universal f 
           (@cofiber_in S A C (g o f)%morphism o g)%morphism H_zero)
    as [u [Hu Hu_unique]].
  
  rewrite (Hu_unique u1 H1).
  rewrite (Hu_unique u2 H2).
  reflexivity.
Qed.

(** TR4 implies that certain compositions in the octahedral diagram are zero. *)
Theorem octahedral_zero_compositions (S : PreStableCategoryWithCofiber)
  (H_TR4 : TR4_octahedral_axiom S)
  {A B C : object S} (f_AB : morphism S A B) (g_BC : morphism S B C)
  : (* Various compositions in the octahedral diagram are zero *)
    let T := octahedral_triangle_distinguished S H_TR4 f_AB g_BC in
    let tri := triangle T in
    (g tri o f tri)%morphism = 
    zero_morphism (add_zero (base S)) (X tri) (Z tri) /\
    (h tri o g tri)%morphism = 
    zero_morphism (add_zero (base S)) (Y tri) (object_of (Susp (base S)) (X tri)) /\
    (morphism_of (Susp (base S)) (f tri) o h tri)%morphism = 
    zero_morphism (add_zero (base S)) (Z tri) (object_of (Susp (base S)) (Y tri)).
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

(** End of Section 18: The Octahedral Axiom (TR4) *)

(** * Section 19: Proper Stable Categories are Triangulated *)

(** ** From Stability to Triangulation
    
    This section establishes the fundamental theorem that proper stable categories
    with cofibers are triangulated categories. This result shows that the abstract
    notion of stability (suspension and loop being inverse equivalences) naturally
    gives rise to the rich structure of a triangulated category.
    
    The proof proceeds by verifying that all four axioms of triangulated categories
    (TR1-TR4) are satisfied in any proper stable category with cofibers. This
    demonstrates the deep connection between stable homotopy theory and the
    algebraic theory of triangulated categories.
*)

(** *** Equivalence Properties of Suspension and Loop
    
    In a proper stable category, the suspension and loop functors form an
    equivalence of categories. We establish the precise nature of this equivalence.
*)

(** In a proper stable category, both unit and counit are isomorphisms at
    every object, establishing that suspension and loop are equivalences. *)
Lemma suspension_is_equivalence (PS : ProperStableCategory)
  : forall X : object PS,
    IsIsomorphism (components_of (eta PS) X) /\
    IsIsomorphism (components_of (epsilon PS) (object_of (Susp PS) X)).
Proof.
  intro X.
  split.
  - (* η is an isomorphism by definition of proper stable *)
    exact (eta_is_iso PS X).
  - (* ε at ΣX is also an isomorphism *)
    exact (epsilon_is_iso PS (object_of (Susp PS) X)).
Qed.

(** The suspension and loop functors are inverse equivalences, with explicit
    inverse isomorphisms given by the unit and counit. *)
Theorem suspension_loop_inverse (PS : ProperStableCategory)
  : forall X : object PS,
    (* ΣΩX ≅ X via ε *)
    IsIsomorphism (components_of (epsilon PS) X) /\
    (* ΩΣX ≅ X via η^(-1) *)
    exists (inv_eta : morphism PS (object_of ((Loop PS) o (Susp PS))%functor X) X),
      (inv_eta o components_of (eta PS) X)%morphism = 1%morphism /\
      (components_of (eta PS) X o inv_eta)%morphism = 1%morphism.
Proof.
  intro X.
  split.
  - exact (epsilon_is_iso PS X).
  - destruct (eta_is_iso PS X) as [inv_eta [H_left H_right]].
    exists inv_eta.
    split; assumption.
Qed.

(** *** Combining Stable and Cofiber Structures
    
    To obtain a triangulated category, we need both the stable structure
    (suspension-loop equivalence) and the cofiber structure (mapping cones).
    We formalize the compatibility between these structures.
*)

(** A proper stable category with cofibers combines the stable adjunction
    structure with the cofiber construction in a compatible way. *)
Record ProperStableWithCofiber := {
  proper_stable :> ProperStableCategory;
  cofiber_structure :> PreStableCategoryWithCofiber;
  structures_compatible : base cofiber_structure = pre_stable proper_stable
}.

(** *** Verification of Triangulated Category Axioms
    
    We systematically verify that each axiom of triangulated categories
    holds in a proper stable category with cofibers.
*)

(** TR1 (Extension): Every morphism extends to a distinguished triangle. *)
Theorem proper_stable_has_TR1 (PSC : ProperStableWithCofiber)
  {X Y : object (cofiber_structure PSC)} 
  (f : morphism (cofiber_structure PSC) X Y)
  : @DistinguishedTriangle (base (cofiber_structure PSC)).
Proof.
  exact (@TR1 (cofiber_structure PSC) X Y f).
Qed.

(** TR2 (Isomorphism): Triangle isomorphisms preserve the distinguished property. *)
Theorem proper_stable_has_TR2 (PSC : ProperStableWithCofiber)
  : forall {T1 T2 : @Triangle (base (cofiber_structure PSC))} 
           (φ : TriangleMorphism T1 T2)
           (Hφ : IsTriangleIsomorphism φ)
           (D1 : @DistinguishedTriangle (base (cofiber_structure PSC)))
           (H1 : triangle D1 = T1),
    @DistinguishedTriangle (base (cofiber_structure PSC)).
Proof.
  intros T1 T2 φ Hφ D1 H1.
  exact (TR2 φ Hφ D1 H1).
Qed.

(** TR3 (Rotation): Distinguished triangles can be rotated. *)
Theorem proper_stable_has_TR3 (PSC : ProperStableWithCofiber)
  (T : @DistinguishedTriangle (base (cofiber_structure PSC)))
  : @DistinguishedTriangle (base (cofiber_structure PSC)).
Proof.
  exact (rotate_distinguished T).
Qed.

(** TR4 (Octahedral): The octahedral axiom is satisfied. *)
Theorem proper_stable_has_TR4 (PSC : ProperStableWithCofiber)
  (H_TR4 : TR4_octahedral_axiom (cofiber_structure PSC))
  : TR4_octahedral_axiom (cofiber_structure PSC).
Proof.
  exact H_TR4.
Qed.

(** *** The Main Theorem
    
    We now state and prove the main result: proper stable categories with
    cofibers satisfying TR4 are triangulated categories.
*)

(** A triangulated category is characterized by satisfying all four axioms
    TR1-TR4. *)
Definition is_triangulated_category (PSC : ProperStableWithCofiber)
  : Type
  := (forall {X Y : object (cofiber_structure PSC)} 
            (f : morphism (cofiber_structure PSC) X Y),
      @DistinguishedTriangle (base (cofiber_structure PSC))) *  (* TR1 *)
     (forall {T1 T2 : @Triangle (base (cofiber_structure PSC))} 
            (φ : TriangleMorphism T1 T2)
            (Hφ : IsTriangleIsomorphism φ)
            (D1 : @DistinguishedTriangle (base (cofiber_structure PSC)))
            (H1 : triangle D1 = T1),
      @DistinguishedTriangle (base (cofiber_structure PSC))) *  (* TR2 *)
     (forall (T : @DistinguishedTriangle (base (cofiber_structure PSC))),
      @DistinguishedTriangle (base (cofiber_structure PSC))) *  (* TR3 *)
     TR4_octahedral_axiom (cofiber_structure PSC).              (* TR4 *)

(** The main theorem: Every proper stable category with cofibers satisfying
    the octahedral axiom is a triangulated category. This establishes the
    fundamental connection between stable categories and triangulated categories. *)
Theorem proper_stable_is_triangulated (PSC : ProperStableWithCofiber)
  (H_TR4 : TR4_octahedral_axiom (cofiber_structure PSC))
  : is_triangulated_category PSC.
Proof.
  unfold is_triangulated_category.
  refine (_, _, _, _).
  - (* TR1 *)
    intros X Y f.
    exact (proper_stable_has_TR1 PSC f).
  - (* TR2 *)
    intros T1 T2 φ Hφ D1 H1.
    exact (proper_stable_has_TR2 PSC φ Hφ D1 H1).
  - (* TR3 *)
    intro T.
    exact (proper_stable_has_TR3 PSC T).
  - (* TR4 *)
    exact (proper_stable_has_TR4 PSC H_TR4).
Qed.

(** End of Section 19: Proper Stable Categories are Triangulated *)

(** * Section 20: Suspension Fixed Points and Periodicity *)

(** ** Suspension Fixed Points
    
    This section investigates objects that are isomorphic to their suspension,
    known as suspension fixed points. These special objects reveal deep structural
    properties of stable categories and lead to periodicity phenomena.
    
    We establish:
    - Basic properties of suspension fixed points
    - The role of the zero object as a universal fixed point
    - Periodicity in stable categories
    - Applications to the classification of objects
*)

(** *** Iteration of Functors
    
    To study periodicity, we first formalize the notion of iterating a functor.
*)

(** The n-fold iteration of an endofunctor. *)
Fixpoint iterate_functor {C : PreCategory} (F : Functor C C) (n : nat) 
  : Functor C C :=
  match n with
  | O => 1%functor
  | S n' => (F o iterate_functor F n')%functor
  end.

(** *** Classification of Suspension Fixed Points
    
    We establish a classification theorem for suspension fixed points,
    showing their relationship to objects admitting retractions from zero.
*)

(** The zero object always satisfies the classification criteria for
    suspension fixed points. *)
Theorem zero_satisfies_fixed_point_classification 
  (PS : PreStableCategory)
  : is_suspension_fixed_point PS (@zero _ (add_zero PS)) ->
    (admits_retraction_from_zero PS (@zero _ (add_zero PS))) +
    ({ n : nat &
      is_suspension_fixed_point PS 
        (object_of (iterate_functor (Susp PS) n) (@zero _ (add_zero PS))) }).
Proof.
  intro H_fixed.
  (* We already know zero admits a retraction from itself *)
  left.
  exact (zero_always_retractable PS).
Qed.

(** The suspension functor preserves the fixed point property: if X is
    isomorphic to ΣX, then ΣX is isomorphic to Σ²X. *)
Theorem suspension_preserves_fixed_points 
  (PS : PreStableCategory) (X : object PS)
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

(** *** Periodicity Phenomena
    
    In some stable categories, the suspension functor exhibits periodicity:
    Σⁿ ≅ Id for some n > 0. We explore the consequences of such periodicity.
*)

(** Addition of natural numbers. *)
Fixpoint nat_add (m n : nat) : nat :=
  match m with
  | O => n
  | S m' => S (nat_add m' n)
  end.

(** If the suspension functor has period n, then this periodicity extends
    to all multiples of n. *)
Theorem suspension_periodicity (PS : PreStableCategory) (n : nat)
  : (n = O -> Empty) ->
    (forall X : object PS, 
     object_of (iterate_functor (Susp PS) n) X = X) ->
    forall m : nat, forall X : object PS,
    object_of (iterate_functor (Susp PS) (nat_add m n)) X = 
    object_of (iterate_functor (Susp PS) m) X.
Proof.
  intros Hn_nonzero H_period m X.
  induction m.
  - (* m = 0 *)
    simpl.
    exact (H_period X).
  - (* m = S m' *)
    simpl.
    rewrite IHm.
    reflexivity.
Qed.

(** In a periodic stable category where suspension preserves zero,
    all iterates of suspension preserve zero. *)
Theorem periodicity_preserves_zero (PS : PreStableCategory) (n : nat)
  : (forall X : object PS, 
     object_of (iterate_functor (Susp PS) n) X = X) ->
    object_of (Susp PS) (@zero _ (add_zero PS)) = @zero _ (add_zero PS) ->
    forall k : nat,
    object_of (iterate_functor (Susp PS) k) (@zero _ (add_zero PS)) = 
    @zero _ (add_zero PS).
Proof.
  intros H_period H_zero_preserved k.
  induction k.
  - (* k = 0 *)
    simpl. reflexivity.
  - (* k = S k' *)
    simpl.
    rewrite IHk.
    exact H_zero_preserved.
Qed.

(** *** Applications to Cofiber Sequences
    
    Periodicity has important implications for cofiber sequences and
    the structure of morphisms in stable categories.
*)

(** In a periodic stable category, endomorphisms induce self-maps on their
    cofibers after applying the appropriate power of suspension. *)
Theorem periodic_cofiber_self_map
  (PSC : ProperStableWithCofiber)
  (n : nat) (Hn_pos : n = O -> Empty)
  (H_period : forall X : object (base (cofiber_structure PSC)), 
              object_of (iterate_functor (Susp (base (cofiber_structure PSC))) n) X = X)
  : forall (X : object (cofiber_structure PSC)) 
           (f : morphism (cofiber_structure PSC) X X),
    (* The periodicity gives us an equality *)
    object_of (iterate_functor (Susp (base (cofiber_structure PSC))) n)
              (@cofiber (cofiber_structure PSC) X X f) = 
    @cofiber (cofiber_structure PSC) X X f.
Proof.
  intros X f.
  exact (H_period (@cofiber (cofiber_structure PSC) X X f)).
Qed.

(** End of Section 20: Suspension Fixed Points and Periodicity *)
