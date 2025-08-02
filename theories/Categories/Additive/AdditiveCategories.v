(** * Additive categories

    Categories enriched over abelian groups with zero objects and biproducts.
*)

From HoTT Require Import Basics Types.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories.Additive Require Import ZeroObjects Biproducts.

(** * Additive categories *)

(** ** Definition
    
    An additive category has a zero object and biproducts for all pairs
    of objects. This is a key step toward abelian categories.
*)

Class AdditiveCategory := {
  cat : PreCategory;
  add_zero :: ZeroObject cat;
  add_biproduct : forall (X Y : object cat), Biproduct X Y;
  
  (** Addition of morphisms *)
  add_morphism : forall {X Y : object cat}, 
    morphism cat X Y -> morphism cat X Y -> morphism cat X Y;
  
  (** Addition is associative *)
  add_morphism_assoc : forall {X Y : object cat} (f g h : morphism cat X Y),
    add_morphism (add_morphism f g) h = add_morphism f (add_morphism g h);
  
  (** Addition is commutative *)
  add_morphism_comm : forall {X Y : object cat} (f g : morphism cat X Y),
    add_morphism f g = add_morphism g f;
    
  (** Zero morphism is the additive identity (left) *)
  add_morphism_zero_l : forall {X Y : object cat} (f : morphism cat X Y),
    add_morphism (@zero_morphism cat add_zero X Y) f = f;
    
  (** Zero morphism is the additive identity (right) *)
  add_morphism_zero_r : forall {X Y : object cat} (f : morphism cat X Y),
    add_morphism f (@zero_morphism cat add_zero X Y) = f;
    
  (** Every morphism has an additive inverse *)
  add_morphism_inverse : forall {X Y : object cat} (f : morphism cat X Y),
    {g : morphism cat X Y & 
     add_morphism f g = @zero_morphism cat add_zero X Y};
     
  (** Composition is bilinear - left distributivity *)
  composition_bilinear_l : forall {X Y Z : object cat} 
    (f g : morphism cat X Y) (h : morphism cat Y Z),
    (h o add_morphism f g)%morphism = 
    add_morphism (h o f) (h o g);

  (** Composition is bilinear - right distributivity *)  
  composition_bilinear_r : forall {X Y Z : object cat}
    (f : morphism cat X Y) (g h : morphism cat Y Z),
    (add_morphism g h o f)%morphism = 
    add_morphism (g o f) (h o f);
    
  (** Addition via biproducts axiom *)
  addition_via_biproduct_axiom : forall {X Y : object cat} (f g : morphism cat X Y),
    add_morphism f g = 
    (biproduct_coprod_mor (add_biproduct Y Y) Y 1%morphism 1%morphism o
     biproduct_prod_mor (add_biproduct Y Y) 
       (biproduct_obj (biproduct_data (add_biproduct X X)))
       (f o outl (biproduct_data (add_biproduct X X)))
       (g o outr (biproduct_data (add_biproduct X X))) o
     biproduct_prod_mor (add_biproduct X X) X 1%morphism 1%morphism)%morphism
}.

Coercion cat : AdditiveCategory >-> PreCategory.

(** ** Helper functions *)

(** Access the zero object. *)
Definition zero_obj (A : AdditiveCategory) : object A
  := @zero A add_zero.

(** Zero morphism in an additive category. *)
Definition add_zero_morphism (A : AdditiveCategory) (X Y : object A)
  : morphism A X Y
  := @zero_morphism A add_zero X Y.

(** Helper functions to access biproduct components. *)
Definition add_biproduct_data (A : AdditiveCategory) (X Y : object A)
  : BiproductData X Y
  := biproduct_data (@add_biproduct A X Y).

Definition add_biproduct_obj (A : AdditiveCategory) (X Y : object A)
  : object A
  := biproduct_obj (add_biproduct_data A X Y).

(** Notation for biproduct object. *)
Notation "X ⊕ Y" := (add_biproduct_obj _ X Y) 
  (at level 40, left associativity).

(** Biproduct injections. *)
Definition add_inl {A : AdditiveCategory} {X Y : object A}
  : morphism A X (X ⊕ Y)
  := inl (add_biproduct_data A X Y).

Definition add_inr {A : AdditiveCategory} {X Y : object A}
  : morphism A Y (X ⊕ Y)
  := inr (add_biproduct_data A X Y).

(** Biproduct projections. *)
Definition add_outl {A : AdditiveCategory} {X Y : object A}
  : morphism A (X ⊕ Y) X
  := outl (add_biproduct_data A X Y).

Definition add_outr {A : AdditiveCategory} {X Y : object A}
  : morphism A (X ⊕ Y) Y
  := outr (add_biproduct_data A X Y).

(** ** Universal property operations *)

Section AdditiveOperations.
  Context (A : AdditiveCategory).
  
  (** Universal property of biproducts as coproducts. *)
  Definition add_coprod_mor {X Y Z : object A}
    (f : morphism A X Z) (g : morphism A Y Z)
    : morphism A (X ⊕ Y) Z
    := biproduct_coprod_mor (@add_biproduct A X Y) Z f g.

  Definition add_coprod_unique {X Y Z : object A}
    (f : morphism A X Z) (g : morphism A Y Z)
    (h : morphism A (X ⊕ Y) Z)
    (Hl : (h o add_inl = f)%morphism)
    (Hr : (h o add_inr = g)%morphism)
    : h = add_coprod_mor f g
    := @biproduct_coprod_unique A add_zero X Y 
         (@add_biproduct A X Y) Z f g h Hl Hr.
    
  (** Universal property of biproducts as products. *)
  Definition add_prod_mor {X Y Z : object A}
    (f : morphism A Z X) (g : morphism A Z Y)
    : morphism A Z (X ⊕ Y)
    := biproduct_prod_mor (@add_biproduct A X Y) Z f g.

  Definition add_prod_unique {X Y Z : object A}
    (f : morphism A Z X) (g : morphism A Z Y)
    (h : morphism A Z (X ⊕ Y))
    (Hl : (add_outl o h = f)%morphism)
    (Hr : (add_outr o h = g)%morphism)
    : h = add_prod_mor f g.
  Proof.
    unfold add_prod_mor.
    set (B := @add_biproduct A X Y).
    set (c := @center _ (prod_universal (biproduct_universal B) Z f g)).
    assert (p : (h; (Hl, Hr)) = c).
    1: apply (@path_contr _ 
                (prod_universal (biproduct_universal B) Z f g)).
    exact (ap pr1 p).
  Qed.

End AdditiveOperations.

(** ** Relationship between addition and biproducts *)

Section AdditionViaBiproducts.
  Context (A : AdditiveCategory).
  
  (** The diagonal morphism. *)
  Definition diagonal {X : object A} : morphism A X (X ⊕ X)
    := biproduct_prod_mor (@add_biproduct A X X) X 
         (1%morphism : morphism A X X) 
         (1%morphism : morphism A X X).
  
  (** The codiagonal morphism. *)
  Definition codiagonal {X : object A} : morphism A (X ⊕ X) X
    := biproduct_coprod_mor (@add_biproduct A X X) X 
         (1%morphism : morphism A X X) 
         (1%morphism : morphism A X X).
  
  (** The biproduct morphism induced by two morphisms. *)
  Definition biproduct_mor {W X Y Z : object A}
    (f : morphism A W Y) (g : morphism A X Z)
    : morphism A (W ⊕ X) (Y ⊕ Z)
    := biproduct_prod_mor (@add_biproduct A Y Z) (W ⊕ X)
         (f o add_outl) 
         (g o add_outr).
  
  (** Addition can be expressed using biproducts. *)
  Theorem addition_via_biproducts {X Y : object A} 
    (f g : morphism A X Y)
    : add_morphism f g = (@codiagonal Y o biproduct_mor f g o @diagonal X)%morphism.
  Proof.
    unfold codiagonal, diagonal, biproduct_mor.
    apply addition_via_biproduct_axiom.
  Qed.
  
End AdditionViaBiproducts.

(** * Additive functors *)

(** ** Definition
    
    An additive functor preserves the additive structure: zero objects,
    biproducts, and morphism addition.
*)

Record AdditiveFunctor (A B : AdditiveCategory) := {
  add_functor :> Functor A B;
  
  preserves_zero : 
    object_of add_functor (zero_obj A) = zero_obj B;
  
  preserves_biproduct : forall (X Y : object A),
    object_of add_functor (X ⊕ Y) =
    (object_of add_functor X ⊕ object_of add_functor Y);
    
  (** Additive functors preserve addition of morphisms *)
  preserves_addition : forall {X Y : object A} (f g : morphism A X Y),
    morphism_of add_functor (add_morphism f g) = 
    add_morphism (morphism_of add_functor f) 
                 (morphism_of add_functor g)
}.

(** ** Properties of additive functors *)

Section AdditiveFunctorProperties.
  Context (A B : AdditiveCategory) (F : AdditiveFunctor A B).

  (** Helper lemmas for preservation properties. *)
  
  (** Additive functors preserve initial morphisms. *)
  Local Lemma functor_preserves_initial_morphism (Y : object A)
    : transport (fun W => morphism B W (object_of F Y)) 
                (@preserves_zero A B F)
                (morphism_of F 
                  (@morphism_from_initial A 
                    (initialobject_zeroobject (@add_zero A)) Y)) =
      @morphism_from_initial B 
        (initialobject_zeroobject (@add_zero B)) 
        (object_of F Y).
  Proof.
    rapply path_contr.
  Qed.
  
  (** Additive functors preserve terminal morphisms. *)
  Local Lemma functor_preserves_terminal_morphism (X : object A)
    : transport (fun W => morphism B (object_of F X) W) 
                (@preserves_zero A B F)
                (morphism_of F 
                  (@morphism_to_terminal A 
                    (terminalobject_zeroobject (@add_zero A)) X)) =
      @morphism_to_terminal B 
        (terminalobject_zeroobject (@add_zero B)) 
        (object_of F X).
  Proof.
    rapply path_contr.
  Qed.
  
  (** Transporting morphisms across an equality. *)
  Local Lemma transport_morphism_compose {C : PreCategory} 
    {W X Y Z : C} (p : W = X) 
    (f : morphism C Y W) (g : morphism C W Z)
    : transport (fun U => morphism C Y Z) p (g o f)%morphism =
      (transport (fun U => morphism C U Z) p g o 
       transport (fun U => morphism C Y U) p f)%morphism.
  Proof.
    destruct p. reflexivity.
  Qed.
  
  (** F preserves the zero morphism components. *)
  Local Lemma F_preserves_zero_morphism_factorization (X Y : object A)
    : morphism_of F (add_zero_morphism A X Y) =
      (morphism_of F 
        (@morphism_from_initial A 
          (initialobject_zeroobject (@add_zero A)) Y) o
       morphism_of F 
        (@morphism_to_terminal A 
          (terminalobject_zeroobject (@add_zero A)) X))%morphism.
  Proof.
    unfold add_zero_morphism, zero_morphism.
    apply composition_of.
  Qed.
  
  (** F preserves composition through zero. *)
  Local Lemma F_preserves_composition_through_zero (X Y : object A)
    : (morphism_of F 
        (@morphism_from_initial A 
          (initialobject_zeroobject (@add_zero A)) Y) o
       morphism_of F 
        (@morphism_to_terminal A 
          (terminalobject_zeroobject (@add_zero A)) X))%morphism =
      (@morphism_from_initial B 
        (initialobject_zeroobject (@add_zero B)) (object_of F Y) o
       @morphism_to_terminal B 
        (terminalobject_zeroobject (@add_zero B)) (object_of F X))%morphism.
  Proof.
    set (p := @preserves_zero A B F).
    symmetry.
    transitivity 
      ((transport (fun W => morphism B W (object_of F Y)) p
         (morphism_of F 
           (@morphism_from_initial A 
             (initialobject_zeroobject (@add_zero A)) Y)) o
        transport (fun W => morphism B (object_of F X) W) p
         (morphism_of F 
           (@morphism_to_terminal A 
             (terminalobject_zeroobject (@add_zero A)) X)))%morphism).
    2: apply transport_compose_middle.
    apply ap011.
    - symmetry. exact (functor_preserves_initial_morphism Y).
    - symmetry. exact (functor_preserves_terminal_morphism X).
  Qed.
  
  (** ** Main theorem: additive functors preserve zero morphisms *)
  
  Theorem additive_functor_preserves_zero_morphisms (X Y : object A)
    : morphism_of F (add_zero_morphism A X Y) = 
      add_zero_morphism B (object_of F X) (object_of F Y).
  Proof.
    rewrite F_preserves_zero_morphism_factorization.
    unfold add_zero_morphism, zero_morphism.
    exact (F_preserves_composition_through_zero X Y).
  Qed.
  
End AdditiveFunctorProperties.

(** * Examples and constructions *)

(** The identity functor is additive. *)
Definition id_additive_functor (A : AdditiveCategory) 
  : AdditiveFunctor A A
  := {|
    add_functor := 1%functor;
    preserves_zero := idpath;
    preserves_biproduct := fun X Y => idpath;
    preserves_addition := fun X Y f g => idpath
  |}.
  
(** Composition of additive functors is additive. *)
Definition compose_additive_functors {A B C : AdditiveCategory}
  (G : AdditiveFunctor B C) (F : AdditiveFunctor A B)
  : AdditiveFunctor A C.
Proof.
  refine {|
    add_functor := (G o F)%functor;
    preserves_zero := 
      ap (object_of G) (@preserves_zero A B F) @ 
      (@preserves_zero B C G);
    preserves_biproduct := fun X Y => 
      ap (object_of G) (@preserves_biproduct A B F X Y) @ 
      @preserves_biproduct B C G (object_of F X) (object_of F Y);
    preserves_addition := _
  |}.
  intros X Y f g.
  simpl.
  rewrite (@preserves_addition A B F X Y f g).
  apply (@preserves_addition B C G (object_of F X) (object_of F Y)).
Defined.

(** * Export hints *)

Hint Rewrite 
  @additive_functor_preserves_zero_morphisms
  : additive_simplify.
      
