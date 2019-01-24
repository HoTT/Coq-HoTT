(** * Pseudofunctors *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import FunctorCategory.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import Functor.Composition.Core Functor.Identity.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import NaturalTransformation.Isomorphisms.
Require Import NaturalTransformation.Paths.
Require Import FunctorCategory.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section pseudofunctor.
  Local Open Scope natural_transformation_scope.
  Context `{Funext}.

  Variable C : PreCategory.

  (** Quoting from nCatLab (http://ncatlab.org/nlab/show/pseudofunctor):

      Given bicategories [C] and [D], a pseudofunctor (or weak 2-functor,
      or just functor) [P : C → D] consists of:

      - for each object [x] of [C], an object [P_x] of [D];

      - for each hom-category [C(x,y)] in [C], a functor [P_{x,y} :
        C(x,y) → D(P_x, P_y)];

      - for each object [x] of [C], an invertible 2-morphism (2-cell)
        [P_{id_x} : id_{P_x} ⇒ P_{x,x}(id_x)];

      - for each triple [x],[y],[z] of [C]-objects, a isomorphism
        (natural in [f : x → y] and [g : y → z]) [P_{x,y,z}(f,g) :
        P_{x,y}(f);P_{y,z}(g) ⇒ P_{x,z}(f;g)];

      - for each hom-category [C(x,y)],
<<
                                    id_{Pₓ} ; P_{x, y}(f)
                                      //              \\
                                    //                  \\
        P_{idₓ} ; id_{P_{x,y}(f)} //                      \\  λ_{P_{x,y}(f)}
                                //                          \\
                               ⇙                              ⇘
              Pₓ,ₓ(idₓ) ; P_{x,y}(f)                       P_{x,y}(f)
                               \\                             ⇗
                                 \\                         //
                P_{x,x,y}(idₓ, f)  \\                     // P_{x,y}(λ_f)
                                     \\                 //
                                       ⇘              //
                                        P_{x,y}(idₓ ; f)
>>

        and

<<
                                    P_{x, y}(f) ; id_{P_y}
                                      //              \\
                                    //                  \\
       id_{P_{x,y}(f)} ; P_{id_y} //                      \\  ρ_{P_{x,y}(f)}
                                //                          \\
                               ⇙                              ⇘
              P_{x,y}(f) ; P_{y,y}(id_y)                   P_{x,y}(f)
                               \\                             ⇗
                                 \\                         //
                P_{x,y,y}(f, id_y) \\                     // P_{x,y}(ρ_f)
                                     \\                 //
                                       ⇘              //
                                       P_{x,y}(f ; id_y)
>>
        commute; and

      - for each quadruple [w],[x],[y],[z] of [C]-objects,
<<
                                                  α_{P_{w,x}(f),P_{x,y}(g),P_{y,z}(h)}
        (P_{w,x}(f) ; P_{x,y}(g)) ; P_{y,z}(h) ========================================⇒ P_{w,x}(f) ; (P_{x,y}(g) ; P_{y,z}(h))
                                         ∥                                                   ∥
                                         ∥                                                   ∥
        P_{w,x,y}(f,g) ; id_{P_{y,z}(h)} ∥                                                   ∥ id_{P_{w,x}(f)} ; P_{x,y,z}(g, h)
                                         ∥                                                   ∥
                                         ⇓                                                   ⇓
                   P_{w,y}(f ; g) ; P_{y,z}(h)                                           P_{w,x}(f) ; P_{x,z}(g ; h)
                                         ∥                                                   ∥
                                         ∥                                                   ∥
                     P_{w,y,z}(f ; g, h) ∥                                                   ∥ P_{w,x,z}(f, g ; h)
                                         ∥                                                   ∥
                                         ⇓                                                   ⇓
                          P_{w,z}((f ; g) ; h) ========================================⇒ P_{w,z}(f ; (g ; h))
                                                          P_{w,z}(α_{f,g,h})
>>
        commutes.
*)

  (* To obtain the [p_composition_of_coherent] type, I ran
<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (w x y z : C) (f : morphism C w x) (g : morphism C x y) (h : morphism C y z), Type.
  Proof.
    intros.
    pose ((idtoiso (_ -> _) (ap (p_morphism_of F w z) (associativity C _ _ _ _ f g h))) : morphism _ _ _).
    pose ((p_composition_of F w y z h (g ∘ f)) : NaturalTransformation _ _).
    pose (p_morphism_of F y z h ∘ p_composition_of F w x y g f).

    pose (associator_1 (p_morphism_of F y z h) (p_morphism_of F x y g) (p_morphism_of F w x f)).
    pose (p_composition_of F x y z h g ∘ p_morphism_of F w x f).
    pose ((p_composition_of F w x z (h ∘ g) f) : NaturalTransformation _ _).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>

<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (x y : C) (f : morphism C x y), Type.
  Proof.
    intros.
    pose (p_identity_of F y ∘ p_morphism_of F x y f).
    pose (p_composition_of F x y y (Identity y) f : NaturalTransformation _ _).
    pose (idtoiso (_ -> _) (ap (p_morphism_of F x y) (left_identity _ _ _ f)) : morphism _ _ _).
    pose (left_identity_natural_transformation_2 (p_morphism_of F x y f)).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>

<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (x y : C) (f : morphism C x y), Type.
  Proof.
    intros.
    pose (p_morphism_of F x y f ∘ p_identity_of F x).
    pose (p_composition_of F x x y f (Identity x) : NaturalTransformation _ _).
    pose (idtoiso (_ -> _) (ap (p_morphism_of F x y) (right_identity _ _ _ f)) : morphism _ _ _).
    pose (right_identity_natural_transformation_2 (p_morphism_of F x y f)).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>
 *)

  Record Pseudofunctor :=
    {
      p_object_of :> C -> PreCategory;
      p_morphism_of : forall s d, morphism C s d
                                  -> Functor (p_object_of s) (p_object_of d);
      p_composition_of : forall s d d'
                                (m1 : morphism C d d') (m2 : morphism C s d),
                           (p_morphism_of _ _ (m1 o m2))
                             <~=~> (p_morphism_of _ _ m1 o p_morphism_of _ _ m2)%functor;
      p_identity_of : forall x, p_morphism_of x x 1 <~=~> 1%functor;
      p_composition_of_coherent
      : forall w x y z
               (f : morphism C w x) (g : morphism C x y) (h : morphism C y z),
          ((associator_1 (p_morphism_of y z h) (p_morphism_of x y g) (p_morphism_of w x f))
             o ((p_composition_of x y z h g oR p_morphism_of w x f)
                  o (p_composition_of w x z (h o g) f)))
          = ((p_morphism_of y z h oL p_composition_of w x y g f)
               o ((p_composition_of w y z h (g o f))
                    o (Category.Morphisms.idtoiso (_ -> _) (ap (p_morphism_of w z) (Category.Core.associativity C w x y z f g h)) : morphism _ _ _)));
      p_left_identity_of_coherent
      : forall x y (f : morphism C x y),
          ((p_identity_of y oR p_morphism_of x y f)
             o p_composition_of x y y 1 f)
          = ((left_identity_natural_transformation_2 (p_morphism_of x y f))
               o (Category.Morphisms.idtoiso (_ -> _) (ap (p_morphism_of x y) (Category.Core.left_identity C x y f)) : morphism _ _ _));
      p_right_identity_of_coherent
      : forall x y (f : morphism C x y),
          ((p_morphism_of x y f oL p_identity_of x)
             o p_composition_of x x y f 1)
          = ((right_identity_natural_transformation_2 (p_morphism_of x y f))
               o (Category.Morphisms.idtoiso (_ -> _) (ap (p_morphism_of x y) (Category.Core.right_identity C x y f)) : morphism _ _ _))
    }.
End pseudofunctor.

Declare Scope pseudofunctor_scope.
Delimit Scope pseudofunctor_scope with pseudofunctor.
Bind Scope pseudofunctor_scope with Pseudofunctor.

Create HintDb pseudofunctor discriminated.

Arguments p_object_of {_} {C%category} F%pseudofunctor / c%object : rename.
Arguments p_morphism_of {_} {C%category} F%pseudofunctor / {s d}%object m%morphism : rename.

(*Notation "F ₀ x" := (p_object_of F x) : object_scope.
Notation "F ₁ m" := (p_morphism_of F m) : morphism_scope.*)
