(** * Definition of a [PreCategory] *)
Require Export Overture Basics.Notations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Declare Scope morphism_scope.
Declare Scope category_scope.
Declare Scope object_scope.

Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Local Open Scope morphism_scope.

(** Quoting the HoTT Book: *)
(** Definition 9.1.1. A precategory [A] consists of the following.

    (i) A type [A₀] of objects. We write [a : A] for [a : A₀].

    (ii) For each [a, b : A], a set [hom_A(a, b)] of arrows or morphisms.

    (iii) For each [a : A], a morphism [1ₐ : hom_A(a, a)].

    (iv) For each [a, b, c : A], a function

         [hom_A(b, c) → hom_A(a, b) → hom_A(a, c)]

         denoted infix by [g ↦ f ↦ g ∘ f] , or sometimes simply by [g f].

    (v) For each [a, b : A] and [f : hom_A(a, b)], we have [f = 1_b ∘
        f] and [f = f ∘ 1ₐ].

    (vi) For each [a, b, c, d : A] and [f : hom_A(a, b)], [g :
         hom_A(b, c)], [h : hom_A(c,d)], we have [h ∘ (g ∘ f) = (h ∘
         g) ∘ f]. *)
(** In addition to these laws, we ask for a few redundant laws to give
    us more judgmental equalities.  For example, since [(p^)^ ≢ p] for
    paths [p], we ask for the symmetrized version of the associativity
    law, so we can swap them when we take the dual. *)

Record PreCategory :=
  Build_PreCategory' {
      object :> Type;
      morphism : object -> object -> Type;

      identity : forall x, morphism x x;
      compose : forall s d d',
                  morphism d d'
                  -> morphism s d
                  -> morphism s d'
                              where "f 'o' g" := (compose f g);

      associativity : forall x1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
                        (m3 o m2) o m1 = m3 o (m2 o m1);
      (** Ask for the symmetrized version of [associativity], so that [(Cᵒᵖ)ᵒᵖ] and [C] are equal without [Funext] *)
      associativity_sym : forall x1 x2 x3 x4
                                 (m1 : morphism x1 x2)
                                 (m2 : morphism x2 x3)
                                 (m3 : morphism x3 x4),
                            m3 o (m2 o m1) = (m3 o m2) o m1;

      left_identity : forall a b (f : morphism a b), identity b o f = f;
      right_identity : forall a b (f : morphism a b), f o identity a = f;
      (** Ask for the double-identity version so that [InitialTerminalCategory.Functors.from_terminal Cᵒᵖ X] and [(InitialTerminalCategory.Functors.from_terminal C X)ᵒᵖ] are convertible. *)
      identity_identity : forall x, identity x o identity x = identity x;

      trunc_morphism : forall s d, IsHSet (morphism s d)
    }.

Bind Scope category_scope with PreCategory.
Bind Scope object_scope with object.
Bind Scope morphism_scope with morphism.

(** We want eta-expanded primitive projections to [simpl] away. *)
Arguments object !C%category / : rename.
Arguments morphism !C%category / s d : rename.
Arguments identity {!C%category} / x%object : rename.
Arguments compose {!C%category} / {s d d'}%object (m1 m2)%morphism : rename.

Local Infix "o" := compose : morphism_scope.
(** Perhaps we should consider making this notation more global. *)
(** Perhaps we should pre-reserve all of the notations. *)
Local Notation "x --> y" := (morphism _ x y) : type_scope.
Local Notation "1" := (identity _) : morphism_scope.

(** Define a convenience wrapper for building a precategory without
    specifying the redundant proofs. *)
Definition Build_PreCategory
           object morphism identity compose
           associativity left_identity right_identity
  := @Build_PreCategory'
       object
       morphism
       identity
       compose
       associativity
       (fun _ _ _ _ _ _ _ => symmetry _ _ (associativity _ _ _ _ _ _ _))
       left_identity
       right_identity
       (fun _ => left_identity _ _ _).

Global Existing Instance trunc_morphism.

(** create a hint db for all category theory things *)
Create HintDb category discriminated.
(** create a hint db for morphisms in categories *)
Create HintDb morphism discriminated.

Hint Resolve @left_identity @right_identity @associativity : category morphism.
Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : morphism.

(** ** Simple laws about the identity morphism *)
Section identity_unique.
  Variable C : PreCategory.

  (** The identity morphism is unique. *)
  Lemma identity_unique (id0 id1 : forall x, morphism C x x)
        (id1_left : forall s d (m : morphism C s d), id1 _ o m = m)
        (id0_right : forall s d (m : morphism C s d), m o id0 _ = m)
  : id0 == id1.
  Proof.
    intro.
    etransitivity;
      [ symmetry; apply id1_left
      | apply id0_right ].
  Qed.

  (** Anything equal to the identity acts like it.  This is obvious,
      but useful as a helper lemma for automation. *)
  Definition concat_left_identity s d (m : morphism C s d) i
  : i = 1 -> i o m = m
    := fun H => (ap10 (ap _ H) _ @ left_identity _ _ _ m)%path.

  Definition concat_right_identity s d (m : morphism C s d) i
  : i = 1 -> m o i = m
    := fun H => (ap _ H @ right_identity _ _ _ m)%path.
End identity_unique.

(** Make a separate module for Notations, which can be exported/imported separately. *)
Module Export CategoryCoreNotations.
  Infix "o" := compose : morphism_scope.
  (** Perhaps we should consider making this notation more global. *)
  (** Perhaps we should pre-reserve all of the notations. *)
  Local Notation "x --> y" := (@morphism _ x y) : type_scope.
  Local Notation "x --> y" := (morphism _ x y) : type_scope.
  Notation "1" := (identity _) : morphism_scope.
End CategoryCoreNotations.

(** We have a tactic for trying to run a tactic after associating morphisms either all the way to the left, or all the way to the right *)
Tactic Notation "try_associativity_quick" tactic(tac) :=
  first [ rewrite <- ?associativity; tac
        | rewrite -> ?associativity; tac ].
