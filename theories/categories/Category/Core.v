Require Export Overture.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Local Open Scope morphism_scope.

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
      (** Ask for the symmetrized version of [associativity], so that [(C^op)^op] and [C] are equal without [Funext] *)
      associativity_sym : forall x1 x2 x3 x4
                                 (m1 : morphism x1 x2)
                                 (m2 : morphism x2 x3)
                                 (m3 : morphism x3 x4),
                            m3 o (m2 o m1) = (m3 o m2) o m1;

      left_identity : forall a b (f : morphism a b), identity b o f = f;
      right_identity : forall a b (f : morphism a b), f o identity a = f;
      (** Ask for the double-identity version so that [FunctorFromTerminal C^op X] and [(FunctorFromTerminal C X)^op] are convertible. *)
      identity_identity : forall x, identity x o identity x = identity x;

      trunc_morphism : forall s d, IsHSet (morphism s d)
    }.

Bind Scope category_scope with PreCategory.
Bind Scope object_scope with object.
Bind Scope morphism_scope with morphism.

Arguments object C%category : rename.
Arguments morphism !C%category s d : rename.
Arguments identity [!C%category] x%object : rename.
Arguments compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Local Infix "o" := compose : morphism_scope.
(** Perhaps we should consider making this notation more global. *)
(** Perhaps we should pre-reserve all of the notations. *)
Local Notation "x --> y" := (@morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Local Notation "1" := (identity _) : morphism_scope.

Definition Build_PreCategory
           object morphism compose identity
           associativity left_identity right_identity
  := @Build_PreCategory'
       object
       morphism
       compose
       identity
       associativity
       (fun _ _ _ _ _ _ _ => symmetry _ _ (associativity _ _ _ _ _ _ _))
       left_identity
       right_identity
       (fun _ => left_identity _ _ _).

Existing Instance trunc_morphism.

(** create a hint db for all category theory things *)
Create HintDb category discriminated.
(** create a hint db for morphisms in categories *)
Create HintDb morphism discriminated.

Hint Resolve @left_identity @right_identity @associativity : category morphism.
Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : morphism.

Section identity_unique.
  Variable C : PreCategory.

  (** The identity morphism is uniuqe. *)
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
Module Export Notations.
  Infix "o" := compose : morphism_scope.
  (** Perhaps we should consider making this notation more global. *)
  (** Perhaps we should pre-reserve all of the notations. *)
  Local Notation "x --> y" := (@morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Notation "1" := (identity _) : morphism_scope.
End Notations.
