(** * Definition of a functor *)
Require Import Category.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Delimit Scope functor_scope with functor.

Local Open Scope morphism_scope.

(** Before defining [Functor], we first define a record of 4-field
    things; this is so that if the fields of two functor types [A → B]
    and [C → D] unify, then they are considered the same type.  This
    way, if we ever get a judgmentally singleton type, we can have [1
    → Cᵒᵖ] and [(1 → C)ᵒᵖ] be judgmentally equal. *)

Record PreFunctorRecord
       (objC objD : Type)
       (morphism_ofT : (objC -> objD) -> Type)
       (composition_ofT : forall object_of, morphism_ofT object_of -> Type)
       (identity_ofT : forall object_of, morphism_ofT object_of -> Type)
  := {
      object_of :> objC -> objD;
      morphism_of : morphism_ofT object_of;
      composition_of' : composition_ofT _ morphism_of;
      identity_of' : identity_ofT _ morphism_of
    }.

Bind Scope functor_scope with PreFunctorRecord.

Section Functor.
  Variables C D : PreCategory.

  (** Quoting from the lecture notes for MIT's 18.705, Commutative Algebra:

      A map of categories is known as a functor. Namely, given
      categories [C] and [C'], a (covariant) functor [F : C -> C'] is
      a rule that assigns to each object [A] of [C] an object [F A] of
      [C'] and to each map [m : A -> B] of [C] a map [F m : F A -> F
      B] of [C'] preserving composition and identity; that is,

     (1) [F (m' ∘ m) = (F m') ∘ (F m)] for maps [m : A -> B] and [m' :
         B -> C] of [C], and

     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A]
         is the identity morphism of [A]. **)

  Definition Functor
    := @PreFunctorRecord
         C D
         (fun object_of
          => forall s d, morphism C s d
                      -> morphism D (object_of s) (object_of d))
         (fun object_of morphism_of
          => forall s d d'
                    (m1 : morphism C s d) (m2: morphism C d d'),
              morphism_of _ _ (m2 o m1)
              = (morphism_of _ _ m2) o (morphism_of _ _ m1))
         (fun object_of morphism_of
          => forall x, morphism_of _ _ (identity x)
                       = identity (object_of x)).
  Bind Scope functor_scope with Functor.

  Definition Build_Functor
    : forall (object_of : C -> D)
             (morphism_of : forall s d, morphism C s d
                                        -> morphism D (object_of s) (object_of d))
             (composition_of : forall s d d'
                                      (m1 : morphism C s d) (m2: morphism C d d'),
                 morphism_of _ _ (m2 o m1)
                 = (morphism_of _ _ m2) o (morphism_of _ _ m1))
             (identity_of : forall x, morphism_of _ _ (identity x)
                                      = identity (object_of x)),
      Functor
    := @Build_PreFunctorRecord _ _ _ _ _.

  Definition composition_of (F : Functor)
    : forall s d d' (m1 : morphism C s d) (m2: morphism C d d'),
      morphism_of F _ _ (m2 o m1)
      = (morphism_of F _ _ m2) o (morphism_of F _ _ m1)
    := composition_of' F.
  Definition identity_of (F : Functor)
    : forall x, morphism_of F _ _ (identity x) = identity (object_of F x)
    := identity_of' F.
End Functor.

Bind Scope functor_scope with Functor.

Create HintDb functor discriminated.

Arguments Functor C D.
Arguments object_of {_ _ _ _ _} F%functor c%object : rename, simpl nomatch.
Arguments morphism_of {_ _ _ _ _} F%functor : rename, simpl nomatch.
Arguments composition_of' {_ _ _ _ _} F%functor : rename, simpl nomatch.
Arguments identity_of' {_ _ _ _ _} F%functor : rename, simpl nomatch.
Arguments composition_of [C D]%category F%functor (s d d')%object (m1 m2)%morphism : rename, simpl nomatch.
Arguments identity_of [C D]%category F%functor x%object : rename, simpl nomatch.

Module Export FunctorCoreNotations.
  (** Perhaps we should consider making this more global? *)
  Local Notation "C --> D" := (Functor C D) (at level 99, right associativity) : type_scope.
  Notation "F '_0' x" := (object_of F%functor x%object) (at level 10, no associativity, only parsing) : object_scope.
  Notation "F '_1' m" := (morphism_of F%functor _ _ m%morphism) (at level 10, no associativity) : morphism_scope.
  Notation "@ 'object_of' C D" := (fun (F_workaround_bug_5292 : Functor C D) x_workaround_bug_5292 => (F_workaround_bug_5292 _0 x_workaround_bug_5292)%object)
                                    (at level 10, C at level 8, D at level 8, only parsing).
  Notation "@ 'morphism_of' C D" := (fun (F_workaround_bug_5292 : Functor C D) s_workaround_bug_5292 d_workaround_bug_5292
                                         (m_workaround_bug_5292 : morphism C s_workaround_bug_5292 d_workaround_bug_5292)
                                     => (F_workaround_bug_5292 _1 m_workaround_bug_5292)%morphism)
                                      (at level 10, C at level 8, D at level 8, only parsing).
End FunctorCoreNotations.

Hint Resolve @composition_of @identity_of : category functor.
Hint Rewrite @identity_of : category.
Hint Rewrite @identity_of : functor.
