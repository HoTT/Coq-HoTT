(** * Opposite comma categories *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
(*Require Import Functor.Composition.Core Functor.Identity Functor.Paths.*)
Require Import Comma.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.

(** ** The dual functors [(S / T) ↔ ((Tᵒᵖ / Sᵒᵖ)ᵒᵖ)] *)
Section opposite.
  Section op.
    Variable A : PreCategory.
    Variable B : PreCategory.
    Variable C : PreCategory.

    Variable S : Functor A C.
    Variable T : Functor B C.

    Local Notation obj_of x
      := (CommaCategory.Build_object (T^op) (S^op) _ _ (CommaCategory.f x)
          : object ((T^op / S^op)^op)).

    Local Notation mor_of s d m
      := (CommaCategory.Build_morphism
            (obj_of d) (obj_of s)
            (CommaCategory.h m%morphism)
            (CommaCategory.g m%morphism)
            ((CommaCategory.p m%morphism)^)
          : morphism ((T^op / S^op)^op) (obj_of s) (obj_of d)).

    Definition dual_functor : Functor (S / T) ((T^op / S^op)^op)
      := Build_Functor
           (S / T) ((T^op / S^op)^op)
           (fun x => obj_of x)
           (fun s d m => mor_of s d m)
           (fun s d d' m1 m2 =>
              CommaCategory.path_morphism
                (mor_of s d' (m2 o m1))
                (mor_of d d' m2 o mor_of s d m1)%morphism
                idpath
                idpath)
           (fun x =>
              CommaCategory.path_morphism
                (mor_of x x (Category.Core.identity x))
                (Category.Core.identity (obj_of x))
                idpath
                idpath).
  End op.

  (** Wait until [Comma.object] is a primitive record to prove this *)
  (**
<<
  Definition dual_functor_involutive `{Funext} A B C (S : Functor A C) (T : Functor B C)
  : dual_functor S T o (dual_functor T^op S^op)^op = 1
    /\ (dual_functor T^op S^op)^op o dual_functor S T = 1.
  Proof.
    split; path_functor.
>> *)
End opposite.
