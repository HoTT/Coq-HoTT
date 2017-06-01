(** * Opposite comma categories *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Functor.Composition.Core Functor.Identity Functor.Paths.
Require Comma.Core.
Local Set Warnings Append "-notation-overridden". (* work around bug #5567, https://coq.inria.fr/bugs/show_bug.cgi?id=5567, notation-overridden,parsing should not trigger for only printing notations *)
Import Comma.Core.
Local Set Warnings Append "notation-overridden".

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
    Variables A B C : PreCategory.

    Variable S : Functor A C.
    Variable T : Functor B C.

    Local Notation obj_of x
      := (CommaCategory.Build_object (T^op) (S^op) _ _ (CommaCategory.f x)
          : object ((T^op / S^op)^op)).

    Local Notation mor_of s d m
      := (CommaCategory.Build_morphism'
            (obj_of d) (obj_of s)
            (CommaCategory.h m%morphism)
            (CommaCategory.g m%morphism)
            (CommaCategory.p_sym m%morphism)
            (CommaCategory.p m%morphism)
          : morphism ((T^op / S^op)^op) (obj_of s) (obj_of d)).

    Definition dual_functor : Functor (S / T) ((T^op / S^op)^op)
      := Build_Functor
           (S / T) ((T^op / S^op)^op)
           (fun x => obj_of x)
           (fun s d m => mor_of s d m)
           (fun _ _ _ _ _ => 1%path)
           (fun _ => 1%path).
  End op.

  Definition dual_functor_involutive A B C (S : Functor A C) (T : Functor B C)
  : dual_functor S T o (dual_functor T^op S^op)^op = 1
    /\ (dual_functor T^op S^op)^op o dual_functor S T = 1
    := (idpath, idpath)%core.
End opposite.
