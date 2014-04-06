(** * Opposite comma categories *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
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
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Section op.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Local Notation obj_of x
      := (CommaCategory.Build_object (T^op) (S^op) _ _ (CommaCategory.f x)
          : object ((T^op / S^op)^op)).
    Local Notation obj_of_inv x
      := (CommaCategory.Build_object S T _ _ (CommaCategory.f x)
          : object (S / T)).

    Local Notation mor_of s d m
      := (CommaCategory.Build_morphism
            (obj_of d) (obj_of s)
            (CommaCategory.h m)
            (CommaCategory.g m)
            ((CommaCategory.p m)^)
          : morphism ((T^op / S^op)^op) (obj_of s) (obj_of d)).
    Local Notation mor_of_inv s d m
      := (CommaCategory.Build_morphism
            (obj_of_inv s) (obj_of_inv d)
            (CommaCategory.h m)
            (CommaCategory.g m)
            ((CommaCategory.p m)^)
          : morphism (S / T) (obj_of_inv s) (obj_of_inv d)).

    Definition dual_functor : Functor (S / T) ((T^op / S^op)^op)
      := Build_Functor
           (S / T) ((T^op / S^op)^op)
           (fun x => obj_of x)
           (fun s d m => mor_of s d m)
           (fun s d d' m1 m2 =>
              CommaCategory.path_morphism
                (mor_of s d' (m2 o m1))
                (mor_of d d' m2 o mor_of s d m1)
                idpath
                idpath)
           (fun x =>
              CommaCategory.path_morphism
                (mor_of x x (Category.Core.identity x))
                (Category.Core.identity (obj_of x))
                idpath
                idpath).

    Definition dual_functor_inv : Functor ((T^op / S^op)^op) (S / T)
      := Build_Functor
           ((T^op / S^op)^op) (S / T)
           (fun x => obj_of_inv x)
           (fun s d m => mor_of_inv s d m)
           (fun s d d' m1 m2 =>
              CommaCategory.path_morphism
                (mor_of_inv s d' (m2 o m1))
                (mor_of_inv d d' m2 o mor_of_inv s d m1)
                idpath
                idpath)
           (fun x =>
              CommaCategory.path_morphism
                (mor_of_inv x x (Category.Core.identity x))
                (Category.Core.identity (obj_of_inv x))
                idpath
                idpath).

    (** It would be nice to prove that these functors are inverses.  It would be almost trivial if we had eta for records.  Without it, I fear it will be rather tedius. *)
  End op.

  Section op'.
    Variable S : Functor A^op C^op.
    Variable T : Functor B^op C^op.

    Local Notation obj_of x
      := (CommaCategory.Build_object (T^op') (S^op') _ _ (CommaCategory.f x)
          : object ((T^op' / S^op')^op)).
    Local Notation obj_of_inv x
      := (CommaCategory.Build_object S T _ _ (CommaCategory.f x)
          : object (S / T)).

    Local Notation mor_of s d m
      := (CommaCategory.Build_morphism
            (obj_of d) (obj_of s)
            (CommaCategory.h m)
            (CommaCategory.g m)
            ((CommaCategory.p m)^)
          : morphism ((T^op' / S^op')^op) (obj_of s) (obj_of d)).
    Local Notation mor_of_inv s d m
      := (CommaCategory.Build_morphism
            (obj_of_inv s) (obj_of_inv d)
            (CommaCategory.h m)
            (CommaCategory.g m)
            ((CommaCategory.p m)^)
          : morphism (S / T) (obj_of_inv s) (obj_of_inv d)).

    Definition dual_functor' : Functor (S / T) ((T^op' / S^op')^op)
      := Build_Functor
           (S / T) ((T^op' / S^op')^op)
           (fun x => obj_of x)
           (fun s d m => mor_of s d m)
           (fun s d d' m1 m2 =>
              CommaCategory.path_morphism
                (mor_of s d' (m2 o m1))
                (mor_of d d' m2 o mor_of s d m1)
                idpath
                idpath)
           (fun x =>
              CommaCategory.path_morphism
                (mor_of x x (Category.Core.identity x))
                (Category.Core.identity (obj_of x))
                idpath
                idpath).

    Definition dual_functor_inv' : Functor ((T^op' / S^op')^op) (S / T)
      := Build_Functor
           ((T^op' / S^op')^op) (S / T)
           (fun x => obj_of_inv x)
           (fun s d m => mor_of_inv s d m)
           (fun s d d' m1 m2 =>
              CommaCategory.path_morphism
                (mor_of_inv s d' (m2 o m1))
                (mor_of_inv d d' m2 o mor_of_inv s d m1)
                idpath
                idpath)
           (fun x =>
              CommaCategory.path_morphism
                (mor_of_inv x x (Category.Core.identity x))
                (Category.Core.identity (obj_of_inv x))
                idpath
                idpath).
  End op'.
End opposite.
