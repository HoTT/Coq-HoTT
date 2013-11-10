Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Comma.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Section opposite.
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Local Ltac t :=
    simpl; intros; repeat apply ap;
    exact (center _).

  Section op.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Local Notation obj_of x
      := (CommaCategory.Build_object (T^op) (S^op) _ _ (CommaCategory.f x)).
    Local Notation obj_of_inv x
      := (CommaCategory.Build_object S T _ _ (CommaCategory.f x)).

    Definition dual_functor : Functor (S |v| T) ((T^op |v| S^op)^op).
    Proof.
      refine (Build_Functor (S |v| T) ((T^op |v| S^op)^op)
                            (fun x => obj_of x)
                            (fun s d m =>
                               CommaCategory.Build_morphism
                                 (obj_of d) (obj_of s)
                                 (CommaCategory.h m)
                                 (CommaCategory.g m)
                                 (symmetry _ _ (CommaCategory.p m)))
                            _
                            _);
      abstract t.
    Defined.

    Definition dual_functor_inv : Functor ((T^op |v| S^op)^op) (S |v| T).
    Proof.
      refine (Build_Functor ((T^op |v| S^op)^op) (S |v| T)
                            (fun x => obj_of_inv x)
                            (fun s d m => CommaCategory.Build_morphism
                                            (obj_of_inv s) (obj_of_inv d)
                                            (CommaCategory.h m)
                                            (CommaCategory.g m)
                                            (symmetry _ _ (CommaCategory.p m)))
                            _
                            _);
      abstract t.
    Defined.

    (** It would be nice to prove that these functors are inverses.  It would be almost trivial if we had eta for records.  Without it, I fear it will be rather tedius. *)
  End op.

  Section op'.
    Variable S : Functor A^op C^op.
    Variable T : Functor B^op C^op.

    Local Notation obj_of x
      := (CommaCategory.Build_object (T^op') (S^op') _ _ (CommaCategory.f x)).
    Local Notation obj_of_inv x
      := (CommaCategory.Build_object S T _ _ (CommaCategory.f x)).

    Definition dual_functor' : Functor (S |v| T) ((T^op' |v| S^op')^op).
    Proof.
      refine (Build_Functor (S |v| T) ((T^op' |v| S^op')^op)
                            (fun x => obj_of x)
                            (fun s d m => CommaCategory.Build_morphism
                                            (obj_of d) (obj_of s)
                                            (CommaCategory.h m)
                                            (CommaCategory.g m)
                                            (symmetry _ _ (CommaCategory.p m)))
                            _
                            _);
      abstract t.
    Defined.

    Definition dual_functor_inv' : Functor ((T^op' |v| S^op')^op) (S |v| T).
    Proof.
      refine (Build_Functor ((T^op' |v| S^op')^op) (S |v| T)
                            (fun x => obj_of_inv x)
                            (fun s d m => CommaCategory.Build_morphism
                                            (obj_of_inv s) (obj_of_inv d)
                                            (CommaCategory.h m)
                                            (CommaCategory.g m)
                                            (symmetry _ _ (CommaCategory.p m)))
                            _
                            _);
      abstract t.
    Defined.
  End op'.
End opposite.
