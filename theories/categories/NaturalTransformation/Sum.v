(** * Coproduct of natural transformations *)
Require Import Category.Core Functor.Core Category.Sum Functor.Sum NaturalTransformation.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section sum.
  Definition sum
             C C' D F G F' G'
             (T : @NaturalTransformation C D F G)
             (T' : @NaturalTransformation C' D F' G')
  : NaturalTransformation (F + F') (G + G').
  Proof.
    refine (Build_NaturalTransformation
              (F + F') (G + G')
              (fun x => match x with
                          | Datatypes.inl c => T c
                          | Datatypes.inr c' => T' c'
                        end)
              _).
    abstract (
        repeat (intros [] || intro); simpl;
        auto with natural_transformation
      ).
  Defined.
End sum.

Module Export NaturalTransformationSumNotations.
  Notation "T + U" := (sum T U) : natural_transformation_scope.
End NaturalTransformationSumNotations.
