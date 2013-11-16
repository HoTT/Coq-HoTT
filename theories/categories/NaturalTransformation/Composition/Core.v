Require Import Category.Core Functor.Core Functor.Composition.Core NaturalTransformation.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section composition.
  (**
     We have the diagram
<<
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''
>>

     And we want the commutative diagram
<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B
>>
  *)

  Section compose.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variables F F' F'' : Functor C D.

    Variable T' : NaturalTransformation F' F''.
    Variable T : NaturalTransformation F F'.

    Local Notation CO c := (T' c o T c).

    Local Ltac t_fin :=
      match goal with
        | _ => apply associativity
        | _ => symmetry; apply associativity
      end.

    Local Ltac t :=
      match goal with
        | _ => t_fin
        | [ T : _, m : _ |- _ ] => case (commutes T _ _ m); t_fin
        | [ T : _, m : _ |- _ ] => case (symmetry _ _ (commutes T _ _ m));
                                  t_fin
      end.

    Definition compose_commutes s d (m : morphism C s d)
    : CO d o morphism_of F m = morphism_of F'' m o CO s.
    Proof.
      transitivity (T' _ o (morphism_of F' m o T _)).
      - t.
      - transitivity ((T' _ o morphism_of F' m) o T _);
        t.
    Defined.

    Global Arguments compose_commutes / .
    Global Opaque compose_commutes.

    Definition compose
    : NaturalTransformation F F''
      := Build_NaturalTransformation F F''
                                     (fun c => CO c)
                                     compose_commutes.
  End compose.

  Local Ltac whisker_t :=
    simpl;
    repeat first [ apply commutes
                 | apply ap
                 | progress (etransitivity; try apply composition_of); []
                 | progress (etransitivity; try (symmetry; apply composition_of)); [] ].

  Section whisker.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.

    Section L.
      Variable F : Functor D E.
      Variables G G' : Functor C D.
      Variable T : NaturalTransformation G G'.

      Local Notation CO c := (morphism_of F (T c)).

      Definition whisker_l_commutes s d (m : morphism C s d)
      : F _1 (T d) o (F o G) _1 m = (F o G') _1 m o F _1 (T s).
      Proof.
        whisker_t.
      Defined.

      Global Arguments whisker_l_commutes / .
      Global Opaque whisker_l_commutes.

      Definition whisker_l
        := Build_NaturalTransformation
             (F o G) (F o G')
             (fun c => CO c)
             whisker_l_commutes.
    End L.

    Section R.
      Variables F F' : Functor D E.
      Variable T : NaturalTransformation F F'.
      Variable G : Functor C D.

      Local Notation CO c := (T (G c)).

      Definition whisker_r_commutes s d (m : morphism C s d)
      : T (G d) o (F o G) _1 m = (F' o G) _1 m o T (G s).
      Proof.
        whisker_t.
      Defined.

      Global Arguments whisker_r_commutes / .
      Global Opaque whisker_r_commutes.

      Definition whisker_r
        := Build_NaturalTransformation
             (F o G) (F' o G)
             (fun c => CO c)
             whisker_r_commutes.
    End R.
  End whisker.
End composition.

Module Export NaturalTransformationCompositionCoreNotations.
  Infix "o" := compose : natural_transformation_scope.
  Infix "oL" := whisker_l (at level 40, left associativity) : natural_transformation_scope.
  Infix "oR" := whisker_r (at level 40, left associativity) : natural_transformation_scope.
End NaturalTransformationCompositionCoreNotations.
