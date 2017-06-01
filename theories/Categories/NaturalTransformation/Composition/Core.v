(** * Composition of natural transformations *)
Require Import Category.Core Functor.Core Functor.Composition.Core NaturalTransformation.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

(** ** Vertical composition *)
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
    Variables C D : PreCategory.
    Variables F F' F'' : Functor C D.

    Variable T' : NaturalTransformation F' F''.
    Variable T : NaturalTransformation F F'.

    Local Notation CO c := (T' c o T c).

    Definition compose_commutes s d (m : morphism C s d)
    : CO d o F _1 m = F'' _1 m o CO s
      := (associativity _ _ _ _ _ _ _ _)
           @ ap (fun x => _ o x) (commutes T _ _ m)
           @ (associativity_sym _ _ _ _ _ _ _ _)
           @ ap (fun x => x o _) (commutes T' _ _ m)
           @ (associativity _ _ _ _ _ _ _ _).

    (** We define the symmetrized version separately so that we can get more unification in the functor [(C → D)ᵒᵖ → (Cᵒᵖ → Dᵒᵖ)] *)
    Definition compose_commutes_sym s d (m : morphism C s d)
    : F'' _1 m o CO s = CO d o F _1 m
      := (associativity_sym _ _ _ _ _ _ _ _)
           @ ap (fun x => x o _) (commutes_sym T' _ _ m)
           @ (associativity _ _ _ _ _ _ _ _)
           @ ap (fun x => _ o x) (commutes_sym T _ _ m)
           @ (associativity_sym _ _ _ _ _ _ _ _).

    Global Arguments compose_commutes : simpl never.
    Global Arguments compose_commutes_sym : simpl never.

    Definition compose
    : NaturalTransformation F F''
      := Build_NaturalTransformation' F F''
                                      (fun c => CO c)
                                      compose_commutes
                                      compose_commutes_sym.
  End compose.

  (** ** Whiskering *)
  Section whisker.
    Variables C D E : PreCategory.

    Section L.
      Variable F : Functor D E.
      Variables G G' : Functor C D.
      Variable T : NaturalTransformation G G'.

      Local Notation CO c := (F _1 (T c)).

      Definition whisker_l_commutes s d (m : morphism C s d)
      : F _1 (T d) o (F o G) _1 m = (F o G') _1 m o F _1 (T s)
        := ((composition_of F _ _ _ _ _)^)
             @ (ap (fun m => F _1 m) (commutes T _ _ _))
             @ (composition_of F _ _ _ _ _).

      Definition whisker_l_commutes_sym s d (m : morphism C s d)
      : (F o G') _1 m o F _1 (T s) = F _1 (T d) o (F o G) _1 m
        := ((composition_of F _ _ _ _ _)^)
             @ (ap (fun m => F _1 m) (commutes_sym T _ _ _))
             @ (composition_of F _ _ _ _ _).

      Global Arguments whisker_l_commutes : simpl never.
      Global Arguments whisker_l_commutes_sym : simpl never.

      Definition whisker_l
        := Build_NaturalTransformation'
             (F o G) (F o G')
             (fun c => CO c)
             whisker_l_commutes
             whisker_l_commutes_sym.
    End L.

    Section R.
      Variables F F' : Functor D E.
      Variable T : NaturalTransformation F F'.
      Variable G : Functor C D.

      Local Notation CO c := (T (G c)).

      Definition whisker_r_commutes s d (m : morphism C s d)
      : T (G d) o (F o G) _1 m = (F' o G) _1 m o T (G s)
        := commutes T _ _ _.

      Definition whisker_r_commutes_sym s d (m : morphism C s d)
      : (F' o G) _1 m o T (G s) = T (G d) o (F o G) _1 m
        := commutes_sym T _ _ _.

      Global Arguments whisker_r_commutes : simpl never.
      Global Arguments whisker_r_commutes_sym : simpl never.

      Definition whisker_r
        := Build_NaturalTransformation'
             (F o G) (F' o G)
             (fun c => CO c)
             whisker_r_commutes
             whisker_r_commutes_sym.
    End R.
  End whisker.
End composition.

Module Export NaturalTransformationCompositionCoreNotations.
  Infix "o" := compose : natural_transformation_scope.
  Infix "oL" := whisker_l : natural_transformation_scope.
  Infix "oR" := whisker_r : natural_transformation_scope.
End NaturalTransformationCompositionCoreNotations.
