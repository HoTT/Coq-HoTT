(** * Limits and Colimits *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import ExponentialLaws.Law1.Functors FunctorCategory.Core.
Require Import UniversalProperties KanExtensions.Core InitialTerminalCategory.Core NatCategory.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Comma.Core.
Require Import Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope functor_scope.
Local Open Scope category_scope.

(** ** The diagonal or "constant diagram" functor Δ *)
Section diagonal_functor.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.

  (**
     Quoting Dwyer and Spalinski:

     There is a diagonal or ``constant diagram'' functor

<<
     Δ : C → Cᴰ,
>>

     which carries an object [X : C] to the constant functor [Δ X : D
     -> C] (by definition, this ``constant functor'' sends each object
     of [D] to [X] and each morphism of [D] to [Identity X]). The
     functor Δ assigns to each morphism [f : X -> X'] of [C] the
     constant natural transformation [t(f) : Δ X -> Δ X'] determined
     by the formula [t(f) d = f] for each object [d] of [D].  **)

  (** We use [C¹] rather than [C] for judgemental compatibility with
      Kan extensions. *)

  Definition diagonal_functor : Functor (1 -> C) (D -> C)
    := @pullback_along _ D 1 C (Functors.to_terminal _).

  Definition diagonal_functor' : Functor C (D -> C)
    := diagonal_functor o ExponentialLaws.Law1.Functors.inverse _.

  Section convert.
    Lemma diagonal_functor_diagonal_functor' X
    : diagonal_functor X = diagonal_functor' (X (center _)).
    Proof.
      path_functor.
      simpl.
      repeat (apply path_forall || intro).
      apply identity_of.
    Qed.
  End convert.
End diagonal_functor.

Arguments diagonal_functor : simpl never.

Section diagonal_functor_lemmas.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.

  Lemma compose_diagonal_functor x (F : Functor D' D)
  : diagonal_functor C D x o F = diagonal_functor _ _ x.
  Proof.
    path_functor.
  Qed.

  Definition compose_diagonal_functor_natural_transformation
             x (F : Functor D' D)
  : NaturalTransformation (diagonal_functor C D x o F) (diagonal_functor _ _ x)
    := Build_NaturalTransformation
         (diagonal_functor C D x o F)
         (diagonal_functor _ _ x)
         (fun z => identity _)
         (fun _ _ _ => transitivity
                         _ _ _
                         (left_identity _ _ _ _)
                         (symmetry
                            _ _
                            (right_identity _ _ _ _))).
End diagonal_functor_lemmas.

Hint Rewrite @compose_diagonal_functor : category.

Section Limit.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor D C.

  (** ** Definition of Limit *)
  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A limit
     for [F] is an object [L] of [C] together with a natural
     transformation [t : Δ L -> F] such that for every object [X] of
     [C] and every natural transformation [s : Δ X -> F], there exists
     a unique map [s' : X -> L] in [C] such that [t (Δ s') = s].  **)

  Definition IsLimit
    := @IsRightKanExtensionAlong _ D 1 C (Functors.to_terminal _) F.
  (*Definition IsLimit' := @IsTerminalMorphism (_ -> _) (_ -> _) (diagonal_functor C D) F.*)
  (*  Definition Limit (L : C) :=
    { t : SmallNaturalTransformation ((diagonal_functor C D) L) F &
      forall X : C, forall s : SmallNaturalTransformation ((diagonal_functor C D) X) F,
        { s' : C.(Morphism) X L |
          unique
          (fun s' => SNTComposeT t ((diagonal_functor C D).(MorphismOf) s') = s)
          s'
        }
    }.*)

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A colimit
     for [F] is an object [c] of [C] together with a natural
     transformation [t : F -> Δ c] such that for every object [X] of
     [C] and every natural transformation [s : F -> Δ X], there exists
     a unique map [s' : c -> X] in [C] such that [(Δ s') t = s].  **)

  (** ** Definition of Colimit *)
  Definition IsColimit
    := @IsLeftKanExtensionAlong _ D 1 C (Functors.to_terminal _) F.
  (*Definition IsColimit' := @IsInitialMorphism (_ -> _) (_ -> _) F (diagonal_functor C D).*)
  (*  Definition Colimit (c : C) :=
    { t : SmallNaturalTransformation F ((diagonal_functor C D) c) &
      forall X : C, forall s : SmallNaturalTransformation F ((diagonal_functor C D) X),
        { s' : C.(Morphism) c X | is_unique s' /\
          SNTComposeT ((diagonal_functor C D).(MorphismOf) s') t = s
        }
    }.*)
  (** TODO(JasonGross): Figure out how to get good introduction and elimination rules working, which don't mention spurious identities. *)
  (*Section AbstractionBarrier.
    Section Limit.
      Set Printing  Implicit.
      Section IntroductionAbstractionBarrier.
        Local Open Scope morphism_scope.

        Definition Build_IsLimit
                 (lim_obj : C)
                 (lim_mor : morphism (D -> C)
                                     (diagonal_functor' C D lim_obj)
                                     F)
                 (lim := CommaCategory.Build_object
                           (diagonal_functor C D)
                           !(F : object (_ -> _))
                           !lim_obj
                           (center _)
                           lim_mor)
                 (UniversalProperty
                  : forall (lim_obj' : C)
                           (lim_mor' : morphism (D -> C)
                                                (diagonal_functor' C D lim_obj')
                                                F),
                      Contr { m : morphism C lim_obj' lim_obj
                            | lim_mor o morphism_of (diagonal_functor' C D) m = lim_mor' })
        : IsTerminalMorphism lim.
        Proof.
          apply Build_IsTerminalMorphism.
          intros A' p'.
          specialize (UniversalProperty (A' (center _))).*)
End Limit.

(** TODO(JasonGross): Port MorphismsBetweenLimits from catdb *)
