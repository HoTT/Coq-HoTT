(** * Kan Extensions *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import ExponentialLaws.Law4.Functors FunctorCategory.Core.
Require Import Functor.Composition.Functorial.Core.
Require Import UniversalProperties.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

(** Quoting nCatLab on Kan Exensions:

    ** Idea

    The Kan extension of a functor [F : C → D] with respect to a
    functor

<<
    C
    |
    | p
    ↓
    C'
>>

    is, if it exists, a kind of best approximation to the problem of
    finding a functor [C' → D] such that

<<
        F
    C -----> D
    |       ↗
    | p   /
    |   /
    ↓ /
    C'
>>

    hence to extending the domain of [F] through [p] from [C] to [C'].

    More generally, this makes sense not only in Cat but in any
    2-category.

    Similarly, a Kan lift is the best approximation to lifting a
    morphism [F : C → D] through a morphism

<<
    D'
    |
    ↓
    D
>>

    to a morphism [F̂]

<<
                D'
              ↗ |
            /   |
        F̂ /     |
        /       |
      /   F     ↓
    C --------> D
>>

    Kan extensions are ubiquitous. See the discussion at Examples
    below.

    ** Definitions

    There are various slight variants of the definition of Kan
    extension. In good cases they all exist and all coincide, but in
    some cases only some of these will actually exist.

    We (have to) distinguish the following cases:

    - “ordinary” or “weak” Kan extensions

      These define the extension of an entire functor, by an
      adjointness relation.

      Here we (have to) distinguish further between

      - global Kan extensions,

        which define extensions of all possible functors of given
        domain and codomain (if all of them indeed exist);

      - local Kan extensions,

        which define extensions of single functors only, which may
        exist even if not every functor has an extension.

    - “pointwise” or “strong” Kan extensions

      These define the value of an extended functor on each object
      (each “point”) by a weighted (co)limit.

      Furthermore, a pointwise Kan extension can be “absolute”.

    If the pointwise version exists, then it coincides with the
    “ordinary” or “weak” version, but the former may exist without the
    pointwise version existing. See below for more.

    Some authors (such as Kelly) assert that only pointwise Kan
    extensions deserve the name “Kan extension,” and use the term as
    “weak Kan extension” for a functor equipped with a universal
    natural transformation. It is certainly true that most Kan
    extensions which arise in practice are pointwise. This distinction
    is even more important in enriched category theory. *)

Section kan_extensions.
  (** ** Ordinary or weak Kan extensions

      *** Global Kan extensions

      Let [p : C → C'] be a functor. For [D] any other category, write
      [p* : (C' → D) → (C → D)] for the induced functor on the functor
      categories: this sends a functor [h : C' → D] to the composite functor

<<
                p      h
      p* h : C --> C' --> D
>>
   *)


  (** *** Pullback-along functor *)
  Context `{Funext}.
  Variables C C' D : PreCategory.

  Section pullback_along.
    Definition pullback_along_functor
    : object ((C -> C') -> (C' -> D) -> (C -> D))
      := Functor.Composition.Functorial.Core.compose_functor _ _ _.

    Definition pullback_along (p : Functor C C')
    : object ((C' -> D) -> (C -> D))
      := Eval hnf in pullback_along_functor p.
  End pullback_along.

  (** Definition. If [p*] has a left adjoint, typically denoted [p_! :
      (C → D) → (C' → D)] or [Lan_p : (C → D) → (C' → D)] then this
      left adjoint is called the (ordinary or weak) left Kan extension
      operation along [p]. For [h ∈ (C -> D)] we call [p_! h] the left
      Kan extension of [h] along [p].

      Similarly, if [p*] has a right adjoint, this right adjoint is
      called the right Kan extension operation along [p]. It is
      typically denoted [p_* : (C → D) → (C' → D)] or [Ran = Ran_p :
      (C → D) → (C' → D)].

      The analogous definition clearly makes sense as stated in other
      contexts, such as in enriched category theory.

      Observation. If [C' = 1] is the terminal category, then

      - the left Kan extension operation forms the colimit of a functor;

      - the right Kan extension operation forms the limit of a functor. *)

  (** *** Left Kan extensions *)
  (** Colimits are initial morphisms. *)
  Definition IsLeftKanExtensionAlong (p : Functor C C') (h : Functor C D)
    := @IsInitialMorphism (_ -> _) _ h (pullback_along p).

  (** *** Right Kan extensions *)
  (** Limits are terminal morphisms *)
  Definition IsRightKanExtensionAlong (p : Functor C C') (h : Functor C D)
    := @IsTerminalMorphism _ (_ -> _) (pullback_along p) h.
End kan_extensions.
