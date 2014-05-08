(** * Universal morphisms *)
Require Import Category.Core Functor.Core.
Require Import Category.Dual Functor.Dual.
Require Import Category.Objects Category.Morphisms.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import Comma.Core.
Require Import types.Unit Trunc types.Sigma HProp HoTT.Tactics Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section UniversalMorphism.
  (** Quoting Wikipedia:

      Suppose that [U : D → C] is a functor from a category [D] to a
      category [C], and let [X] be an object of [C].  Consider the
      following dual (opposite) notions: *)

  Local Ltac univ_hprop_t UniversalProperty :=
    apply @trunc_succ in UniversalProperty;
    eapply @trunc_sigma;
    first [ intro;
            simpl;
            match goal with
              | [ |- appcontext[?m o 1] ]
                => simpl rewrite (right_identity _ _ _ m)
              | [ |- appcontext[1 o ?m] ]
                => simpl rewrite (left_identity _ _ _ m)
            end;
            assumption
          | by typeclasses eauto ].

  (** ** Initial morphisms *)
  Section InitialMorphism.
    (** *** Definition *)
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable X : C.
    Variable U : Functor D C.
    (** An initial morphism from [X] to [U] is an initial object in
        the category [(X ↓ U)] of morphisms from [X] to [U].  In other
        words, it consists of a pair [(A, φ)] where [A] is an object
        of [D] and [φ: X → U A] is a morphism in [C], such that the
        following initial property is satisfied:

       - Whenever [Y] is an object of [D] and [f : X → U Y] is a
         morphism in [C], then there exists a unique morphism [g : A
         → Y] such that the following diagram commutes:

<<
             φ
         X -----> U A       A
          \        .        .
            \      . U g    . g
           f  \    .        .
               ↘   ↓        ↓
                 U Y        Y
>>
       *)

    Definition IsInitialMorphism (Ap : object (X / U)) :=
      IsInitialObject (X / U) Ap.

    (** *** Introduction rule *)
    Section IntroductionAbstractionBarrier.
      Definition Build_IsInitialMorphism
                 (*(Ap : Object (X ↓ U))*)
                 (A : D)(* := CCO_b Ap*)
                 (p : morphism C X (U A))(*:= CCO_f Ap*)
                 (Ap := CommaCategory.Build_object !X U tt A p)
                 (UniversalProperty
                  : forall (A' : D) (p' : morphism C X (U A')),
                      Contr { m : morphism D A A'
                            | morphism_of U m o p = p' })
      : IsInitialMorphism Ap.
      Proof.
        intro x.
        specialize (UniversalProperty (CommaCategory.b x) (CommaCategory.f x)).
        (** We want to preserve the computation rules for the morphisms, even though they're unique up to unique isomorphism. *)
        eapply trunc_equiv'.
        apply CommaCategory.issig_morphism.
        apply contr_inhabited_hprop.
        - abstract univ_hprop_t UniversalProperty.
        - (exists tt).
          (exists (@center _ UniversalProperty).1).
          abstract (progress rewrite ?right_identity, ?left_identity;
                    exact (@center _ UniversalProperty).2).
      Defined.

      Definition Build_IsInitialMorphism_curried
                 (A : D)
                 (p : morphism C X (U A))
                 (Ap := CommaCategory.Build_object !X U tt A p)
                 (m : forall (A' : D) (p' : morphism C X (U A')),
                        morphism D A A')
                 (H : forall (A' : D) (p' : morphism C X (U A')),
                        morphism_of U (m A' p') o p = p')
                 (H' : forall (A' : D) (p' : morphism C X (U A')) m',
                         morphism_of U m' o p = p'
                         -> m A' p' = m')
      : IsInitialMorphism Ap
        := Build_IsInitialMorphism
             A
             p
             (fun A' p' =>
                {| center := (m A' p'; H A' p');
                   contr m' := path_sigma
                                 _
                                 (m A' p'; H A' p')
                                 m'
                                 (H' A' p' m'.1 m'.2)
                                 (center _) |}).

      (** Projections from nested sigmas are currently rather slow.  We should just be able to do

<<
      Definition Build_IsInitialMorphism_uncurried
                 (univ
                  : { A : D
                    | { p : morphism C X (U A)
                       | let Ap := CommaCategory.Build_object !X U tt A p in
                         forall (A' : D) (p' : morphism C X (U A')),
                           { m : morphism D A A'
                           | { H : morphism_of U m o p = p'
                             | forall m',
                                 morphism_of U m' o p = p'
                                 -> m = m' }}}})
        := @Build_IsInitialMorphism_curried
             (univ.1)
             (univ.2.1)
             (fun A' p' => (univ.2.2 A' p').1)
             (fun A' p' => (univ.2.2 A' p').2.1)
             (fun A' p' => (univ.2.2 A' p').2.2).
>>

      But that's currently too slow.  (About 6-8 seconds, on my machine.)  So instead we factor out all of the type parts by hand, and then apply them after. *)

      Let make_uncurried A' B' C' D' E'0
          (E'1 : forall a a' b b' (c : C' a a'), D' a a' b b' c -> E'0 a a' -> Type)
          (E' : forall a a' b b' (c : C' a a'), D' a a' b b' c -> E'0 a a' -> Type)
          F'
          (f : forall (a : A')
                      (b : B' a)
                      (c : forall (a' : A') (b' : B' a'),
                             C' a a')
                      (d : forall (a' : A') (b' : B' a'),
                             D' a a' b b' (c a' b'))
                      (e : forall (a' : A') (b' : B' a')
                                  (e0 : E'0 a a')
                                  (e1 : E'1 a a' b b' (c a' b') (d a' b') e0),
                             E' a a' b b' (c a' b') (d a' b') e0),
                 F' a b)
          (univ
           : { a : A'
             | { b : B' a
               | forall (a' : A') (b' : B' a'),
                   { c : C' a a'
                   | { d : D' a a' b b' c
                     | forall (e0 : E'0 a a')
                              (e1 : E'1 a a' b b' c d e0),
                         E' a a' b b' c d e0 }}}})
      : F' univ.1 univ.2.1
        := f
             (univ.1)
             (univ.2.1)
             (fun A' p' => (univ.2.2 A' p').1)
             (fun A' p' => (univ.2.2 A' p').2.1)
             (fun A' p' => (univ.2.2 A' p').2.2).

      Definition Build_IsInitialMorphism_uncurried
      : forall (univ
                : { A : D
                  | { p : morphism C X (U A)
                    | let Ap := CommaCategory.Build_object !X U tt A p in
                      forall (A' : D) (p' : morphism C X (U A')),
                        { m : morphism D A A'
                        | { H : morphism_of U m o p = p'
                          | forall m',
                              morphism_of U m' o p = p'
                              -> m = m' }}}}),
          IsInitialMorphism (CommaCategory.Build_object !X U tt univ.1 univ.2.1)
        := @make_uncurried
             _ _ _ _ _ _ _ _
             (@Build_IsInitialMorphism_curried).
    End IntroductionAbstractionBarrier.

    Global Arguments Build_IsInitialMorphism : simpl never.
    Global Arguments Build_IsInitialMorphism_curried : simpl never.
    Global Arguments Build_IsInitialMorphism_uncurried : simpl never.

    (** *** Elimination rule *)
    Section EliminationAbstractionBarrier.
      Variable Ap : object (X / U).

      Definition IsInitialMorphism_object (M : IsInitialMorphism Ap) : D
        := CommaCategory.b Ap.
      Definition IsInitialMorphism_morphism (M : IsInitialMorphism Ap)
      : morphism C X (U (IsInitialMorphism_object M))
        := CommaCategory.f Ap.
      Definition IsInitialMorphism_property_morphism (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : morphism D (IsInitialMorphism_object M) Y
        := CommaCategory.h
             (@center _ (M (CommaCategory.Build_object !X U tt Y f))).
      Definition IsInitialMorphism_property_morphism_property
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : (morphism_of U (IsInitialMorphism_property_morphism M Y f))
          o IsInitialMorphism_morphism M = f
        := concat
             (CommaCategory.p
                (@center _ (M (CommaCategory.Build_object !X U tt Y f))))
             (right_identity _ _ _ _).
      Definition IsInitialMorphism_property_morphism_unique
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
                 m'
                 (H : morphism_of U m' o IsInitialMorphism_morphism M = f)
      : IsInitialMorphism_property_morphism M Y f = m'
        := ap
             (@CommaCategory.h _ _ _ _ _ _ _)
             (@contr _
                     (M (CommaCategory.Build_object !X U tt Y f))
                     (CommaCategory.Build_morphism
                        Ap (CommaCategory.Build_object !X U tt Y f)
                        tt m' (H @ (right_identity _ _ _ _)^)%path)).
      Definition IsInitialMorphism_property
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : Contr { m : morphism D (IsInitialMorphism_object M) Y
              | morphism_of U m o IsInitialMorphism_morphism M = f }
        := {| center := (IsInitialMorphism_property_morphism M Y f;
                         IsInitialMorphism_property_morphism_property M Y f);
              contr m' := path_sigma
                            _
                            (IsInitialMorphism_property_morphism M Y f;
                             IsInitialMorphism_property_morphism_property M Y f)
                            m'
                            (@IsInitialMorphism_property_morphism_unique M Y f m'.1 m'.2)
                            (center _) |}.
    End EliminationAbstractionBarrier.

    Global Arguments IsInitialMorphism_object : simpl never.
    Global Arguments IsInitialMorphism_morphism : simpl never.
    Global Arguments IsInitialMorphism_property : simpl never.
    Global Arguments IsInitialMorphism_property_morphism : simpl never.
    Global Arguments IsInitialMorphism_property_morphism_property : simpl never.
    Global Arguments IsInitialMorphism_property_morphism_unique : simpl never.
  End InitialMorphism.

  (** ** Terminal morphisms *)
  Section TerminalMorphism.
    (** *** Definition *)
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable U : Functor D C.
    Variable X : C.
    (** A terminal morphism from [U] to [X] is a terminal object in
       the comma category [(U ↓ X)] of morphisms from [U] to [X].  In
       other words, it consists of a pair [(A, φ)] where [A] is an
       object of [D] and [φ : U A -> X] is a morphism in [C], such
       that the following terminal property is satisfied:

       - Whenever [Y] is an object of [D] and [f : U Y -> X] is a
         morphism in [C], then there exists a unique morphism [g : Y
         -> A] such that the following diagram commutes:

<<
         Y      U Y
         .       . \
       g .   U g .   \  f
         .       .     \
         ↓       ↓       ↘
         A      U A -----> X
                      φ
>>
       *)
    Local Notation op_object Ap
      := (CommaCategory.Build_object
            (Functors.from_terminal C^op X) (U^op)
            (CommaCategory.b (Ap : object (U / X)))
            (CommaCategory.a (Ap : object (U / X)))
            (CommaCategory.f (Ap : object (U / X)))
          : object ((X : object C^op) / U^op)).

    Definition IsTerminalMorphism (Ap : object (U / X)) : Type
      := @IsInitialMorphism
           (C^op)
           _
           X
           (U^op)
           (op_object Ap).

    (** *** Introduction rule *)
    Section IntroductionAbstractionBarrier.
      Definition Build_IsTerminalMorphism
      : forall
          (*(Ap : Object (U ↓ X))*)
          (A : D)(* := CommaCategory.a Ap*)
          (p : morphism C (U A) X)(*:= CommaCategory.f Ap*)
          (Ap := CommaCategory.Build_object U !X A tt p)
          (UniversalProperty
           : forall (A' : D) (p' : morphism C (U A') X),
               Contr { m : morphism D A' A
                     | p o morphism_of U m = p' }),
          IsTerminalMorphism Ap
        := @Build_IsInitialMorphism
             (C^op)
             (D^op)
             X
             (U^op).

      Definition Build_IsTerminalMorphism_curried
      : forall
          (A : D)
          (p : morphism C (U A) X)
          (Ap := CommaCategory.Build_object U !X A tt p)
          (m : forall (A' : D) (p' : morphism C (U A') X),
                 morphism D A' A)
          (H : forall (A' : D) (p' : morphism C (U A') X),
                 p o morphism_of U (m A' p') = p')
          (H' : forall (A' : D) (p' : morphism C (U A') X) m',
                  p o morphism_of U m' = p'
                  -> m A' p' = m'),
          IsTerminalMorphism Ap
        := @Build_IsInitialMorphism_curried
             (C^op)
             (D^op)
             X
             (U^op).

      Definition Build_IsTerminalMorphism_uncurried
      : forall
          (univ : { A : D
                  | { p : morphism C (U A) X
                    | let Ap := CommaCategory.Build_object U !X A tt p in
                      forall (A' : D) (p' : morphism C (U A') X),
                        { m : morphism D A' A
                        | { H : p o morphism_of U m = p'
                          | forall m',
                              p o morphism_of U m' = p'
                              -> m = m' }}}}),
          IsTerminalMorphism (CommaCategory.Build_object U !X univ.1 tt univ.2.1)
        := @Build_IsInitialMorphism_uncurried
             (C^op)
             (D^op)
             X
             (U^op).
    End IntroductionAbstractionBarrier.

    (** *** Elimination rule *)
    Section EliminationAbstractionBarrier.
      Variable Ap : object (U / X).
      Variable M : IsTerminalMorphism Ap.

      Definition IsTerminalMorphism_object : D :=
        @IsInitialMorphism_object C^op D^op X U^op (op_object Ap) M.
      Definition IsTerminalMorphism_morphism
      : morphism C (U IsTerminalMorphism_object) X
        := @IsInitialMorphism_morphism C^op D^op X U^op (op_object Ap) M.
      Definition IsTerminalMorphism_property
      : forall (Y : D) (f : morphism C (U Y) X),
          Contr { m : morphism D Y IsTerminalMorphism_object
                | IsTerminalMorphism_morphism o morphism_of U m = f }
        := @IsInitialMorphism_property C^op D^op X U^op (op_object Ap) M.
      Definition IsTerminalMorphism_property_morphism
      : forall (Y : D) (f : morphism C (U Y) X),
          morphism D Y IsTerminalMorphism_object
        := @IsInitialMorphism_property_morphism
             C^op D^op X U^op (op_object Ap) M.
      Definition IsTerminalMorphism_property_morphism_property
      : forall (Y : D) (f : morphism C (U Y) X),
          IsTerminalMorphism_morphism
            o (morphism_of U (IsTerminalMorphism_property_morphism Y f))
          = f
        := @IsInitialMorphism_property_morphism_property
             C^op D^op X U^op (op_object Ap) M.
      Definition IsTerminalMorphism_property_morphism_unique
      : forall (Y : D) (f : morphism C (U Y) X)
               m'
               (H : IsTerminalMorphism_morphism o morphism_of U m' = f),
          IsTerminalMorphism_property_morphism Y f = m'
        := @IsInitialMorphism_property_morphism_unique
             C^op D^op X U^op (op_object Ap) M.
    End EliminationAbstractionBarrier.
  End TerminalMorphism.

  Section UniversalMorphism.
    (** The term universal morphism refers either to an initial
        morphism or a terminal morphism, and the term universal
        property refers either to an initial property or a terminal
        property.  In each definition, the existence of the morphism
        [g] intuitively expresses the fact that [(A, φ)] is ``general
        enough'', while the uniqueness of the morphism ensures that
        [(A, φ)] is ``not too general''.  *)
  End UniversalMorphism.
End UniversalMorphism.

Arguments Build_IsInitialMorphism [C D] X U A p UniversalProperty _.
Arguments Build_IsTerminalMorphism [C D] U X A p UniversalProperty _.
