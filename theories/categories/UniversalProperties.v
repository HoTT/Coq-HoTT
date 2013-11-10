Require Import Category.Core Functor.Core.
Require Import Category.Dual Functor.Dual.
Require Import Category.Objects Category.Morphisms.
Require Import InitialTerminalCategory.
Require Import Comma.Core.
Require Import types.Unit Trunc types.Sigma HProp HoTT.Tactics Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section UniversalMorphism.
  (** Quoting Wikipedia:

      Suppose that [U : D -> C] is a functor from a category [D] to a
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

  Section InitialMorphism.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable X : C.
    Variable U : Functor D C.
    (** An initial morphism from [X] to [U] is an initial object in
        the category [(X ↓ U)] of morphisms from [X] to [U].  In other
        words, it consists of a pair [(A, φ)] where [A] is an object
        of [D] and [φ: X -> U A] is a morphism in [C], such that the
        following initial property is satisfied:

       - Whenever [Y] is an object of [D] and [f : X -> U Y] is a
         morphism in [C], then there exists a unique morphism [g : A
         -> Y] such that the following diagram commutes:

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

    Definition IsInitialMorphism (Ap : object (X |v| U)) :=
      IsInitialObject (X |v| U) Ap.

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
    End IntroductionAbstractionBarrier.

    Section EliminationAbstractionBarrier.
      Variable Ap : object (X |v| U).

      Definition IsInitialMorphism_object (M : IsInitialMorphism Ap) : D
        := CommaCategory.b Ap.
      Definition IsInitialMorphism_morphism (M : IsInitialMorphism Ap)
      : morphism C X (U (IsInitialMorphism_object M))
        := CommaCategory.f Ap.
      Definition IsInitialMorphism_property (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : Contr { m : morphism D (IsInitialMorphism_object M) Y
              | morphism_of U m o (IsInitialMorphism_morphism M) = f }.
      Proof.
        (** We could just [rewrite right_identity], but we want to preserve judgemental computation rules. *)
        pose proof (@trunc_equiv'
                      _
                      _
                      (symmetry _ _ (@CommaCategory.issig_morphism _ _ _ !X U _ _))
                      minus_two
                      (M (CommaCategory.Build_object
                            !X
                            U
                            tt
                            Y
                            f))) as H'.
        simpl in H'.
        apply contr_inhabited_hprop.
        - abstract (
              apply @trunc_succ in H';
              eapply @trunc_equiv'; [ | exact H' ];
              match goal with
                | [ |- appcontext[?m o 1] ]
                  => simpl rewrite (right_identity _ _ _ m)
                | [ |- appcontext[1 o ?m] ]
                  => simpl rewrite (left_identity _ _ _ m)
              end;
              simpl;
              unfold IsInitialMorphism_object, IsInitialMorphism_morphism;
              let A := match goal with |- Equiv ?A ?B => constr:(A) end in
              let B := match goal with |- Equiv ?A ?B => constr:(B) end in
              apply (equiv_adjointify
                       (fun x : A => x.2)
                       (fun x : B => (tt; x)));
              [ intro; reflexivity
              | intros [[]]; reflexivity ]
            ).
        - (exists (@center _ H').2.1).
          abstract (
              etransitivity;
              [ apply (@center _ H').2.2 | auto with morphism ]
            ).
      Defined.
    End EliminationAbstractionBarrier.
  End InitialMorphism.

  Section TerminalMorphism.
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
            (CommaCategory.b (Ap : object (U |v| X)))
            (CommaCategory.a (Ap : object (U |v| X)))
            (CommaCategory.f (Ap : object (U |v| X)))
          : object ((X : object C^op) |v| U^op)).

    Definition IsTerminalMorphism (Ap : object (U |v| X)) : Type
      := @IsInitialMorphism
           (C^op)
           _
           X
           (U^op)
           (op_object Ap).

    Section IntroductionAbstractionBarrier.
      Definition Build_IsTerminalMorphism
                 (*(Ap : Object (U ↓ X))*)
                 (A : D)(* := CommaCategory.a Ap*)
                 (p : morphism C (U A) X)(*:= CommaCategory.f Ap*)
                 (Ap := CommaCategory.Build_object U !X A tt p)
                 (UniversalProperty
                  : forall (A' : D) (p' : morphism C (U A') X),
                      Contr { m : morphism D A' A
                            | p o morphism_of U m  = p' })
      : IsTerminalMorphism Ap
        := @Build_IsInitialMorphism
             (C^op)
             (D^op)
             X
             (U^op)
             A
             p
             UniversalProperty.
    End IntroductionAbstractionBarrier.

    Section AbstractionBarrier.
      Variable Ap : object (U |v| X).
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
    End AbstractionBarrier.
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
