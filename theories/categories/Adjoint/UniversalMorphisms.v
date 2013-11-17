Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity Functor.Composition.Core.
Require Import Functor.Dual NaturalTransformation.Dual Category.Dual.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.UnitCounitCoercions Adjoint.Dual.
Require Import Comma.Core UniversalProperties Comma.Dual InitialTerminalCategory.
Require Import HProp types.Sigma HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section adjunction_universal.
  Section initial.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F -| G.
    Variable Y : C.

    Definition initial_morphism__of__adjunction
    : object (Y / G)
      := @CommaCategory.Build_object
           _ D C
           (! Y) G
           (center _)
           (F Y)
           ((unit A) Y).

    Definition is_initial_morphism__of__adjunction
    : IsInitialMorphism initial_morphism__of__adjunction
      := Build_IsInitialMorphism
           _
           _
           _
           _
           ((A : AdjunctionUnit _ _).2 _).
  End initial.

  Global Arguments initial_morphism__of__adjunction [C D F G] A Y.
  Global Arguments is_initial_morphism__of__adjunction [C D F G] A Y _.

  Section terminal.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F -| G.
    Variable X : D.

    Definition terminal_morphism__of__adjunction
    : object (F / X)
      := Eval simpl in
          dual_functor_inv
            F (! X)
            (initial_morphism__of__adjunction A^op X).

    Definition is_terminal_morphism__of__adjunction
    : IsTerminalMorphism terminal_morphism__of__adjunction
      := is_initial_morphism__of__adjunction A^op X.
  End terminal.

  Global Arguments terminal_morphism__of__adjunction [C D F G] A X.
  Global Arguments is_terminal_morphism__of__adjunction [C D F G] A X _.
End adjunction_universal.

Section adjunction_from_universal.
  Section initial.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable G : Functor D C.
    Context `(HM : forall Y, @IsInitialMorphism _ _ Y G (M Y)).

    Local Notation obj_of Y :=
      (IsInitialMorphism_object (@HM Y))
        (only parsing).

    Local Notation mor_of Y0 Y1 f :=
      (let etaY1 := IsInitialMorphism_morphism (@HM Y1) in
       (@center _ (IsInitialMorphism_property (@HM Y0) _ (etaY1 o f))).1)
        (only parsing).

    Lemma identity_of Y : mor_of Y Y 1 = 1.
    Proof.
      simpl.
      match goal with
        | [ |- ((@center ?A ?H).2).1 = _ ]
          => erewrite (@contr A H (center _; (_; _)))
      end.
      simpl; reflexivity.
      Grab Existential Variables.
      simpl.
      rewrite ?identity_of, ?left_identity, ?right_identity.
      reflexivity.
    Qed.

    Local Arguments IsInitialMorphism_object / .
    Local Arguments IsInitialMorphism_morphism / .

    Lemma composition_of x y z g f
    : mor_of _ _ (f o g) = mor_of y z f o mor_of x y g.
    Proof.
      simpl.
      match goal with
        | [ |- ((@center ?A ?H).2).1 = _ ]
          => erewrite (@contr A H (center _; (_; _)))
      end. (* 7 s *)
      simpl; reflexivity.
      Grab Existential Variables.
      simpl in *.
      repeat match goal with
               | [ |- appcontext[?x.2.1] ]
                 => generalize (x.2); intro
             end.
      rewrite ?composition_of.
      repeat
        try_associativity_quick
        (idtac;
         match goal with
           | [ |- appcontext[?x.1] ]
             => simpl rewrite x.2
         end).
      rewrite ?left_identity, ?right_identity, ?associativity.
      reflexivity.
    Qed.

    Definition functor__of__initial_morphism : Functor C D
      := Build_Functor
           C D
           (fun x => obj_of x)
           (fun s d m => mor_of s d m)
           composition_of
           identity_of.

    Definition adjunction__of__initial_morphism
    : functor__of__initial_morphism -| G.
    Proof.
      refine (_ : AdjunctionUnit functor__of__initial_morphism G).
      eexists (Build_NaturalTransformation
                1
                (G o functor__of__initial_morphism)
                (fun x => IsInitialMorphism_morphism (@HM x))
                (fun s d m =>
                   symmetry
                     _ _
                     (@center _ (IsInitialMorphism_property (@HM s) _ _)).2)).
      simpl.
      exact (fun c => @IsInitialMorphism_property _ _ c G (M c) (@HM c)).
    Defined.
  End initial.

  Section terminal.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable F : Functor C D.
    Context `(HM : forall X, @IsTerminalMorphism _ _ F X (M X)).

    Definition functor__of__terminal_morphism : Functor D C
      := (@functor__of__initial_morphism
            (D^op) (C^op)
            (F^op)
            (fun x : D => dual_functor F !x (M x)) HM)^op'.

    Definition adjunction__of__terminal_morphism
    : F -| functor__of__terminal_morphism
      := ((@adjunction__of__initial_morphism
             (D^op) (C^op)
             (F^op)
             (fun x : D => dual_functor F !x (M x)) HM)^op'R)%adjunction.
  End terminal.
End adjunction_from_universal.
